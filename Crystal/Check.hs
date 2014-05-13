{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
{-#LANGUAGE TypeSynonymInstances, FlexibleInstances, OverloadedStrings #-}
module Crystal.Check where

import Control.Applicative
import Control.Lens hiding (transform, transformM, universe, (.=))
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Aeson hiding (encode)
import Data.List
import Data.Maybe
import Debug.Trace
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text.Lazy as T
import Data.Generics hiding (GT)
import Data.Generics.Biplate

import Crystal.AST
import Crystal.JSON
import Crystal.Config
import Crystal.Misc
import Crystal.Tuple
import Crystal.Type

data Check = Cnone
           | Cand [Check]
           | Cor [Check]
           | Check [TLabel] Type (Either LitVal Ident)
             deriving (Show, Eq, Data, Typeable)

type CheckedLabel = TLabel :*: Check :*: Effect

_check :: Simple Lens CheckedLabel Check
_check = _2._1

annCheck :: Simple Lens (Expr CheckedLabel) Check
annCheck = ann._check

annEffect :: Simple Lens (Expr CheckedLabel) Effect
annEffect = ann._2._2

addChecks :: Expr TypedLabel -> Step (Expr TLabel)
addChecks = reifyChecks <=< maybeAnnotateLabels <=< maybeDumpTree "check-simplification" <=< generateMobilityStats <=< eliminateRedundantChecks <=< maybeDumpTree "check-mobility" <=< moveChecksUp <=< introduceChecks

maybeDumpTree :: ToJSON a => String -> Expr a -> Step (Expr a)
maybeDumpTree tag expr =
  do dump <- asks (^.cfgDumpTree)
     when dump $ do
       report tag $ encode expr
     return expr

instance ToJSON TLabel where
  toJSON l = toJSON $ show l

instance ToJSON CheckedLabel where
  toJSON (l :*: c :*: ef) = object [ "label" .= show l, "check" .= show c, "effect" .= toJSON (S.toList ef) ]

introduceChecks :: Expr TypedLabel -> Step (Expr CheckedLabel)
introduceChecks expr = return $ go expr
  where go (Expr (l :*: t :*: ef) expr) =
          let simply ie = Expr (l :*: Cnone :*: ef) ie in
          case expr of
               Appl op args         -> Expr (l :*: checks :*: ef) (Appl op' args')
                 where labLookup l =
                         case [ litOrIdent e | (Expr (l' :*: _) e) <- op':args', l == l' ] of
                              []     -> Nothing
                              (x:xs) -> Just x
                       (op':args') = map go (op:args)
                       checks = simplifyC (typeToChecks labLookup t)
                       litOrIdent (Ref r) = Right r
                       litOrIdent (Lit l) = Left l
               Lit lit              -> simply (Lit lit)
               Ref r                -> simply (Ref r)
               If cond cons alt     -> simply (If (go cond) (go cons) (go alt))
               Let [(id, e)] bod    -> simply (Let [(id, go e)] (go bod))
               LetRec bnds bod      -> simply (LetRec (over (mapped._2) go bnds) (go bod))
               Lambda ids r bod     -> simply (Lambda ids r (go bod))
               Begin es             -> simply (Begin $ map go es)

typeToChecks :: (TLabel -> Maybe (Either LitVal Ident)) -> Type -> Check
typeToChecks look (TIf (blame, cause) prim var rest) =
  case look cause of
       Just v  -> Cand [Check [blame] prim v, typeToChecks look rest]
       Nothing -> typeToChecks look rest
typeToChecks look (Tor types) =
  Cor $ map (typeToChecks look) types
typeToChecks look _ = Cnone


simplifyC :: Check -> Check
simplifyC c@(Cand cs) =
  case cs' of
       [c] -> c
       [] -> Cnone
       _ -> Cand cs'
  where cs' = simplifyMerge c
        simplifyMerge (Cand cs) = nub $ filter (/= Cnone) $ concatMap simplifyMerge cs
        simplifyMerge c = [simplifyC c]
simplifyC (Cor cs) =
  case cs' of
       [c] -> c
       _ | Cnone `elem` cs' -> Cnone
       _ -> Cor cs' 
  where cs' = nub $ map simplifyC cs
simplifyC (Check labs typ target) = Check (nub labs) typ target
simplifyC Cnone = Cnone

insertC :: Check -> [Check] -> [Check]
insertC            c                []   = [c]
insertC cc@(Check l t (Right id)) (c:cs) =
  case cc of
       Check l' t' (Right id')
        | id == id' && t == t' -> Check (l++l') t' (Right id) : cs
       _                       -> c : insertC cc cs

moveChecksUp :: Expr CheckedLabel -> Step (Expr CheckedLabel)
moveChecksUp ast = do moveUp <- asks (^.cfgCheckMobility)
                      if moveUp
                         then return $ transformBi f ast
                         else return ast
  where f :: Expr CheckedLabel -> Expr CheckedLabel
        f simple@(Expr (l :*: checks :*: ef) e) =
          case e of
               Appl op args         -> simple
               Lit lit              -> simple
               Ref r                -> simple
               If cond cons alt     -> Expr (l :*: simplifyC (Cor [cons ^. annCheck , alt ^. annCheck]) :*: ef) e
               LetRec bnds bod      -> simple
               Lambda ids r bod     -> simple
               Begin exps           -> 
                 Expr (l :*: firstCheck :*: ef) $ Begin (exp' : exps')
                   where firstCheck  = exp ^. annCheck
                         exp'        = exp & annCheck .~ Cnone
                         (exp:exps') = scanr1 push exps
                         push e1 e2  = e1 & annCheck %~ \c1 -> simplifyC $ Cand [c1, removeChecksOn (e1 ^. annEffect) (e2 ^. annCheck)]
               Let [(id, e)] bod    ->
                 Expr (l :*: checksNoId :*: ef) $ Let [(id, set annCheck Cnone e)] bod
                   where (e_c, bod_c) = (e ^. annCheck, bod ^. annCheck)
                         checksNoId = simplifyC $ Cand [e_c, removeChecksOn (effectSingleton id `mappend` ef) bod_c]

removeChecksOn :: Effect -> Check -> Check
removeChecksOn ef = transform f
  where f c@(Check _ _ (Right id)) | id `varInEffect` ef = Cnone
        f c = c

getAndDelete :: (MonadState (M.Map k v) m, Ord k) => k -> m (Maybe v)
getAndDelete k = do m_v <- gets $ M.lookup k
                    modify $ M.delete k
                    return m_v

mergeSameChecks :: Check -> Check
mergeSameChecks check = evalState (stripMerged check) grouped
  where grouped = M.fromListWith S.union [ ((typ, tgt), S.fromList labs) | Check labs typ tgt <- universe check ]
        stripMerged Cnone = return Cnone
        stripMerged (Cand cs) = Cand <$> mapM stripMerged cs
        stripMerged (Cor cs)  = Cor <$> mapM stripMerged cs
        stripMerged (Check _ typ tgt) = do m_labs <- getAndDelete (typ, tgt)
                                           case m_labs of
                                                Nothing -> return Cnone
                                                Just labs -> return $ Check (S.toAscList labs) typ tgt



type ChecksMap = M.Map TLabel (Check :*: Effect)
type CachedTypes = M.Map Ident (TLabel :*: Type)

eliminateRedundantChecks :: Expr CheckedLabel -> Step (Expr CheckedLabel)
eliminateRedundantChecks expr = return $ updateChecks finalChecks expr
  where startChecks :: ChecksMap
        startChecks = M.fromList [ (l, c :*: ef) | Expr (l :*: c :*: ef) _ <- universeBi expr :: [Expr CheckedLabel] ]
        finalChecks = execState redundantLoop startChecks
        updateChecks :: ChecksMap -> Expr CheckedLabel -> Expr CheckedLabel
        updateChecks checks expr = transformBi u expr
          where u (Expr (l :*: _) ie) = Expr (l :*: fromJust (M.lookup l checks)) ie
        
        allSet :: [Ident]
        allSet = [ r | Expr _ (Ref r) <- sets ]
          where sets = [ var | Expr _ (Appl f [var, _]) <- universeBi expr :: [Expr CheckedLabel], isRefTo "set!" f ]

        redundantLoop :: State ChecksMap ()
        redundantLoop = do evalStateT (walk expr) M.empty
                           modify $ M.map (_1 %~ (simplifyC . mergeSameChecks . simplifyC))

        stripWithCache :: TLabel -> Check -> StateT CachedTypes (State ChecksMap) Check
        stripWithCache l cs = do check <- simplifyC <$> transformM strip cs
                                 lift $ updateChecksMap l $ \_ -> check
                                 return check
          where strip c@(Check ls typ (Right id)) =
                  do res <- gets $ M.lookup id
                     case res of
                          Just (l_top :*: typ_top)
                            | typ == typ_top -> do lift $ updateChecksMap l_top $ \check -> simplifyC $ Cand [check, c]
                                                   return Cnone
                          _ -> return c
                strip x = return x
                updateChecksMap l f = do map <- get
                                         let Just (c :*: ef) = M.lookup l map
                                         put $ M.insert l (f c :*: ef) map
        updateCachedTypes :: TLabel -> Check -> StateT CachedTypes (State ChecksMap) ()
        updateCachedTypes l check = update check
          where update Cnone = return ()
                update (Cand cs) = mapM_ update cs
                update (Cor cs) = sequence_ [ modify (M.insert id (unknownLabel :*: TAny)) | c <- cs, Check _ typ (Right id) <- universe c ]
                update (Check ls typ (Left lv)) = return ()
                update (Check ls typ (Right id)) = modify (M.insert id (l :*: typ))

        unknownLabel = error $ "Trying to add check to unknown label."

        lowerBound :: (TLabel :*: Type) -> (TLabel :*: Type) -> (TLabel :*: Type)
        lowerBound t1 t2 | t1 == t2 = t1
        lowerBound _  _  = unknownLabel :*: TAny

        -- With every type test τ? x, fix type of x to τ until next assignment.
        walk :: Expr CheckedLabel -> StateT CachedTypes (State ChecksMap) ()
        walk (Expr _ (Lit _)) = return ()
        walk (Expr _ (Ref _)) = return ()
        walk (Expr (l :*: c :*: ef) ie) =
          do c' <- stripWithCache l c
             updateCachedTypes l c'
             case ie of
               -- Function application can affect variables. Reset their type.
               (Appl   f args)        -> do mapM_ walk (f:args)
                                            forM_ (effectToList ef) $ \id -> modify (M.insert id (unknownLabel :*: TAny))
               (If     cond cons alt) -> do cached <- get
                                            m1 <- lift $ execStateT (walk cons) cached
                                            m2 <- lift $ execStateT (walk alt) cached
                                            put $ M.unionWith lowerBound m1 m2
               (Let    [(id, e)] bod) -> do walk e
                                            modify $ M.insert id (l :*: TAny)
                                            walk bod
               (LetRec bnds bod)      -> do mapM_ walk $ map snd bnds
                                            forM_ (map fst bnds) $ \id -> modify $ M.insert id (l :*: TAny)
                                            walk bod
               (Lambda ids r bod)     -> do cached <- get
                                            let act = do forM_ allSet $ \id -> modify $ M.insert id (unknownLabel :*: TAny)
                                                         -- TODO: r is a list
                                                         forM_ (params ids r) $ \id -> modify $ M.insert id (l :*: TAny)
                                                         walk bod
                                            lift $ evalStateT act cached
               (Begin  exps)          -> mapM_ walk exps



data Distance = Distance Depth Depth Depth

instance Show Distance where
  showsPrec _ (Distance def check use) = \s -> (show def ++ "-" ++ show check) ++ s

mkDistance def check use = Distance (use - def) (check - def) 0


(Distance d1 c1 u1) `lowestCheckAndUse` (Distance d2 c2 u2) = 
  case ((c1 `compare` c2) `mappend` (u1 `compare` u2)) of
       GT -> Distance d1 c1 u1
       _  -> Distance d2 c2 u2

data MobilityReport = MRPing Depth | MRAT Ident Distance | MRRAT Depth Ident Distance

relativeDistance :: Depth -> Distance -> Distance
relativeDistance d (Distance def check use) = Distance (f def) (f check) (f use)
  where f x = (x * 100) `div` d

generateMobilityStats :: Expr CheckedLabel -> Step (Expr CheckedLabel)
generateMobilityStats expr = do generateStats <- asks (^.cfgMobilityStats)
                                doMobility <- asks (^.cfgCheckMobility)
                                when generateStats $ do
                                  report "Number of checks" (T.pack $ show numChecks)
                                when (generateStats && doMobility) $ do
                                  report "Mobility stats" (T.pack $ format stats)
                                return expr
  where format stats = unlines [ k ++ "\t" ++ show d | (k, d) <- M.toAscList stats ]
        stats = M.fromListWith lowestCheckAndUse compDists
        compDists = [ (id, relativeDistance d d') | MRRAT d id d' <- execWriter (runReaderT (go 0 expr) (MI M.empty M.empty)) ]
        numChecks = length [ () | (Expr (_ :*: cs :*: _) _) <- universe expr, Check _ _ _ <- universe cs]

        go :: Depth -> Expr CheckedLabel -> ReaderT MobilityInfo (Writer [MobilityReport]) ()
        go depth (Expr (LPrim _ :*: _ :*: _) _)        = return ()
        go depth (Expr (LVar _ :*: _ :*: _) _)        = return ()
        go depth (Expr (LSource l :*: checks :*: _) e) =
          withChecks $ 
            case e of 
                 Appl op args         -> mapM_ descend (op:args)
                 Lit lit              -> return ()
                 Ref r                -> return ()
                 If cond cons alt     -> descend cond >> descend cons >> descend alt
                 Let [(id, e)] bod    -> descend e >> local (over bindDepths (M.insert id depth)) (descend bod)
                 LetRec bnds bod      -> local (over bindDepths (M.union (M.fromList [ (id, depth) | (id, _) <- bnds ]))) $
                                          mapM_ (descend.snd) bnds >> descend bod
                 Lambda ids r bod     ->
                   local (over bindDepths (M.union (M.fromList [ (id, depth) | id <- params ids r ]))) $
                     censor (makeRelative (params ids r)) (descend bod)
                 Begin exps           -> zipWithM_ go [depth+1..] exps
          where descend = go (depth + 1)
                withChecks body = local (over checkDepths (M.unionWith (M.unionWith min) newState)) $
                  tell [MRPing depth] >> forCurrentLabel >> body
                newState :: M.Map Int (M.Map Ident Depth)
                newState = M.fromListWith (M.unionWith const)
                   [ (lab, M.singleton target depth) | Check labs _ (Right target) <- universe checks, LSource lab <- labs]
                forCurrentLabel = do (MI bindsMap checksMap) <- ask
                                     let checks = checksMap ^. at l
                                     case checks of
                                          Nothing      -> return ()
                                          Just checks_ -> tell [ MRAT i (mkDistance d0 d depth)
                                                               | (i, d) <- M.toList checks_
                                                               , let Just d0 = bindsMap ^. at i ]
                makeRelative ids reports = concatMap select reports
                  where realDepth = maximum [ d | MRPing d <- reports ] - depth
                        select (MRAT id d) | id `elem` ids = [MRRAT realDepth id d]
                        select report     = [report]
        go depth e        = error ("wtf " ++ show e)

maybeAnnotateLabels :: Expr CheckedLabel -> Step (Expr CheckedLabel)
maybeAnnotateLabels expr = do doAnnotate <- asks (^.cfgAnnotateLabels)
                              if doAnnotate
                                 then return $ annotate expr
                                 else return expr

annotate :: Expr CheckedLabel -> Expr CheckedLabel
annotate expr = transformBi ann expr
  where annotatedLabels = S.fromList [ lab | Expr (_ :*: checks :*: _) _ <- universe expr, Check labs _ _ <- universeBi checks, LSource lab <- labs]
        syn x = Expr (LSyn :*: Cnone :*: emptyEffect) x 
        ann (Expr (LSource l :*: cs :*: ef) (Appl f args)) | l `S.member` annotatedLabels =
          Expr (LSource l :*: cs :*: ef) $ Appl (syn $ Ref "@") (syn (Lit (LitInt (fromIntegral l))) : f : args)
        ann x = x


reifyChecks :: Expr CheckedLabel -> Step (Expr TLabel)
reifyChecks = return . go
  where go (Expr (l :*: checks :*: _) e) =
          let simply e = reify (simplifyC checks) (Expr l e) in
              case e of
                 Appl op args         -> simply (Appl (go op) (map go args))
                 Lit lit              -> simply (Lit lit)
                 Ref r                -> simply (Ref r)
                 If cond cons alt     -> simply (If (go cond) (go cons) (go alt))
                 Let [(id, e)] bod    -> simply (Let [(id, go e)] (go bod))
                 LetRec bnds bod      -> simply (LetRec (over (mapped._2) go bnds) (go bod))
                 Lambda ids r bod     -> simply (Lambda ids r (go bod))
                 Begin es             -> simply (Begin $ map go es)

reify :: Check -> Expr TLabel -> Expr TLabel
reify Cnone e = e
reify checks e = appl "check" [reify' checks, e]
  where reify' :: Check -> Expr TLabel
        reify' (Cnone) = syn (Lit (LitBool True))
        reify' (Cor cs) = appl "or" $ map reify' cs
        reify' (Cand cs) = appl "and" $ map reify' cs
        reify' (Check blame prim cause) = appl (test prim) (syn (toExpr cause) : map (syn . toBlame) (nub blame))
          where test TInt         = "number?"
                test TString      = "string?"
                test TBool        = "boolean?"
                test TChar        = "char?"
                test TSymbol      = "symbol?"
                test TVoid        = "void?"
                test TVec         = "vector?"
                test TPair        = "pair?"
                test TPort        = "port?"
                test (TFun _ _ _) = "procedure?"

        syn e = Expr LSyn e
        appl f args = syn (Appl (syn $ Ref f) args)
        toExpr (Left lit) = Lit lit
        toExpr (Right r) = Ref r
        toBlame LSyn = error "tried to assign blame to synthetic label"
        toBlame (LVar _) = error "tried to assign blame to type variable"
        toBlame (LSource i) = Lit (LitInt $ fromIntegral i)
        toBlame (LPrim r)   = Ref r
