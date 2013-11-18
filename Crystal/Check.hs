{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
module Crystal.Check where

import Control.Lens hiding (transform, universe)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List
import Debug.Trace
import qualified Data.Map as M
import Data.Generics
import Data.Generics.Biplate

import Crystal.AST
import Crystal.Config
import Crystal.Misc
import Crystal.Tuple
import Crystal.Type

data Check = Cnone
           | Cand [Check]
           | Cor [Check]
           | Check [TLabel] Type (Either LitVal Ident)
             deriving (Show, Eq, Data, Typeable)

type CheckedLabel = TLabel :*: Check

_check :: Simple Lens CheckedLabel Check
_check = _2

annCheck :: Simple Lens (Expr CheckedLabel) Check
annCheck = ann._check

addChecks :: Expr TypedLabel -> Step (Expr TLabel)
addChecks = reifyChecks <=< generateMobilityStats <=< eliminateRedundantChecks <=< moveChecksUp <=< introduceChecks

introduceChecks :: Expr TypedLabel -> Step (Expr CheckedLabel)
introduceChecks expr = return $ go expr
  where go (Expr (l :*: t) e) =
          let simply = Expr (l :*: Cnone) in
          case e of 
               Appl op args         -> Expr (l :*: checks) (Appl op' args')
                 where labLookup l =
                         case [ litOrIdent e | (Expr (l' :*: _) e) <- op':args', l == l' ] of
                              [] -> error ("Label lookup failed. Failing expression: " ++ show e)
                              (x:xs) -> x
                       (op':args') = map go (op:args)
                       checks = simplifyC (typeToChecks labLookup t)
                       litOrIdent (Ref r) = Right r
                       litOrIdent (Lit l) = Left l
               Lit lit              -> simply (Lit lit)
               Ref r                -> simply (Ref r)
               If cond cons alt     -> simply (If (go cond) (go cons) (go alt))
               Let [(id, e)] bod    -> simply (Let [(id, go e)] (go bod))
               LetRec bnds bod      -> simply (LetRec (over (mapped._2) go bnds) (go bod))
               Lambda ids bod       -> simply (Lambda ids (go bod))
               Begin es             -> simply (Begin $ map go es)

typeToChecks :: (TLabel -> Either LitVal Ident) -> Type -> Check
typeToChecks look (TIf (blame, cause) prim var rest) =
  Cand [Check [blame] prim (look cause), typeToChecks look rest]
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
        f simple@(Expr (l :*: checks) e) =
          case e of
               Appl op args         -> simple
               Lit lit              -> simple
               Ref r                -> simple
               If cond cons alt     -> Expr (l :*: simplifyC (Cor [cons ^. annCheck , alt ^. annCheck])) e
               LetRec bnds bod      -> simple
               Lambda ids bod       -> simple
               Begin exps           -> 
                 Expr (l :*: combinedChecks) $ Begin $ map (set annCheck Cnone) exps
                   where combinedChecks = Cand $ map (^. annCheck) exps
               Let [(id, e)] bod    ->
                 Expr (l :*: checksNoId) $ Let [(id, set annCheck Cnone e)] bod
                   where (e_c, bod_c) = (e ^. annCheck, bod ^. annCheck)
                         checksNoId = simplifyC $ Cand [e_c, removeChecksOn id bod_c]

removeChecksOn id = transform f
  where f c@(Check _ _ (Right id')) | id == id' = Cnone
        f c = c

type TypeMap = M.Map Ident Type
type Dups    = [(Ident, [TLabel])]
type DupsMap = M.Map Ident [TLabel]

toDupsMap :: Dups -> DupsMap
toDupsMap = M.fromListWith (++)

eliminateRedundantChecks :: Expr CheckedLabel -> Step (Expr CheckedLabel)
eliminateRedundantChecks expr = return $ fst $ runReader (runWriterT $ go expr) M.empty
  where go :: Expr CheckedLabel -> WriterT Dups (Reader TypeMap) (Expr CheckedLabel)
        go orig@(Expr (l :*: checks) e) =
          do env <- ask
             let (env', checks', dupsC) = elimRedundant env checks
             (e', dupsE) <- local (const env') $ lift $ runWriterT (f e)
             let dups = M.unionWith (++) (toDupsMap dupsC) (toDupsMap dupsE)
             tell $ M.toList dups
             return (Expr (l :*: simplifyC (addDuplicates dups checks')) e')
        f :: InExpr (Expr CheckedLabel) -> WriterT Dups (Reader TypeMap) (InExpr (Expr CheckedLabel))
        f e =
          case e of
             Appl op args         -> Appl op `liftM` mapM go args
             Lit lit              -> return e
             Ref r                -> return e
             If cond cons alt     -> liftM2 (If cond) (go cons) (go alt)
             Let [(id, e)] bod    -> do e_ <- go e
                                        bod_ <- local (M.insert id TAny) $ go bod
                                        return $ Let [(id, e_)] bod_
             LetRec bnds bod ->
               local (M.union $ M.fromList (bnds & (mapped._2) .~ TAny)) $ do
                 bnds' <- mapM (\(nam, exp) -> go exp >>= \l -> return (nam, l)) bnds
                 bod'  <- go bod
                 return $ LetRec bnds' bod'
             Lambda ids bod       -> Lambda ids `liftM` local (M.union (defaultEnv ids)) (go bod)
             Begin exps           -> Begin `liftM` mapM go exps
        defaultEnv ids = M.fromList [ (x, TAny) | x <- ids ]

addDuplicates :: DupsMap -> Check -> Check
addDuplicates dups c | M.null dups = c
addDuplicates dups c = transform f c
  where f c@(Check lab typ (Right i)) =
          case M.lookup i dups of
               Nothing -> c
               Just lab' -> Check (lab++lab') typ (Right i)
        f c = c

elimRedundant :: TypeMap -> Check -> (TypeMap, Check, Dups)
elimRedundant env checks = (env', simplifyC checks', duplicates)
  where ((checks', env'), duplicates) = runWriter (runStateT (go checks) env)
        go :: Check -> StateT TypeMap (Writer Dups) Check
        go Cnone     = return Cnone
        go (Cand cs) = Cand `liftM` mapM go cs
        go (Cor cs)  = do env <- get
                          cs' <- lift $ mapM (\c -> evalStateT (go c) env) cs
                          return $ Cor cs'
        go c@(Check lab typ target) =
          do env <- get
             case target of
                  Left lit -> return c
                  Right id ->
                    case M.lookup id env  of
                         Nothing   -> trace ("ignoring unbound identifier " ++ show id) $ return c -- error ("Unbound identifier " ++ id ++ " in check " ++ show c)
                         Just TAny -> modify (M.insert id typ) >> return c
                         Just typ' | typ == typ' -> tell [(id, lab)] >> return Cnone
                                   | otherwise   -> return c

generateMobilityStats :: Expr CheckedLabel -> Step (Expr CheckedLabel)
generateMobilityStats expr = do generateStats <- asks (^.cfgMobilityStats)
                                when generateStats $ do
                                  report "Mobility stats" (format stats)
                                  report "Number of checks" (show numChecks)
                                return expr
  where format stats = unlines [ k ++ "\t" ++ unwords (map show vs) | (k, vs) <- M.toAscList stats ]
        stats = M.map sort $ M.fromListWith (++) $ map (over _2 return) checkDepths
        checkDepths = execWriter (runReaderT (go 0 expr) M.empty)
        numChecks = length [ () | (Expr (_ :*: check) _) <- universe expr, check /= Cnone]

        go :: Int -> Expr CheckedLabel -> ReaderT (M.Map Int [(Ident, Int)]) (Writer [(Ident, Int)]) ()
        go depth (Expr (LPrim _ :*: _) _)        = return ()
        go depth (Expr (LVar _ :*: _) _)        = return ()
        go depth (Expr (LSource l :*: checks) e) =
          withChecks $ 
            case e of 
                 Appl op args         -> mapM_ descend (op:args)
                 Lit lit              -> return ()
                 Ref r                -> return ()
                 If cond cons alt     -> descend cond >> descend cons >> descend alt
                 Let [(id, e)] bod    -> descend e >> descend bod
                 LetRec bnds bod      -> mapM (descend.snd) bnds >> descend bod
                 Lambda ids bod       -> descend bod
                 Begin exps           -> zipWithM_ go [depth+1..] exps
          where descend = go (depth + 1)
                withChecks body = local (M.unionWith (++) newState) (forCurrentLabel >> body)
                newState = M.fromListWith (++)
                   [ (lab, [(target, depth)]) | Check labs _ (Right target) <- universe checks, LSource lab <- labs]
                forCurrentLabel = do checks <- asks (M.lookup l)
                                     case checks of
                                          Nothing      -> return ()
                                          Just checks_ -> tell [ (i, depth - d0) | (i, d0) <- checks_ ]
        go depth e        = error ("wtf " ++ show e)


reifyChecks :: Expr CheckedLabel -> Step (Expr TLabel)
reifyChecks = return . go
  where go (Expr (l :*: checks) e) = 
          let simply e = reify (simplifyC checks) (Expr l e) in
              case e of
                 Appl op args         -> simply (Appl (go op) (map go args))
                 Lit lit              -> simply (Lit lit)
                 Ref r                -> simply (Ref r)
                 If cond cons alt     -> simply (If (go cond) (go cons) (go alt))
                 Let [(id, e)] bod    -> simply (Let [(id, go e)] (go bod))
                 LetRec bnds bod      -> simply (LetRec (over (mapped._2) go bnds) (go bod))
                 Lambda ids bod       -> simply (Lambda ids (go bod))
                 Begin es             -> simply (Begin $ map go es)

reify :: Check -> Expr TLabel -> Expr TLabel
reify Cnone e = e
reify checks e = appl "check" [reify' checks, e]
  where reify' :: Check -> Expr TLabel
        reify' (Cnone) = syn (Lit (LitBool True))
        reify' (Cor cs) = appl "or" $ map reify' cs
        reify' (Cand cs) = appl "and" $ map reify' cs
        reify' (Check blame prim cause) = appl (test prim) (syn (toExpr cause) : map (syn . toBlame) (nub blame))
          where test TInt       = "number?"
                test TString    = "string?"
                test TBool      = "boolean?"
                test TChar      = "character?"
                test TSymbol    = "symbol?"
                test TVoid      = "void?"
                test TVec       = "vector?"
                test TPair      = "pair?"
                test (TFun _ _) = "procedure?"

        syn e = Expr LSyn e
        appl f args = syn (Appl (syn $ Ref f) args)
        toExpr (Left lit) = Lit lit
        toExpr (Right r) = Ref r
        toBlame LSyn = error "tried to assign blame to synthetic label"
        toBlame (LVar _) = error "tried to assign blame to type variable"
        toBlame (LSource i) = Lit (LitInt $ fromIntegral i)
        toBlame (LPrim r)   = Ref r
