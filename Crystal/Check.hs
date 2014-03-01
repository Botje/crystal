{-#LANGUAGE FlexibleContexts, TypeOperators, DeriveDataTypeable, PatternGuards #-}
{-#LANGUAGE TypeSynonymInstances, FlexibleInstances, OverloadedStrings #-}
module Crystal.Check where

import Control.Lens hiding (transform, universe, (.=))
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
import Data.Generics
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
addChecks = reifyChecks <=< maybeDumpTree "check-simplification" <=< generateMobilityStats <=< {- eliminateRedundantChecks <=< -} maybeDumpTree "check-mobility" <=< moveChecksUp <=< introduceChecks

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
               Lambda ids bod       -> simply (Lambda ids (go bod))
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
               Lambda ids bod       -> simple
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

type ChecksMap = M.Map TLabel (Check :*: Effect)

eliminateRedundantChecks :: Expr CheckedLabel -> Step (Expr CheckedLabel)
eliminateRedundantChecks expr = return $ updateChecks finalChecks expr
  where startChecks :: ChecksMap
        startChecks = M.fromList [ (l, c :*: ef) | Expr (l :*: c :*: ef) _ <- universeBi expr :: [Expr CheckedLabel] ]
        finalChecks = execState redundantLoop startChecks
        updateChecks :: ChecksMap -> Expr CheckedLabel -> Expr CheckedLabel
        updateChecks checks expr = transformBi u expr
          where u (Expr (l :*: _) ie) = Expr (l :*: fromJust (M.lookup l checks)) ie

        redundantLoop :: State ChecksMap ()
        redundantLoop = runReaderT (walk expr) M.empty -- apply optimization -- loop
        walk :: Expr CheckedLabel -> ReaderT (M.Map Ident Type) (State ChecksMap) ()
        walk expr = return ()
        
generateMobilityStats :: Expr CheckedLabel -> Step (Expr CheckedLabel)
generateMobilityStats expr = do generateStats <- asks (^.cfgMobilityStats)
                                when generateStats $ do
                                  report "Mobility stats" (T.pack $ format stats)
                                  report "Number of checks" (T.pack $ show numChecks)
                                return expr
  where format stats = unlines [ k ++ "\t" ++ unwords (map show vs) | (k, vs) <- M.toAscList stats ]
        stats = M.map sort $ M.fromListWith (++) $ map (over _2 return) checkDepths
        checkDepths = execWriter (runReaderT (go 0 expr) M.empty)
        numChecks = length [ () | (Expr (_ :*: check :*: _) _) <- universe expr, check /= Cnone]

        go :: Int -> Expr CheckedLabel -> ReaderT (M.Map Int [(Ident, Int)]) (Writer [(Ident, Int)]) ()
        go depth (Expr (LPrim _ :*: _ :*: _) _)        = return ()
        go depth (Expr (LVar _ :*: _ :*: _) _)        = return ()
        go depth (Expr (LSource l :*: checks :*: _) e) =
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
  where go (Expr (l :*: checks :*: _) e) =
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
          where test TInt         = "number?"
                test TString      = "string?"
                test TBool        = "boolean?"
                test TChar        = "character?"
                test TSymbol      = "symbol?"
                test TVoid        = "void?"
                test TVec         = "vector?"
                test TPair        = "pair?"
                test (TFun _ _ _) = "procedure?"

        syn e = Expr LSyn e
        appl f args = syn (Appl (syn $ Ref f) args)
        toExpr (Left lit) = Lit lit
        toExpr (Right r) = Ref r
        toBlame LSyn = error "tried to assign blame to synthetic label"
        toBlame (LVar _) = error "tried to assign blame to type variable"
        toBlame (LSource i) = Lit (LitInt $ fromIntegral i)
        toBlame (LPrim r)   = Ref r
