{-# LANGUAGE PatternGuards, FlexibleContexts #-}
module Crystal.Transform (transformC) where

import Control.Arrow
import Control.Applicative
import Control.Lens hiding (transformM)
import Control.Monad
import Control.Monad.RWS
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer
import Data.Function
import Data.Generics
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text.Lazy as T
import Data.Generics.Uniplate.Operations
import System.Random hiding (next)

import Crystal.AST
import Crystal.Config
import Crystal.Env
import Crystal.JSON
import Crystal.Misc
import Crystal.Pretty
import Crystal.Seq

transformC :: Expr Label -> Step (Expr Label)
transformC = maybeDumpTree <=< denestLet <=< toANF <=< expandMacros <=< maybeMutate <=< flattenLets <=< splitLetRecs <=< alphaRename

alphaRename, splitLetRecs, flattenLets, maybeMutate, expandMacros, toANF, denestLet, maybeDumpTree :: Expr Label -> Step (Expr Label)

maybeDumpTree expr =
  do dump <- asks (^.cfgDumpTree)
     when dump $ do
       report "transform" $ encode expr
     return expr

denestLet expr = return $ transformBi denest expr
  where denest :: Expr Label -> Expr Label
        denest (Expr l (Let [(id, expr)] bod))
                  | Expr l_i (Let [(id_i, expr_i)] bod_i) <- expr
                  = denest $ Expr l_i $ Let [(id_i, expr_i)] $ denest (Expr l $ Let [(id, bod_i)] bod)
        denest x = x

toANF expr@(Expr start _) = return $ evalState (go expr return >>= updateRootLabel) (succ start)
  where go :: Expr Label -> (Expr Label -> State Int (Expr Label)) -> State Int (Expr Label)
        go e@(Expr l (Lit x)) k = k e
        go e@(Expr l (Ref r)) k = k e
        go (Expr l (Lambda ids r bod)) k = do body_ <- go bod return
                                              k (Expr l (Lambda ids r body_))
        go (Expr l (Begin [x]) ) k = go x k
        go (Expr l (Begin exps)) k =
          do exps_ <- mapM (flip go return) exps
             k (Expr l $ Begin exps_)
        go (Expr l (If cond cons alt)) k =
          goFloat cond $ \cond_ -> do cons_ <- (go cons return)
                                      alt_ <- (go alt return)
                                      k (Expr l $ If cond_ cons_ alt_)
        go (Expr l (Let [(name,expr)] bod)) k =
          go expr $ \expr_ -> do body_ <- go bod return
                                 k (Expr l $ Let [(name, expr_)] body_)
        go (Expr l (LetRec bnds bod)) k = 
          do bnds_ <- mapM (_2 (flip go return)) bnds
             bod_ <- go bod return
             k (Expr l $ LetRec bnds_ bod_)
        go (Expr l (Appl f args)) k =
          goFloat f $ \f_ ->
            goF args [] $ \args_ ->
              k (Expr l $ Appl f_ args_)

        goFloat :: Expr Label -> (Expr Label -> State Int (Expr Label)) -> State Int (Expr Label)
        goFloat expr k =
          case expr of 
            Expr l (If _ _ _) ->
              float expr k
            Expr l (Begin _) ->
              float expr k
            Expr l (Lambda _ _ _) ->
              float expr k
            Expr l (Let _ _) ->
              float expr k
            Expr l (LetRec _ _) ->
              float expr k
            Expr l (Appl _ _) ->
              float expr k
            otherwise ->
              go expr k
        
        float :: Expr Label -> (Expr Label -> State Int (Expr Label)) -> State Int (Expr Label)
        float expr k =
          do var <- next "tmp-"
             labRef <- nextSeq
             labLet <- nextSeq
             expr_ <- go expr return
             rest <- k (Expr labRef $ Ref var)
             return $ Expr labLet $ Let [(var, expr_)] rest

        goF [] args k = k (reverse args)
        goF (x:xs) args k = goFloat x $ \x_ -> goF xs (x_:args) k

makeExpr :: InExpr (Expr Label) -> State Label (Expr Label)
makeExpr expr = nextSeq >>= \s -> return $ Expr s expr

expandMacros expr@(Expr start _) = return $ evalState (transformBiM f expr >>= updateRootLabel) (succ start)
  where f :: Expr Label -> State Label (Expr Label)
        f expr@(Expr l (Appl (Expr _ (Ref r)) args)) =
          case (r, args) of
               ("and", []) -> return $ Expr l (Lit (LitBool True))
               ("and", _ ) -> foldM (g (flip . If)) (last args) (reverse $ init args)
               ("or",  []) -> return $ Expr l (Lit (LitBool False))
               ("or",  _ ) -> foldM (g If) (last args) (reverse $ init args)
               ("unless", (cond : exps)) -> do begin <- makeExpr $ Begin exps
                                               void  <- makeExpr $ Lit LitVoid
                                               makeExpr $ If cond void begin
               ("when", (cond : exps)) -> do begin <- makeExpr $ Begin exps
                                             void  <- makeExpr $ Lit LitVoid
                                             makeExpr $ If cond begin void
               (_   , [l]) | carLike r ->
                 foldM addCarStep l (reverse $ carSteps r)
               _ -> return expr
        f x = return x
        g fun bod test = do nam <- next "tmp-"
                            ifExpr <- makeExpr =<< liftM3 fun (makeExpr $ Ref nam) (makeExpr $ Ref nam) (return bod)
                            letExpr <- makeExpr $ Let [(nam, test)] ifExpr
                            return letExpr
        addCarStep bod 'a' = makeExpr (Ref "car") >>= \r -> makeExpr (Appl r [bod]) 
        addCarStep bod 'd' = makeExpr (Ref "cdr") >>= \r -> makeExpr (Appl r [bod]) 

carSteps = init . tail
                        
carLike :: Ident -> Bool
carLike [] = False
carLike n  = head n == 'c' && last n == 'r' && all (`elem` "ad") (carSteps n)

isSpecialForm :: Ident -> Bool
isSpecialForm r = r `elem` ["and", "or", "set!", "when", "unless"] || carLike r

updateRootLabel :: Expr Label -> State Label (Expr Label)
updateRootLabel (Expr _ e) = nextSeq >>= return . flip Expr e 

flattenLets expr@(Expr start _) = return $ evalState (transformBiM f expr >>= updateRootLabel) (succ start)
  where f :: Expr Label -> State Label (Expr Label)
        f (Expr l (Let [] bod)) = return bod
        f (Expr l (Let bnds bod)) | length bnds > 1 =
          do labels <- mapM (const nextSeq) bnds
             let body_ = foldr (\(lab, bnd) body -> Expr lab (Let [bnd] body)) bod $ zip labels bnds
             return body_
        f x = return x

type Idents = S.Set Ident

type Mutation a = RWST (M.Map Label Idents) [String] Int IO a

mutations :: [ Expr Label -> Mutation (Expr Label) ]
mutations = [ swapIf >=> swapRef , swapRef >=> swapIf ]

consumeFuel :: Mutation ()
consumeFuel = modify (subtract 1)

genericMut :: (Expr Label -> Mutation (Expr Label)) -> Expr Label -> Mutation (Expr Label)
genericMut mut = transformM go
  where go e = do fuel <- get
                  if fuel == 0
                     then return e
                     else mut e

swapIf :: Expr Label -> Mutation (Expr Label)
swapIf = genericMut si
  where si :: Expr Label -> Mutation (Expr Label)
        si e@(Expr l (If cond cons alt)) = 
           do roll <- liftIO (randomIO :: IO Float)
              if roll <= 0.01
                 then do consumeFuel
                         tell ["Swapped if branches at " ++ show l]
                         return $ Expr l (If cond alt cons)
                 else return e
        si other = return other

swapRef :: Expr Label -> Mutation (Expr Label)
swapRef = genericMut sr
  where sr :: Expr Label -> Mutation (Expr Label)
        sr e@(Expr l (Ref r)) =
          do roll <- liftIO (randomIO :: IO Float)
             Just bvs <- fmap (S.delete r) `fmap` asks (M.lookup l)
             if roll <= 0.01 && not (S.null bvs)
                then do consumeFuel
                        idx <- liftIO $ randomRIO (0, S.size bvs - 1)
                        let r' = S.elemAt idx bvs
                        tell ["Changed " ++ r ++ " to " ++ r' ++ " at " ++ show l]
                        return $ Expr l (Ref r')
                else return e
        sr other = return other

runMutation :: Mutation (Expr Label) -> Int -> M.Map Label Idents -> Step (Expr Label)
runMutation mut fuel bvs =
  do (tree, fuel', rep) <- liftIO $ runRWST mut bvs fuel
     if fuel == fuel'
        then runMutation mut fuel bvs
        else do report "Mutation" $ T.unlines $ map T.pack rep
                return tree


boundVariables :: Expr Label -> M.Map Label Idents
boundVariables expr = execState (go S.empty expr) M.empty
  where go bvs (Expr l ie) = 
          do modify (M.insert l bvs)
             case ie of
                Lit    lv               -> return ()
                Ref    r                -> return ()
                Appl   f args           -> mapM_ (go bvs) (f:args)
                If     cond cons alt    -> mapM_ (go bvs) [cond, cons, alt]
                Let    [(nam, exp)] bod -> go bvs exp >> go (S.insert nam bvs) bod
                LetRec bnds bod         -> do let bvs' = S.fromList (map fst bnds) `S.union` bvs
                                              mapM_ (go bvs') (bod : map snd bnds)
                Lambda args r bod       -> do let bvs' = S.fromList (maybeToList r ++ args) `S.union` bvs
                                              go bvs' bod
                Begin  es               -> mapM_ (go bvs) es

maybeMutate expr = do mutate <- asks (^.cfgMutate)
                      if mutate
                         then do choice <- liftIO $ randomRIO (0,length mutations - 1)
                                 let mut = mutations !! choice
                                 let fuel = 1
                                 runMutation (mut expr) fuel (boundVariables expr)
                         else return expr

splitLetRecs expr@(Expr start _) = return $ evalState (transformBiM f expr >>= updateRootLabel) (succ start)
  where f :: Expr Label -> State Label (Expr Label)
        f (Expr _ (LetRec bnds bod)) = float fv names
          where names = S.fromList $ map fst bnds
                fv = M.fromList $ map (second (\e -> names `S.intersection` freeVars e)) bnds
                float :: M.Map Ident Idents -> Idents -> State Label (Expr Label)
                float fv names | S.null names = return bod
                               | otherwise = do lab <- nextSeq
                                                let fv' = M.map (`S.difference` gone) fv
                                                bod <- float fv' (names `S.difference` gone)
                                                let bnds' = filter (flip S.member gone . fst) bnds
                                                if null zeroDeps
                                                   then return $ Expr lab (LetRec bnds' bod)
                                                   else return $ Expr lab (Let bnds' bod)
                  where minStar = minimumBy (compare `on` S.size) stars
                        zeroDeps = [ n | n <- S.toList names, Just s <- return $ M.lookup n fv, S.null s ]
                        gone = if null zeroDeps then minStar else S.fromList zeroDeps
                        stars = map (star fv . S.singleton) $ S.toList names
        f x = return x

star :: M.Map Ident Idents -> Idents -> Idents
star fv names = if names == names' then names' else star fv names'
  where names' = names `S.union` S.unions [ s | n <- S.elems names, Just s <- return $ M.lookup n fv ]

alphaRename expr@(Expr start _) = return $ fst $ evalRWS (f expr) startMap (M.keysSet startMap)
  where startMap = M.fromList [("check","check"), ("@","@")] `M.union` M.mapWithKey (\k _ -> k) main_env
        f :: Expr Label -> RWS (M.Map Ident Ident) [Int] (S.Set Ident) (Expr Label)
        f (Expr l e) =
          let simply ie = Expr l <$> ie
              rename r = do newName <- asks (M.lookup r)
                            case newName of
                                 Just n -> return n
                                 Nothing -> error $ "Unbound variable " ++ r
              withNewNames ids comp =
                do seenSet <- get
                   let (seen, notseen) = partition (`S.member` seenSet) ids
                   let newnames = zipWith (\s i -> (s, concat [s, "-", show i])) seen [1+S.size seenSet..]
                   put $ S.fromList (map snd newnames) `S.union` S.fromList notseen `S.union` seenSet
                   let oldnames = zip notseen notseen
                   local (M.union $ M.fromList (newnames ++ oldnames)) comp
          in
            case e of
                 Lit  lit -> simply $ return $ Lit lit
                 Ref  r | isSpecialForm r -> simply $ return $ Ref r
                        | otherwise -> simply $ Ref <$> rename r
                 Appl fun args -> simply $ Appl <$> f fun <*> mapM f args
                 Lambda ids r bod ->
                   do withNewNames (params ids r) $ do
                        ids' <- mapM rename ids
                        r' <- maybe (return Nothing) (\x -> Just `fmap` rename x) r
                        simply $ Lambda ids' r' <$> f bod
                 Begin exps -> simply $ Begin <$> mapM f exps
                 If cond cons alt -> simply $ If <$> f cond <*> f cons <*> f alt
                 Let bnds bod ->
                   do let (ids, exprs) = unzip bnds
                      exprs' <- mapM f exprs
                      withNewNames ids $ do
                        ids' <- mapM rename ids
                        bod' <- f bod
                        simply $ return $ Let (zip ids' exprs') bod'
                 LetRec bnds bod ->
                    do let (ids, exprs) = unzip bnds
                       withNewNames ids $ do
                         ids' <- mapM rename ids
                         exprs' <- mapM f exprs
                         bod' <- f bod
                         simply $ return $ LetRec (zip ids' exprs') bod'
