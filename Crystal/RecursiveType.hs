{-#LANGUAGE DeriveDataTypeable #-}
module Crystal.RecursiveType where

import Control.Arrow (second)
import Control.Lens (_1, _2, _3, mapped, (^.), (.~), (&), view, to, (%~))
import Control.Lens.TH
import Data.List
import Data.Function
import Debug.Trace
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Generics
import Data.Generics.Uniplate.Data

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative
import Test.QuickCheck
import Text.Show

import Crystal.Trace
import Crystal.Tuple
import Crystal.Type

debugging = True

traced f x | debugging = trace (f x) x
traced f x | otherwise = x

-- TODO: remove
type T = Type

type Head = (Int, [T])
type HeadsMap = M.Map Head (Maybe T)

braid :: [Int] -> Effect -> S.Set T -> T
braid vars ef result = if S.null result
                          then TFun vars ef TError
                          else TFun vars ef $ Tor $ S.elems result 

unbraid :: T -> S.Set T
unbraid (Tor ts) = S.unions $ map unbraid ts
unbraid (TIf ls t1 t2 t) | t1 == t2  = unbraid t
                         | isTVar t2 = S.map (TIf ls t1 t2) $ unbraid t
                         | otherwise = S.empty
unbraid (TChain appl var lab body) = S.map (TChain appl var lab) $ unbraid body
unbraid (TAppl fun args) = S.fromList [ TAppl fun args' | args' <- sequence (map g args) ]
  where g (l :*: t) = map (l :*:) $ S.toList $ unbraid t
unbraid t = S.singleton t

getTFunEffect :: Type -> Effect
getTFunEffect (TFun _ ef _) = ef

getTFunBody :: Type -> Type
getTFunBody (TFun _ _ bod) = bod

canon :: T -> T
canon t = flatten tests spine
  where (tests, spine) = descend t
        descend (TIf ls t1 t2 t)
          | t1 == t2 = descend t
          | all (`elem` concreteTypes) [t1, t2] = ([], TError)
          | t2 == TAny || isTFun t1 =
            let (tests, spine) = descend t
            in ((ls,t1,t2) : tests, spine)
          | otherwise = let TVar tv = t2
                            (tests, spine) = descend (subst [(tv, t1)] t)
                        in ((ls,t1,t2) : tests, spine)
        descend (TChain appl var lab body) =
          let (tests, spine) = descend body
              (varTests, otherTests) = partition (\t -> t ^._3 == TVar var) tests
          in (otherTests, TChain appl var lab $ flatten varTests spine)
        descend t = ([], simplify t)
        flatten tests t =
          let sorted = nub $ sortBy (compare `on` (^. _3)) tests
          in foldr (\(ls,t1,t2) rest -> TIf ls t1 t2 rest) t sorted 


tip :: T -> T
tip = snd . splitThread

splitThread :: T -> (T -> T, T)
splitThread (TIf ls t1 t2 t) = (TIf ls t1 t2 . prefix', tip)
  where (prefix', tip) = splitThread t
splitThread (TChain appl var lab body) = (TChain appl var lab . prefix', tip)
  where (prefix', tip) = splitThread body
splitThread t = (id, t)

hasApplies :: Type -> Bool
hasApplies (TChain _ _ _ _) = True
hasApplies (TIf _ _ _ t)    = hasApplies t
hasApplies (TAppl _ _)      = True
hasApplies _ = False

typeToTrace :: TVar -> Type -> Trace
typeToTrace tv (TFun args ef body) = processTrace trace 
  where trace = Trace tk ef S.empty S.empty todo
        todo = unbraid body
        tk = (tv, map TVar args)

traceToType :: Trace -> [TVar] -> Type
traceToType (Trace _ ef _seen concrete _todo) vars =
  simplify $ braid vars ef concrete

matchKey :: TraceKey -> TraceKey-> Bool
matchKey (f1, xs1) (f2, xs2) = f1 == f2 && and (zipWith (\t1 t2 -> t1 == TAny || t1 == t2) xs1 xs2)

toTraceKey :: TraceKey -> TraceKey
toTraceKey (tv, vs) = (tv, [ if isTVar v then TAny else v | v <- vs ])

specialize :: TraceKey -> Trace -> Trace
specialize tk@(tv, vs) orig = processTrace trace
  where toSpecialize = [ (i, v) | (oldV, v) <- zip origVs vs, v /= TAny, oldV /= v, let TVar i = oldV ]
        origVs = orig ^. traceTraceKey._2
        newTk = (tv, zipWith max origVs vs)
        allTraces    = (orig ^. traceSeen) `S.union` (orig ^. traceConcrete) `S.union` (orig ^. traceTodo)
        trace = orig & traceTraceKey .~ newTk
                     & traceSeen     .~ S.empty
                     & traceConcrete .~ S.empty
                     & traceTodo     .~ S.map (canon . subst toSpecialize) allTraces

applyToTraceKey :: Type -> TraceKey
applyToTraceKey (TAppl (TVar tv) args) = (tv, types)
  where types = [ if isTVar t then TAny else t | (_ :*: t) <- args ]
applyToTraceKey t | traceShow t False = undefined

processTrace :: Trace -> Trace
processTrace trace = trace & traceSeen     .~ seen'
                           & traceConcrete .~ concrete'
                           & traceTodo     .~ todo'
  where (seen', concrete', todo') = traced (\x -> "processTrace " ++ show myTraceKey ++ "\n" ++ show x) $ loop (trace ^. traceSeen) (trace ^. traceConcrete) (trace ^. traceTodo)
        myTraceKey = trace ^. traceTraceKey
        myArgs = snd myTraceKey
        isApplyOfMe appl@(TAppl _ _) = applyToTraceKey appl == toTraceKey myTraceKey
        isApplyOfMe _ = False
        loop seen concrete todo = traceShow (seen,concrete, todo) $
          let (applies, concrete') = S.partition hasApplies todo
              (seenApplies, todoApplies) = S.partition (`S.member` seen) applies
              (meApplies, otherApplies) = S.partition (isApplyOfMe . tip) todoApplies
          in if S.null (meApplies `S.difference` seenApplies)
                then (meApplies `S.union` seen, S.map canon concrete' `S.union` concrete, todoApplies)
                else let (oneApply,restApplies) = S.deleteFindMin meApplies
                     in loop (oneApply `S.insert` seen)
                             (S.map canon concrete' `S.union` concrete)
                             (walk oneApply `S.union` restApplies `S.union` otherApplies)
          where walk :: T -> S.Set T
                walk thread = let (prefix, tip) = splitThread thread
                                  chained = extractChainVars thread
                              in case tip of 
                                   TAppl (TVar v) args ->
                                     -- Refuse to expand threads of the form (TChain ... v ... (TAppl self [..., v, ...]))
                                     if any (\(_ :*: t) -> t `elem` chained) args || myArgs == (map (^. _2) args)
                                        then S.singleton thread -- S.singleton (prefix TAny)
                                        else let toReplace = [ (tv, new) | (old, new) <- zip myArgs (map (^. _2) args), old /= new, let TVar tv = old]
                                             in traced (\_ -> show "walk, expanding " ++ show (applyToTraceKey tip) ++ "\n") $ S.map (canon . prefix) $ S.map (subst toReplace) $ S.unions [seen, concrete, todo]

extractChainVars :: Type -> [Type]
extractChainVars t = [ TVar v | TChain _ v _ _ <- universe t ] 

solveLetrec :: [TVar] -> [Type] -> [Type]
solveLetrec vars types = [ traceToType t args | (tv, TFun args _ _) <- funs, let k = (tv, map (const TAny) args), let Just t = M.lookup k solved]
  where funs   = zip vars types
        traces = traced (\x -> "input: \n" ++ prettyTraces x) $ M.fromList [ (toTraceKey (trace ^. traceTraceKey), trace) | (tv, t) <- funs, let trace = typeToTrace tv t]
        solved = traced (\x -> "solved: \n" ++ prettyTraces x) $ transitiveTraces $ exploreTraces traces 

exploreTraces :: Traces -> Traces
exploreTraces traces = traced (\x -> "explore: \n" ++ prettyTraces x) $ execState (addTrace $ M.keysSet traces) M.empty
  where functionsInScope = S.map fst $ M.keysSet traces
        addTrace :: S.Set TraceKey -> State Traces ()
        addTrace tks | S.null tks = 
          do traces' <- get
             return ()
        addTrace tks =
          do traces' <- get
             let (tk,tks') = S.deleteFindMin tks
             let hasTk = M.member tk traces'
             if hasTk 
                then addTrace tks'
                else do let suitable  = M.filterWithKey (\tk' _ -> tk' `matchKey` tk) (traces `M.union` traces')
                            bestTrace = snd $ minimumBy (compare `on` (length . filter (==TAny) . snd . fst)) $ M.assocs suitable
                            trace     = specialize tk bestTrace
                        put $ M.insert tk trace traces'
                        -- TODO: intersect traceTV with original traces set
                        let (todo, concrete) = (trace ^. traceTodo, trace ^. traceConcrete)
                        let threads = S.toList $ S.union todo concrete
                        let applies = [ applyToTraceKey t
                                      | thread <- threads
                                      , t@(TAppl (TVar tv) args) <- universe thread
                                      , tv `S.member` functionsInScope ]
                        addTrace $ (S.fromList applies) `S.union` tks'

expandTrace :: Traces -> Trace -> Trace
expandTrace solved t = processTrace $
                         t & traceConcrete %~ (S.map canon . S.unions . map expand . S.toList)
                           & traceSeen     %~ (S.map canon . S.unions . map expand . S.toList)
                           & traceTodo     %~ (S.map canon . S.unions . map expand . S.toList)
  where expand (TIf ls t1 t2 t) = S.map (TIf ls t1 t2) $ expand t
        expand (TChain appl var lab body) =
          case M.lookup (applyToTraceKey appl) solved of
              Just trace -> S.fromList
                              [ prefix body''
                              | thread <- S.toList $ expanded appl trace
                              , let (prefix, tip) = splitThread thread
                              , let body' = subst [(var, tip)] body
                              , body'' <- S.toList $ expand body'
                              ]
              Nothing    -> S.map (TChain appl var lab) $ expand body
        expand appl@(TAppl _ _) =
          case M.lookup (applyToTraceKey appl) solved of
               Just trace -> expanded appl trace
               Nothing    -> S.singleton appl
        expand t = S.singleton t
        expanded (TAppl _ args) trace = let toReplace = [ (tv, v) | (i, v) <- zip (trace ^. traceTraceKey._2) (map (^. _2) args), i /= v, let TVar tv = i ]
                                       in S.map (subst toReplace) (trace ^. traceConcrete)

transitiveTraces :: Traces -> Traces
transitiveTraces traces = traced (\_ -> "transitive input: \n" ++ prettyTraces traces) $ execState (loop traces) M.empty
  where calls = transitiveCalls traces
        loop traces | M.null traces = return ()
        loop traces = do solved <- get
                         let seen = M.keysSet solved
                             working = M.mapWithKey (\k _ -> fromJust (M.lookup k calls) `S.difference` seen) traces
                             keyFun (tk, tks) = (S.size tks, not $ tk `S.member` tks)
                             next    = minimumBy (compare `on` keyFun) $ M.toList working
                             (tk, called) = next
                             tks = tk : S.toList (S.delete tk called)
                             workTraces = [ expandTrace solved trace | tk <- tks, let Just trace = M.lookup tk traces ]
                         consider workTraces
                         loop $ M.difference traces $ M.fromList $ zip tks (repeat undefined)
        consider :: [Trace] -> State Traces ()
        consider traces = traced (\_ -> "consider input: \n" ++ pretty traces) $
            modify $ M.union $ considerFix seed traces
          where seed = M.fromList [ (toTraceKey (trace ^. traceTraceKey), trace) | trace <- traces, let conc = trace ^. traceConcrete, not $ S.null conc ]
                considerFix :: Traces -> [Trace] -> Traces
                considerFix solved traces = traced (\_ -> "after one round: \n" ++ pretty (M.elems expanded)) $
                  if M.null (M.differenceWith diff solved expanded)
                     then expanded
                     else considerFix expanded traces
                  where expanded = M.fromList $ map (\trace -> (toTraceKey (trace ^. traceTraceKey), trace)) $ map (expandTrace solved) traces
                        diff t1 t2 = if (t1 ^. traceConcrete) == (t2 ^. traceConcrete) then Nothing else Just t2

transitiveCalls :: Traces -> M.Map TraceKey (S.Set TraceKey)
transitiveCalls traces = M.map fixCalls calls
  where functionsInScope = S.map fst $ M.keysSet traces
        calls = M.map (S.fromList . extractCalls) traces
        extractCalls t = [ applyToTraceKey ta
                         | thread <- S.toList (view traceConcrete t `S.union` view traceTodo t)
                         , ta@(TAppl (TVar tv) _) <- universe thread
                         , tv `S.member` functionsInScope ]
        fixCalls ts | S.size ts == S.size ts' = ts
                    | otherwise = fixCalls ts'
          where ts' = ts `S.union` S.unions [ s | tk <- S.toList ts, let Just s = M.lookup tk calls ]

replaceTips :: Traces -> Trace -> Trace
replaceTips traces t =
  if S.null suitable
     then t
     else t & traceTodo .~ rest
            & traceConcrete %~ flip S.union (S.unions (map replaceTip $ S.toList suitable))
  where (suitable, rest) = S.partition (\thread -> applyToTraceKey (tip thread) `M.member` traces) (t ^. traceTodo)
        replaceTip thread = let (prefix, tip@(TAppl var args)) = splitThread thread
                                Just trace' = M.lookup (applyToTraceKey tip) traces
                                toReplace = [ (tv, v) | (i, v) <- zip (trace' ^. traceTraceKey._2) (map (^. _2) args), i /= v, let TVar tv = i ]
                            in S.map (canon . prefix . subst toReplace) (trace' ^. traceConcrete)

subst :: [(Int, T)] -> T -> T
subst m body = simplify $ transform (apply' m) body
  where apply' m (TVar x) = maybe (TVar x) id $ lookup x m
        apply' m t = t

typeLeafs :: T -> [T]
typeLeafs (Tor ts) = concatMap typeLeafs ts
typeLeafs (TIf _ _ _ t) = typeLeafs t
typeLeafs (TFun _ _ t) = typeLeafs t
typeLeafs t = [t]
