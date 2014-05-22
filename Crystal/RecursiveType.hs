{-#LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Crystal.RecursiveType where

import Control.Arrow (second)
import Control.Lens (_1, _2, mapped, (^.), (.~), (&))
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

import Crystal.Tuple
import Crystal.Type

-- TODO: remove
type T = Type

type Head = (Int, [T])
type HeadsMap = M.Map Head (Maybe T)

type TraceKey = (TVar, [Type])

data Trace = Trace { _traceTraceKey :: TraceKey
                   , _traceEffects  :: Effect
                   , _traceSeen     :: S.Set T
                   , _traceConcrete :: S.Set T
                   , _traceTodo     :: S.Set T
                   } deriving (Show)

$(makeLenses ''Trace)

braid :: [Int] -> Effect -> S.Set T -> T
braid vars ef result = if S.null result
                          then TFun vars ef TError
                          else TFun vars ef $ Tor $ S.elems result 

unbraid :: T -> S.Set T
unbraid (Tor ts) = S.unions $ map unbraid ts
unbraid (TIf ls t1 t2 t) | t1 == t2  = unbraid t
                           | isTVar t2 = S.map (TIf ls t1 t2) $ unbraid t
                           | otherwise = S.empty
unbraid t = S.singleton t

getTFunEffect :: Type -> Effect
getTFunEffect (TFun _ ef _) = ef

getTFunBody :: Type -> Type
getTFunBody (TFun _ _ bod) = bod

canon :: T -> T
canon t = descend [] t
  where descend env (TIf ls t1 t2 t)
          | t1 == t2 = descend env t
          | all (`elem` concreteTypes) [t1, t2] = TError
          | otherwise = let TVar tv = t2 in descend ((t1,ls,t2):env) $ subst [(tv, t1)] t
        descend env t = foldr (\(t1,ls,t2) rest -> TIf ls t1 t2 rest) t $ sortBy (compare `on` (^. _2)) env


tip :: T -> T
tip (TIf _ _ _ t) = tip t
tip t = t

splitThread :: T -> (T -> T, T)
splitThread (TIf ls t1 t2 t) = (TIf ls t1 t2 . prefix', tip)
  where (prefix', tip) = splitThread t
splitThread t = (id, t)

data Mutual = Mutual [(TVar, T)] deriving (Data, Typeable, Eq, Show)

solveLetrec :: [TVar] -> [Type] -> [Type]
solveLetrec vars types = map snd solved
  where mut = Mutual $ zip vars types
        Mutual solved = solveMutual mut

traced x = traceShow x x

typeToTrace :: TVar -> Type -> Trace
typeToTrace tv (TFun args ef body) = traced $ processTrace trace 
  where trace = Trace tk ef S.empty S.empty todo
        todo = unbraid body
        tk = (tv, map TVar args)

traceToType :: Trace -> [TVar] -> Type
traceToType (Trace _ ef _seen concrete _todo) vars =
  simplify $ braid vars ef concrete

matchKey :: TraceKey -> TraceKey-> Bool
matchKey (_, xs1) (_, xs2) = and $ zipWith (\t1 t2 -> t1 == TAny || t1 == t2) xs1 xs2

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
-- applyToTraceKey x | trace (show x) False = undefined
applyToTraceKey (TAppl (TVar tv) args) = (tv, types)
  where types = [ if isTVar t then TAny else t | (_ :*: t) <- args ]

processTrace :: Trace -> Trace
processTrace trace = trace & traceSeen .~ seen' & traceConcrete .~ concrete' & traceTodo .~ todo'
  where (seen', concrete', todo') = loop (trace ^. traceSeen) (trace ^. traceConcrete) (trace ^. traceTodo)
        myTraceKey = trace ^. traceTraceKey
        myArgs = snd myTraceKey
        isApplyOfMe appl@(TAppl _ _) = applyToTraceKey appl == toTraceKey myTraceKey
        isApplyOfMe _ = False
        loop seen concrete todo =
          let (applies, concrete') = S.partition (isApply . tip) todo
              (seenApplies, todoApplies) = S.partition (`S.member` seen) applies
              (meApplies, otherApplies) = S.partition (isApplyOfMe . tip) todoApplies
          in Debug.Trace.trace ("process " ++ show myTraceKey ++" " ++ show (seen, concrete, todo)) $
              if S.null (meApplies `S.difference` seenApplies)
                then (meApplies `S.union` seen, concrete' `S.union` concrete, todoApplies)
                else let (oneApply,restApplies) = S.deleteFindMin meApplies
                     in loop (oneApply `S.insert` seen) (concrete' `S.union` concrete) (walk oneApply `S.union` restApplies `S.union` otherApplies)
          where walk :: T -> S.Set T
                walk thread = let (prefix, tip) = splitThread thread
                              in case tip of 
                                   TAppl (TVar v) args ->
                                     let toReplace = [ (tv, new) | (old, new) <- zip myArgs (map (^. _2) args), old /= new, let TVar tv = old]
                                     in S.map (canon . prefix) $ S.map (subst toReplace) $ S.unions [seen, concrete, todo]

solveMutual :: Mutual -> Mutual
solveMutual (Mutual funs) = traced $
     Mutual [ (tv, traceToType t args) | k@(tv, _) <- M.keys traces , let Just t = M.lookup k solved, let Just (TFun args _ _) = lookup tv funs ]
  where traces = M.fromList [ (toTraceKey (trace ^. traceTraceKey), trace) | (tv, t) <- funs, let trace = typeToTrace tv t]
        solved = exploreTraces traces 

type Traces = M.Map TraceKey Trace

exploreTraces :: Traces -> Traces
exploreTraces traces = execState (addTrace $ M.keysSet traces) M.empty
  where addTrace :: S.Set TraceKey -> State Traces ()
        addTrace tks | S.null tks = 
          do traces' <- get
             trace ("final traces: " ++ show traces') $ return ()
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
                        addTrace $ S.map (applyToTraceKey . tip) (trace ^. traceTodo) `S.union` tks'

transitiveTraces :: Traces -> Traces
transitiveTraces = id

subst :: [(Int, T)] -> T -> T
subst m body = transform (apply' m) body
  where apply' m (TVar x) = maybe (TVar x) id $ lookup x m
        apply' m t = t

typeLeafs :: T -> [T]
typeLeafs (Tor ts) = concatMap typeLeafs ts
typeLeafs (TIf _ _ _ t) = typeLeafs t
typeLeafs (TFun _ _ t) = typeLeafs t
typeLeafs t = [t]
