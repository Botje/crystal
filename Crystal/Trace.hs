{-#LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Crystal.Trace where

import Control.Lens
import Control.Lens.TH
import Data.Function
import Data.List

import qualified Data.Map as M
import qualified Data.Set as S

import Crystal.Type

type TraceKey = (TVar, [Type])

data Trace = Trace { _traceTraceKey :: TraceKey
                   , _traceEffects  :: Effect
                   , _traceSeen     :: S.Set Type
                   , _traceConcrete :: S.Set Type
                   , _traceTodo     :: S.Set Type
                   } deriving (Show)

$(makeLenses ''Trace)

type Traces = M.Map TraceKey Trace

pretty :: [Trace] -> String
pretty traces = concatMap (\x -> prettyTrace x "\n") traces
  where traces' = sortBy (compare `on` view traceTraceKey) traces

prettyTrace :: Trace -> String -> String
prettyTrace tr = shows (tr ^. traceTraceKey) . space . concrete . space . todo
  where space = (" "++)
        concrete = ("concrete="++) . shows (S.toList (tr ^. traceConcrete))
        todo = ("todo="++) . shows (S.toList (tr ^. traceTodo))

prettyTraces :: Traces -> String
prettyTraces traces = pretty $ M.elems traces
