{-#LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Crystal.Trace where

import Control.Lens.TH

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
