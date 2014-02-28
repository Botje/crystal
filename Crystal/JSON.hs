{-#LANGUAGE FlexibleContexts #-}
{-#LANGUAGE TypeSynonymInstances, FlexibleInstances, OverloadedStrings #-}
module Crystal.JSON where

import Data.Aeson
import Data.Aeson.Encode
import Data.Aeson.Types
import qualified Data.HashMap.Strict as HM
import qualified Data.Text.Lazy as T
import Data.Text.Lazy.Builder

import Crystal.AST

encode :: ToJSON (Expr a) => Expr a -> T.Text
encode = toLazyText . fromValue . toJSON

instance ToJSON a => ToJSON (Expr a) where
  toJSON (Expr a ie) = Object (HM.insert "ann" (toJSON a) obj)
    where Object obj = toJSON ie

obj :: String -> [Pair] -> Value
obj typ pairs = object ("type" .= typ : pairs )

str :: String -> String
str = id

instance ToJSON LitVal where
  toJSON (LitChar c)   = obj "Literal" [ "value" .= show c ]
  toJSON (LitString s) = obj "Literal" [ "value" .= show s ]
  toJSON (LitInt    i) = obj "Literal" [ "value" .= show i ]
  toJSON (LitFloat  d) = obj "Literal" [ "value" .= show d ]
  toJSON (LitBool   b) = obj "Literal" [ "value" .= show b ]
  toJSON (LitSymbol s) = obj "Literal" [ "value" .= ("'"++show s) ]
  toJSON (LitVoid)     = obj "Literal" [ "value" .= str "#<void>" ]
  toJSON (LitList lvs) = obj "ArrayExpression" [ "elements" .= map toJSON lvs ]

instance ToJSON a => ToJSON (InExpr (Expr a)) where
  toJSON (Lit lit)            = toJSON lit
  toJSON (Ref r)              = obj "Identifier" [ "name" .= r ]
  toJSON (If cond cons alt)   = obj "ConditionalExpression" [ "test" .= toJSON cond, "consequent" .= toJSON cons, "alternative" .= toJSON alt ]
  toJSON (Let [(id, e)] bod)  = obj "LetExpression" [ "head" .= toJSON [ object [ "id" .= id, "init" .= toJSON e ] ], "body" .= toJSON bod ]
  toJSON (LetRec bnds bod)    = obj "LetExpression" [ "head" .= toJSON [ map f bnds ], "body" .= toJSON bod ]
    where f (id, e) = object [ "id" .= id, "init" .= toJSON e ]
  toJSON (Lambda ids bod)     = obj "FunctionExpression" [ "params" .= toJSON [ ids ], "body" .= toJSON bod ]
  toJSON (Begin es)           = obj "SequenceExpression" [ "expressions" .= toJSON (map toJSON es) ]
  toJSON (Appl f args)        = obj "CallExpression" [ "callee" .= toJSON f, "arguments" .= toJSON [ map toJSON args ] ]
