module Crystal.Post (postprocess, DeclExpr) where

import Control.Lens hiding (transform)
import Control.Monad
import Control.Monad.Reader
import Data.List
import Data.Generics
import Data.Generics.Biplate

import Crystal.AST
import Crystal.Config
import Crystal.Misc
import Crystal.Tuple
import Crystal.Type

type Decl = (Ident, Expr TLabel)
type DeclExpr = ([Decl], Expr TLabel)

postprocess :: Expr TLabel -> Step DeclExpr 
postprocess = undoLetrec <=< undoLetLet

undoLetrec :: Expr TLabel -> Step DeclExpr
undoLetrec expr = do addDefines <- not `fmap` asks (^.cfgAnnotateLabels)
                     if addDefines
                        then return (decls, core)
                        else return ([], expr)
  where (decls, core) = go expr
        go (Expr _ (LetRec bnds bod)) = go bod & _1 %~ (bnds++)
        go (Expr _ (Let bnds bod)) = go bod & _1 %~ (bnds++)
        go e = ([], e)

undoLetLet :: Expr TLabel -> Step (Expr TLabel)
undoLetLet = return . transformBi f
  where f e@(Expr l (Let [(id, app)] b)) =
          case b of
               Expr l' (If cond cons alt)
                  | "tmp-" `isPrefixOf` id -> Expr l (If (inline id app cond) cons alt)
               Expr l' (Let bnds bod)
                  | "tmp-" `isPrefixOf` id -> inline id app b
                  | otherwise              -> Expr l (Let ((id, app) : bnds) bod)
               Expr l' (Appl f args)
                 | "tmp-" `isPrefixOf` id && not (isRefTo "check" f) -> inline id app b
               Expr _ (Ref id') | id' == id -> app
               _ -> e
        f x = x

inline :: Ident -> Expr TLabel -> Expr TLabel -> Expr TLabel
inline id expr = transformBi f
  where f (Expr _ (Ref var)) | var == id = expr
        f x = x
