module Crystal.Post (postprocess, DeclExpr) where

import Control.Lens hiding (transform)
import Control.Monad
import Data.List
import Data.Generics
import Data.Generics.Biplate

import Crystal.AST
import Crystal.Misc
import Crystal.Tuple
import Crystal.Type

type Decl = (Ident, Expr TLabel)
type DeclExpr = ([Decl], Expr TLabel)

postprocess :: Expr TLabel -> Step DeclExpr 
postprocess = undoLetrec <=< undoLetLet

undoLetrec :: Expr TLabel -> Step DeclExpr
undoLetrec expr = return (decls, core)
  where (decls, core) = go expr
        go (Expr _ (LetRec bnds bod)) = go bod & _1 %~ (bnds++)
        go (Expr _ (Let bnds bod)) = go bod & _1 %~ (bnds++)
        go e = ([], e)

undoLetLet :: Expr TLabel -> Step (Expr TLabel)
undoLetLet = return . transform f
  where f e@(Expr l (Let [(id, app)] b)) =
          case b of
               Expr _ (Let bnds bod) -> Expr l (Let ((id, app) : bnds) bod)
               Expr _ (Ref id') | id' == id -> app
               _ -> e
        f x = x
