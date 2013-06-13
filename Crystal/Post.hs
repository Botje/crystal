module Crystal.Post (postprocess) where

import Control.Lens hiding (transform)
import Data.List
import Data.Generics
import Data.Generics.Biplate

import Crystal.AST
import Crystal.Tuple
import Crystal.Type

type Decl = (Ident, Expr TLabel)

postprocess :: Expr TLabel -> ([Decl], Expr TLabel)
postprocess = undoLetrec . undoLetLet

undoLetrec expr = (decls, core)
  where (decls, core) = go expr
        go (Expr _ (LetRec bnds bod)) = undoLetrec bod & _1 %~ (bnds++)
        go (Expr _ (Let bnds bod)) = undoLetrec bod & _1 %~ (bnds++)
        go e = ([], e)

undoLetLet :: Expr TLabel -> Expr TLabel
undoLetLet = transform f
  where f e@(Expr l (Let [(id, app)] b)) =
          case b of
               Expr _ (Let bnds bod) -> Expr l (Let ((id, app) : bnds) bod)
               Expr _ (Ref id') | id' == id -> app
               _ -> e
        f x = x
