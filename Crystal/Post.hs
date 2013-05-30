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
postprocess = undoLetrec . undoLetLet . undoLetIf

undoLetrec expr = (decls, core)
  where (decls, core) = go expr
        go (Expr _ (LetRec bnds bod)) = undoLetrec bod & _1 %~ (bnds++)
        go (Expr _ (Let bnds bod)) = undoLetrec bod & _1 %~ (bnds++)
        go e = ([], e)

undoLetIf = transform f
  where f e@(Expr _ (Let [(id, app)] b)) =
          case b of
               Expr l (If (Expr _ (Ref r)) cons alt)
                          | r == id -> Expr l (If app cons alt)
               _ -> e
        f x = x

undoLetLet = transform f
  where f e@(Expr l (Let [(id, app)] b)) =
          case b of
               Expr _ (Let bnds bod) -> Expr l (Let ((id, app) : bnds) bod)
               _ -> e
        f x = x
