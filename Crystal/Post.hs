{-# LANGUAGE PatternGuards #-}
module Crystal.Post (postprocess, DeclExpr) where

import Control.Lens hiding (transform, universe)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import Data.List
import Data.Generics
import Data.Generics.Biplate
import qualified Data.Map as M

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
undoLetLet expr = do let (expr', ps) = runWriter $ transformBiM f expr
                     let ps' = M.map (inline ps') ps
                     return $ inline ps' expr'
  where f e@(Expr l (Let [(id, app)] b)) =
          case b of
               Expr l' (If cond cons alt)
                  | isTmp && oneMention -> tell (M.singleton id app)  >> return b
               Expr l' (Let bnds bod)
                  | isTmp && oneMention -> tell (M.singleton id app) >> return b
                  | otherwise              -> return $ Expr l (Let ((id, app) : bnds) bod)
               Expr l' (Appl f args)
                  | isTmp && not (isRefTo "check" f) -> tell (M.singleton id app) >> return b
               Expr _ (Ref id') | oneMention -> return app
               _ -> return e
            where isTmp = "tmp-" `isPrefixOf` id
                  oneMention = Just 1 == (M.lookup id =<< M.lookup l mentions)
        f x = return x
        mentions = computeMentions expr

computeMentions :: Expr TLabel -> M.Map TLabel (M.Map Ident Int)
computeMentions expr = mentionsMap
  where mentionsMap = M.fromList [(l, mentions e)| Expr l e <- universeBi expr ]
        mentions (Lit l)            = M.empty
        mentions (Ref r)            = M.singleton r 1
        mentions (Appl f args)      = M.unionsWith (+) (m f : map m args)
        mentions (If cond cons alt) = M.unionsWith (+) [m cond, m cons, m alt]
        mentions (Let bnds bod)     = M.unionsWith (+) (m bod : map (m . snd) bnds)
        mentions (LetRec bnds bod)  = M.unionsWith (+) (m bod : map (m . snd) bnds)
        mentions (Lambda ids r bod) = m bod
        mentions (Begin es)         = M.unionsWith (+) (map m es)
        m e = mentionsMap M.! (e ^. ann)

inline :: M.Map Ident (Expr TLabel) -> Expr TLabel -> Expr TLabel
inline m expr = transformBi f expr
  where f (Expr _ (Ref var)) | Just expr' <- M.lookup var m = expr'
        f x = x
