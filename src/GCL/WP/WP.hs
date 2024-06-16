{-# LANGUAGE OverloadedStrings #-}

module GCL.WP.WP where

import           Control.Arrow                  ( first, second )
import           Control.Monad.Except           ( MonadError(throwError)
                                                , forM
                                                )
import           Data.Text                      ( Text )
import           Data.Loc                       ( Loc(..), locOf )
import           Data.Map                       ( fromList )
import           GCL.Predicate                  ( Pred(..) )
import           GCL.Predicate.Util             ( conjunct
                                                , toExpr
                                                )
import           GCL.Common                     ( Fresh(..)
                                                , freshName
                                                , freshName'
                                                )
import           Pretty                         ( toText )
import GCL.WP.Type
import GCL.WP.Util
import qualified Syntax.Abstract               as A
import qualified Syntax.Abstract.Operator      as A
import qualified Syntax.Abstract.Util          as A
import Syntax.Common.Types                     ( Name(..)
                                               , nameToText )
import Syntax.Substitution

-- import Debug.Trace
-- import Prettyprinter
-- import Prettyprinter.Render.String

wpFunctions :: TstructSegs
            -> (TwpSegs, TwpSStmts, Twp)
wpFunctions structSegs = (wpSegs, wpSStmts, wp)
 where
 wpStmts :: [A.Stmt] -> Pred -> WP Pred
 wpStmts = wpSegs . groupStmts

  -- handels segments without a precondition.
  -- switches back to structSegs when seeing an assertion
 wpSegs :: [SegElm] -> Pred -> WP Pred
 wpSegs []                 post = return post
 wpSegs (SStmts ss : segs) post = do
  post' <- wpSegs segs post
  wpSStmts ss post'
 wpSegs (SSpec (A.Spec _ range) : segs) post = do
  post' <- wpSegs segs post
  tellSpec post' post' range
  return post'
 wpSegs (SAsrt (A.Assert p l) : segs) post = do
  structSegs (Assertion p l, Nothing) segs post
  return (Assertion p l)
 wpSegs (SAsrt (A.LoopInvariant p bd l) : segs) post = do
  structSegs (LoopInvariant p bd l, Just bd) segs post
  return (Assertion p l) -- SCM: erasing bound information?
 wpSegs _ _ = error "Missing case in wpSegs"

  -- "simple" version of wpStmts.
  -- no assertions and specs (in the outer level),
  -- but may contain invariants in secondary run

 wpSStmts :: [A.Stmt] -> Pred -> WP Pred
 wpSStmts [] post = return post
 wpSStmts (A.LoopInvariant inv _ _ : A.Do gcmds _ : stmts) post = do  -- this happens only in secondary run
  post' <- wpSStmts stmts post
  let guards = A.getGuards gcmds
  return
    .        Constant
    $        inv
    `A.conj` (           (inv `A.conj` A.conjunct (map A.neg guards))
             `A.implies` toExpr post'
             )
 wpSStmts (stmt : stmts) post = do
  post' <- wpSStmts stmts post
  wp stmt post'

 wp :: A.Stmt -> Pred -> WP Pred
 wp (A.Abort _       ) _    = return (Constant A.false)
 wp (A.Skip  _       ) post = return post

 wp (A.Assign xs es _) post = substitute xs es post

 wp (A.AAssign (A.Var x _) i e _) post =
  substitute [x] [A.ArrUpd (A.nameVar x) i e NoLoc] post

 wp (A.AAssign _ _ _ l) _    = throwError (MultiDimArrayAsgnNotImp l)

 wp (A.Do _     l     ) _    = throwError $ MissingAssertion l -- shouldn't happen

 wp (A.If gcmds _     ) post = do
  pres <- forM gcmds $ \(A.GdCmd guard body _) ->
    Constant . (guard `A.imply`) . toExpr <$> wpStmts body post
  return (conjunct (disjunctGuards gcmds : pres))

 wp (A.Proof _ _ _       ) post = return post

 wp (A.Alloc x (e : es) _) post = do -- non-empty
    {- wp (x := es) P = (forall x', (x' -> es) -* P[x'/x])-}
   x'    <- freshName' (toText x) -- generate fresh name using the exisiting "x"
   post' <- substitute [x] [A.nameVar x'] (toExpr post)

   return $ Constant (A.forAll [x'] A.true (newallocs x' `A.sImp` post'))
  where
   newallocs x' = A.sconjunct
    ( (A.nameVar x' `A.pointsTo` e)
    : zipWith (\i -> A.pointsTo (A.nameVar x' `A.add` A.number i)) [1 ..] es
    )

 wp (A.HLookup x e _) post = do
    {- wp (x := *e) P = (exists v . (e->v) * ((e->v) -* P[v/x])) -}
  v     <- freshName' (toText x) -- generate fresh name using the exisiting "x"
  post' <- substitute [x] [A.nameVar v] (toExpr post)

  return $ Constant
    (A.exists [v] A.true (entry v `A.sConj` (entry v `A.sImp` post')))
  where entry v = e `A.pointsTo` A.nameVar v

 wp (A.HMutate e1 e2 _) post = do
    {- wp (e1* := e2) P = (e1->_) * ((e1->e2) -* P) -}
  e1_allocated <- allocated e1
  return $ Constant
    (e1_allocated `A.sConj` ((e1 `A.pointsTo` e2) `A.sImp` toExpr post))

 wp (A.Dispose e _) post = do
    {- wp (dispose e) P = (e -> _) * P -}
  e_allocated <- allocated e
  return $ Constant (e_allocated `A.sConj` toExpr post)
-- TODO:
 wp (A.Block prog _) post = wpBlock prog post
 wp _         _    = error "missing case in wp"

 wpBlock :: A.Program -> Pred -> WP Pred
 wpBlock (A.Program _ decls _props stmts _) post = do
   let localNames = declaredNames decls
   (xs, ys) <- withLocalScopes (\scopes ->
                withScopeExtension (map nameToText localNames)
                 (calcLocalRenaming (concat scopes) localNames))
   stmts' <- subst (toSubst ys) stmts
   withScopeExtension (xs ++ (map (nameToText . snd) ys))
     (wpStmts stmts' post)
   -- if any (`member` (fv pre)) (declaredNames decls)
   --   then throwError (LocalVarExceedScope l)
   --   else return pre
  where toSubst = fromList . map (\(n, n') -> (n, A.Var n' (locOf n')))

calcLocalRenaming :: [Text] -> [Name] -> WP ([Text], [(Text, Name)])
calcLocalRenaming _ [] = return ([], [])
calcLocalRenaming scope (x:xs)
  | t `elem` scope = do
        x' <- freshName t (locOf x)
        second ((t,x') :) <$> calcLocalRenaming scope xs
  | otherwise =
        first (t:) <$> calcLocalRenaming scope xs
 where t = nameToText x

toMapping :: [(Text, Name)] -> A.Mapping
toMapping = fromList . map cvt
  where cvt (x, y) = (x, A.Var y (locOf y))

allocated :: Fresh m => A.Expr -> m A.Expr
allocated e = do
  v <- freshName' "new"
  return (A.exists [v] A.true (e `A.pointsTo` A.nameVar v))
  -- allocated e = e -> _

-- debugging
-- pp :: Pretty a => a -> String
-- pp = renderString . layoutPretty defaultLayoutOptions . pretty
