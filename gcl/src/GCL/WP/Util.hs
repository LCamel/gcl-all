{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}

module GCL.WP.Util where

import Control.Monad
  ( forM,
    unless,
  )
import Control.Monad.RWS
  ( MonadReader (ask),
    MonadWriter (..),
    local,
    withRWST,
  )
import qualified Data.Hashable as Hashable
import Data.Loc (Loc (..))
import Data.Loc.Range (Range)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import GCL.Common
  ( Counterous (..),
    Fresh (..),
    Index,
    TypeEnv,
    TypeInfo,
    freshName',
  )
import GCL.Predicate
  ( Origin (..),
    PO (..),
    Pred,
    Spec (Specification),
  )
import GCL.WP.Types
import Numeric (showHex)
import Pretty (toString)
import Syntax.Abstract.Types (Type (..))
import Syntax.Common
  ( Name (..),
    nameToText,
  )
import Syntax.Typed
import Syntax.Typed.Operator (disjunct)
import Syntax.Typed.Util

-- Syntax Manipulation

--- grouping a sequence of statement by assertions and specs

-- Assert         -> SAsrt stmt
-- other stmt     \
-- other stmt        SStmts [other stmts]
-- other stmt     /
-- LoopInvariant  -> SAsrt stmt
-- other stmt     \
-- other stmt        SStmts [other stmts]
-- other stmt     /
-- Spec           -> SSpec stmt

groupStmts :: [Stmt] -> [SegElm]
groupStmts [] = []
groupStmts (s@(Assert _ _) : stmts) = SAsrt s : groupStmts stmts
groupStmts (s@LoopInvariant {} : stmts) = SAsrt s : groupStmts stmts
groupStmts (s@(Spec _ _ _) : stmts) = SSpec s : groupStmts stmts
groupStmts (s : stmts) = case groupStmts stmts of
  [] -> [SStmts [s]]
  (SStmts ss : segs) -> SStmts (s : ss) : segs
  (s' : segs) -> SStmts [s] : s' : segs

--- removing assertions (while keeping loop invariants).
--- succeed if there are no specs.

stripAsserts :: [Stmt] -> Maybe [Stmt]
stripAsserts [] = Just []
stripAsserts (Assert _ _ : stmts) = stripAsserts stmts
stripAsserts (s1@LoopInvariant {} : s2@Do {} : stmts) =
  (s1 :) <$> stripAsserts (s2 : stmts)
stripAsserts (LoopInvariant {} : stmts) = stripAsserts stmts
stripAsserts (Spec _ _ _ : _) = Nothing
stripAsserts (If gcmds l : stmts) = do
  gcmds' <- forM gcmds $ \(GdCmd guard body l') -> do
    body' <- stripAsserts body
    return (GdCmd guard body' l')
  stmts' <- stripAsserts stmts
  return (If gcmds' l : stmts')
stripAsserts (Do gcmds l : stmts) = do
  gcmds' <- forM gcmds $ \(GdCmd guard body l') -> do
    body' <- stripAsserts body
    return (GdCmd guard body' l')
  stmts' <- stripAsserts stmts
  return (Do gcmds' l : stmts')
stripAsserts (s : stmts) = (s :) <$> stripAsserts stmts

disjunctGuards :: [GdCmd] -> Pred
disjunctGuards = disjunct . getGuards

-- PO handling

tellPO :: Pred -> Pred -> Origin -> WP ()
tellPO p q origin = unless (p == q) $ do
  -- p' <- substitute [] [] p
  -- q' <- substitute [] [] q
  let anchorHash =
        Text.pack $ showHex (abs (Hashable.hash (toString (p, q)))) ""
  tell ([PO p q anchorHash Nothing origin], [], [], mempty)

tellPO' :: Origin -> Pred -> Pred -> WP ()
tellPO' l p q = tellPO p q l

tellSpec :: Pred -> Pred -> [(Index, TypeInfo)] -> Range -> WP ()
tellSpec p q typeEnv l = do
  -- p' <- substitute [] [] p
  -- q' <- substitute [] [] q
  i <- countUp
  tell ([], [Specification i p q l typeEnv], [], mempty)

throwWarning :: StructWarning -> WP ()
throwWarning warning = tell ([], [], [warning], mempty)

-- Misc.

withFreshVar :: Type -> (Expr -> WP a) -> WP a
withFreshVar t f = do
  name <- freshName' "bnd"
  let var = Var name t NoLoc
  withRWST
    ( \(decls, scopes) st ->
        ((Map.insert (nameToText name) Nothing decls, scopes), st)
    )
    (f var)

withLocalScopes :: ([[Text]] -> WP a) -> WP a
withLocalScopes f = do
  (_, scopes) <- ask
  f scopes

withScopeExtension :: [Text] -> WP a -> WP a
withScopeExtension names =
  local (\(defns, scopes) -> (defns, names : scopes))

freshPreInScope :: Text -> [Text] -> Text
freshPreInScope pref scope
  | not (pref `elem` scope) = pref
  | otherwise = freshAux 0
  where
    freshAux :: Int -> Text
    freshAux i
      | fre `elem` scope = freshAux (1 + i)
      | otherwise = fre
      where
        fre = Text.pack (pref' ++ show i)
    pref' = Text.unpack pref

instance Fresh WP where
  fresh = freshPre "m"
  freshPre p = withLocalScopes (return . freshPreInScope p . concat)
