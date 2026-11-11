{-# LANGUAGE OverloadedStrings #-}

module Test.Reduce5 (tests) where

import GCL.Range (mkPos, mkRange)
import qualified Syntax.Abstract.Types as A
import Syntax.Common.Types (Name (..))
import qualified Syntax.Typed.Reduce5 as Reduce5
import qualified Syntax.Typed.Types as T
import qualified Test.Reduce.Contract as Contract
import Test.Reduce.Support (DefnEnv, loaded, prettyExpr, reduciblePathsWith)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "Reduce5"
    [ Contract.tests "contract" reduce Reduce5.redexRT Reduce5.reduceAll,
      generatedNames
    ]
  where
    reduce env expression path = pure (Reduce5.tryReduceAt env expression path)

-- Generated names depend only on the expression being displayed, not on names
-- an earlier part of the same click or run used and then discarded.
generatedNames :: TestTree
generatedNames =
  testGroup
    "generated names"
    [ -- F t = ⟨∀ x : 0 ≤ x : t < x⟩; x := x + 1 { F x }. Opening t takes a
      -- name that the result no longer contains; x's fallback starts at zero.
      testCase "a name used only while opening a scope leaves no gap" $ do
        let (env, start) = loaded ["var x : Int", "{:", "  F t = ⟨ ∀ x : 0 ≤ x : t < x ⟩", ":}", "x := x + 1", "{ F x }"]
            expected = "⟨ ∀ ?x_0 : 0 ≤ ?x_0 : x + 1 < ?x_0 ⟩"
        prettyExpr (clickAll env start) @?= expected
        fmap prettyExpr (Reduce5.reduceAll 10 env start) @?= Right expected,
      -- (case f of y -> (y, ?)[x \ a], the same again). Each selection defers
      -- f into a slot that stays on the hole. The second slot must avoid the
      -- first in reduceAll too, although the first did not exist initially.
      testCase "a later step avoids slots that earlier steps left pending" $ do
        let selection = T.Case (var f) [T.CaseClause (A.PattBinder y) (T.Subst (T.Tuple [var y, hole]) [(x, var a)])] Nothing
            env = [(f, var b)]
            start = T.Tuple [selection, selection]
        case clickAll env start of
          clicked@(T.Tuple [T.Tuple [_, T.Subst _ first], T.Tuple [_, T.Subst _ second]]) -> do
            assertBool "the pending slots must have distinct names" (map fst first /= map fst second)
            Reduce5.reduceAll 100 env start @?= Right clicked
          result -> assertFailure ("unexpected result: " <> show result)
    ]
  where
    hole = T.EHole (T.Hole "hole" 0 (A.TBase A.TInt Nothing) (mkRange (mkPos 1 1) (mkPos 1 2)) mempty)

-- Repeatedly click the first marked path, which is the order reduceAll uses.
clickAll :: DefnEnv -> T.Expr -> T.Expr
clickAll env expression = case reduciblePathsWith Reduce5.redexRT env expression of
  path : _ | Just next <- Reduce5.tryReduceAt env expression path -> clickAll env next
  _ -> expression

f, x, y, a, b :: Name
f = Name "f" Nothing
x = Name "x" Nothing
y = Name "y" Nothing
a = Name "a" Nothing
b = Name "b" Nothing

var :: Name -> T.Expr
var name = T.Var name (A.TBase A.TInt Nothing) Nothing
