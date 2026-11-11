{-# LANGUAGE OverloadedStrings #-}

module Test.LocallyNameless (tests) where

import qualified Data.Set as Set
import GCL.Range (mkPos, mkRange)
import qualified Syntax.Abstract.Types as A
import Syntax.Common.Types (Name (..), nameToText)
import qualified Syntax.Typed.LocallyNameless as L
import qualified Syntax.Typed.Types as T
import Test.Reduce (everyConstructor)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "locally nameless binding tools"
    [ testCase "conversion round trips every typed expression constructor" $
        mapM_ (\expression -> show (export (L.fromExpr expression)) @?= show expression) everyConstructor,
      testCase "shadowing resolves to the nearest binder, leaving free names alone" $ do
        let expression = lam x (T.Tuple [var x, lam x (var x), var y])
        case L.fromExpr expression of
          term@(L.Node T.Lam {} [L.Node T.Tuple {} [L.Bound 0 _, L.Node T.Lam {} [L.Bound 0 _], free]]) -> do
            free @?= L.fromExpr (var y)
            L.freeNames term @?= Set.singleton y
            L.wellScoped 0 term @?= True
            export term @?= expression
          term -> assertFailure ("unexpected binding structure: " <> show term),
      testCase "quantifier binders share a scope in declaration order" $ do
        let expression = T.Quant (var x) [(x, intType), (y, intType)] (T.Tuple [var x, var y]) (var x) Nothing
        case L.fromExpr expression of
          term@(L.Node T.Quant {} [operator, restriction@(L.Node T.Tuple {} [L.Bound 1 _, L.Bound 0 _]), L.Bound 1 _]) -> do
            operator @?= L.fromExpr (var x)
            L.freeNames term @?= Set.singleton x
            export (L.instantiate [L.fromExpr (var a), L.fromExpr (var b)] restriction) @?= T.Tuple [var a, var b]
          term -> assertFailure ("unexpected quantifier scope: " <> show term),
      testCase "case clauses have separate scopes, including tuple patterns" $ do
        let expression =
              T.Case
                (var a)
                [ T.CaseClause (A.PattTuple [A.PattBinder x, A.PattBinder y]) (T.Tuple [var x, var y]),
                  T.CaseClause (A.PattBinder y) (T.Tuple [var x, var y])
                ]
                Nothing
        case L.fromExpr expression of
          term@(L.Node T.Case {} [_, L.Node T.Tuple {} [L.Bound 1 _, L.Bound 0 _], L.Node T.Tuple {} [free, L.Bound 0 _]]) -> do
            free @?= L.fromExpr (var x)
            L.freeNames term @?= Set.fromList [a, x]
            export term @?= expression
          term -> assertFailure ("unexpected clause scopes: " <> show term),
      testCase "a state key is global while its value can refer to a local binder" $ do
        let expression = lam x (T.Subst (var y) [(x, var x)])
        case L.fromExpr expression of
          term@(L.Node T.Lam {} [L.Node (T.Subst _ [(key, _)]) [_, L.Bound 0 _]]) -> do
            key @?= x
            case export term of
              T.Lam binder _ (T.Subst subject [(target, value)]) _ -> do
                assertBool "a displayed global key must stay distinct from the binder" (binder /= x)
                subject @?= var y
                target @?= x
                value @?= var binder
              result -> assertFailure ("unexpected displayed table: " <> show result)
          term -> assertFailure ("unexpected table scope: " <> show term),
      -- λx. (x, a), detached: x is the fragment's own binder (index 0) and a
      -- refers one binder further out (index 1). Moving it under one more
      -- binder lifts only a.
      testCase "shifting lifts outer references but not a fragment's own binders" $ do
        let fragment outer = L.node (lam x (T.Tuple [])) [L.node (T.Tuple [var x, var a]) [L.Bound 0 (var x), L.Bound outer (var a)]]
        L.shift 1 0 (fragment 1) @?= fragment 2,
      testCase "opening and closing preserve references to an outer context" $ do
        let fragment = L.node (T.Tuple [var x, var y]) [L.Bound 0 (var x), L.fromExpr (var y)]
            closed = L.close [y] fragment
        case closed of
          L.Node T.Tuple {} [L.Bound 1 _, L.Bound 0 _] -> pure ()
          term -> assertFailure ("closing captured an existing outer variable: " <> show term)
        L.wellScoped 1 fragment @?= True
        L.wellScoped 2 closed @?= True
        L.open [y] closed @?= fragment,
      testCase "opening a multi-binder scope uses the corresponding free names" $ do
        let body = L.close [x, y] (L.fromExpr (T.Tuple [var x, var y]))
        export (L.open [a, b] body) @?= T.Tuple [var a, var b],
      testCase "instantiation lifts an outer-bound argument under an inner binder" $ do
        let body = L.fromExpr (lam x (var y))
            argument = L.Bound 0 (var x)
            -- Close y outside the existing lambda: y has index one in its body.
            scoped = L.close [y] body
            result = L.instantiate [argument] scoped
        case result of
          L.Node T.Lam {} [L.Bound 1 _] -> pure ()
          term -> assertFailure ("the argument was captured: " <> show term)
        L.wellScoped 1 result @?= True
        case export (L.node (lam x (var x)) [result]) of
          T.Lam outer _ (T.Lam inner _ bound _) _ -> do
            outer @?= x
            assertBool "the inner hint must not capture the outer argument" (inner /= outer)
            bound @?= var outer
          expression -> assertFailure ("unexpected instantiated term: " <> show expression),
      testCase "free substitution lifts bound references and keeps free names free" $ do
        let term = L.fromExpr (lam x (T.Tuple [var y, var a]))
            result = L.substituteFree [(y, L.Bound 0 (var x)), (a, L.fromExpr (var x))] term
        case result of
          L.Node T.Lam {} [L.Node T.Tuple {} [L.Bound 1 _, free]] -> free @?= L.fromExpr (var x)
          expression -> assertFailure ("unexpected free substitution: " <> show expression)
        L.wellScoped 1 result @?= True,
      testCase "free substitution is simultaneous" $ do
        let term = L.fromExpr (T.Tuple [var x, var y])
        export (L.substituteFree [(x, L.fromExpr (var y)), (y, L.fromExpr (var a))] term)
          @?= T.Tuple [var y, var a],
      testCase "renaming affects only free occurrences, not indices or binder hints" $ do
        let term = L.fromExpr (lam x (T.Tuple [var x, var y]))
        export (L.renameFree [(x, a), (y, b)] term) @?= lam x (T.Tuple [var x, var b]),
      testCase "conversion retains every source header, including Const occurrences" $ do
        let location column = Just (mkRange (mkPos 1 column) (mkPos 1 (column + 1)))
            binder = Name "x" (location 1)
            occurrence = Name "x" (location 5)
            expression = T.Lam binder intType (T.Const occurrence intType (location 4)) (location 2)
        -- Eq Name intentionally ignores locations, so compare Show as well.
        show (export (L.fromExpr expression)) @?= show expression,
      testCase "scope checking rejects negative and escaped indices" $ do
        L.wellScoped 0 (L.Bound 0 (var x)) @?= False
        L.wellScoped 1 (L.Bound 0 (var x)) @?= True
        L.wellScoped 1 (L.Bound (-1) (var x)) @?= False
        L.wellScoped 0 (L.fromExpr (lam x (var x))) @?= True,
      testCase "holes retain their source metadata without implicit local replacements" $ do
        let hole = T.EHole (T.Hole "body" 3 intType (mkRange (mkPos 1 1) (mkPos 1 2)) mempty)
        case L.fromExpr (lam x hole) of
          L.Node T.Lam {} [body] -> export (L.instantiate [L.fromExpr (var a)] body) @?= hole
          term -> assertFailure ("unexpected hole term: " <> show term),
      testCase "a generated name takes the first unused suffix" $ do
        L.availableName Set.empty "x" @?= "?x_0"
        L.availableName (Set.fromList ["?x_0", "?x_1", "?y_2"]) "x" @?= "?x_2",
      -- (λx. (x, x), λy. (y, y)), where each second occurrence is a free global.
      -- Both binders need fallbacks; neither choice depends on the other.
      testCase "separate fallback names each take the first unused suffix" $ do
        let capturing name = L.node (lam name (T.Tuple [])) [L.node (T.Tuple [var name, var name]) [L.Bound 0 (var name), L.fromExpr (var name)]]
            fallback name = Name ("?" <> nameToText name <> "_0") Nothing
            expected name = lam (fallback name) (T.Tuple [var (fallback name), var name])
        export (L.node (T.Tuple [var x, var y]) [capturing x, capturing y])
          @?= T.Tuple [expected x, expected y]
    ]

export :: L.Term -> T.Expr
export = L.toExpr

intType :: A.Type
intType = A.TBase A.TInt Nothing

x, y, a, b :: Name
x = Name "x" Nothing
y = Name "y" Nothing
a = Name "a" Nothing
b = Name "b" Nothing

var :: Name -> T.Expr
var name = T.Var name intType Nothing

lam :: Name -> T.Expr -> T.Expr
lam name body = T.Lam name intType body Nothing
