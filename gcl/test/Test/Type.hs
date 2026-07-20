{-# LANGUAGE OverloadedStrings #-}

module Test.Type (tests) where

import GCL.Range (mkPos, mkRange)
import GCL.Type2.Subst (applySubst)
import GCL.Type2.Types (typeToType)
import qualified Data.Map as Map
import Pretty (toText)
import qualified Syntax.Abstract.Operator as AO
import qualified Syntax.Abstract.Types as A
import Syntax.Common.Types (Name (..), TypeOp (..))
import qualified Syntax.Typed.Operator as TO
import Syntax.Typed.Reduce.Saturation (saturatedRedex)
import qualified Syntax.Typed.Types as T
import Syntax.Typed.Util (codomain, typeOf)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "Type"
    [ testCase "mkArrowType constructs Arrow TApp" $
        assertArrowType (A.mkArrowType intType boolType),
      testCase "tFunc constructs Arrow TApp" $
        assertArrowType (AO.tFunc intType boolType),
      testCase "typeToType uses the canonical Arrow representation" $
        typeToType intType boolType @?= A.mkArrowType intType boolType,
      testCase "Arrow type equality ignores source ranges" $ do
        let range = mkRange (mkPos 1 1) (mkPos 1 3)
            ranged =
              A.TApp
                (A.TApp (A.TOp (Arrow (Just range))) intType (Just range))
                boolType
                (Just range)
        ranged @?= A.mkArrowType intType boolType,
      testCase "Arrow types with different components are unequal" $ do
        A.mkArrowType boolType boolType /= A.mkArrowType intType boolType @? "different argument types"
        A.mkArrowType intType intType /= A.mkArrowType intType boolType @? "different result types",
      testCase "typeOf lambda application returns its result type" $ do
        let x = Name "x" Nothing
            identity = T.Lam x intType (T.Var x intType Nothing) Nothing
            application = T.App identity (T.Lit (A.Num 1) intType Nothing) Nothing
        typeOf application @?= intType,
      testCase "typed operator annotations use nested Arrow applications" $
        TO.tBinIntOp
          @?= A.mkArrowType intType (A.mkArrowType intType intType),
      testCase "saturation distinguishes partial and full applications" $ do
        let f = Name "f" Nothing
            functionType = A.mkArrowType intType (A.mkArrowType intType intType)
            function = T.Var f functionType Nothing
            argument = T.Lit (A.Num 1) intType Nothing
            partial = T.App function argument Nothing
            full = T.App partial argument Nothing
        saturatedRedex partial @?= False
        saturatedRedex full @?= True,
      testCase "function signatures render as arrows" $
        toText (A.mkArrowType intType boolType) @?= "Int → Bool",
      testCase "substitution traverses nested Arrow applications" $ do
        let a = Name "a" Nothing
            polymorphic = A.mkArrowType (A.TVar a Nothing) (A.mkArrowType intType (A.TVar a Nothing))
            expected = A.mkArrowType boolType (A.mkArrowType intType boolType)
        applySubst (Map.singleton a boolType) polymorphic @?= expected,
      testCase "array codomain remains its element type" $ do
        let endpoint = A.Including (A.Lit (A.Num 0) Nothing)
            arrayType = A.TArray (A.Interval endpoint endpoint Nothing) boolType Nothing
        codomain arrayType @?= boolType
    ]
  where
    assertArrowType actual =
      case actual of
        A.TApp (A.TApp (A.TOp (Arrow _)) argument _) result _ -> do
          argument @?= intType
          result @?= boolType
        other -> assertFailure $ "expected Arrow TApp, got: " <> show other

intType :: A.Type
intType = A.TBase A.TInt Nothing

boolType :: A.Type
boolType = A.TBase A.TBool Nothing
