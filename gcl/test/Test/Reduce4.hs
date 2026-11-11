module Test.Reduce4 (tests) where

import qualified Syntax.Typed.Reduce4 as Reduce4
import qualified Test.Reduce.Contract as Contract
import Test.Tasty (TestTree)

tests :: TestTree
tests = Contract.tests "Reduce4" Reduce4.tryReduceAt Reduce4.redexRT Reduce4.reduceAll
