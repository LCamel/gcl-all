{-# LANGUAGE OverloadedStrings #-}

-- | A named-environment oracle independent of the reducer's binding tools.
-- Definitions are evaluated in declaration scope; state tables update globals
-- simultaneously, and lexical binders have their own environment.
module Test.Reduce5Property (tests) where

import Data.List (nub)
import Syntax.Abstract.Operator (tFunc, tInt)
import qualified Syntax.Abstract.Types as A
import Syntax.Common.Types (ArithOp (..), ChainOp (..), Name (..), Op (..))
import qualified Syntax.Typed.Operator as Op
import qualified Syntax.Typed.Reduce5 as Reduce5
import qualified Syntax.Typed.Types as T
import Test.Reduce.Support (reduciblePathsWith)
import Test.Tasty (TestTree, adjustOption, testGroup)
import Test.Tasty.QuickCheck
  ( Gen,
    QuickCheckTests (..),
    chooseInt,
    chooseInteger,
    conjoin,
    counterexample,
    elements,
    forAll,
    frequency,
    oneof,
    property,
    shuffle,
    testProperty,
    vectorOf,
    (.&&.),
    (===),
  )

tests :: TestTree
tests =
  adjustOption (\(QuickCheckTests count) -> QuickCheckTests (max 1000 count)) $
    testGroup
      "Reduce5 semantics"
      [ testProperty "every marked click preserves evaluation" $
          forAll genScenario $ \(Scenario definitions globals expression) ->
            let expected = evaluate definitions globals expression
             in conjoin
                  [ counterexample ("path: " <> show path) $
                      case Reduce5.tryReduceAt definitions expression path of
                        Nothing -> counterexample "marked path failed to reduce" False
                        Just result -> evaluate definitions globals result === expected
                  | path <- reduciblePathsWith Reduce5.redexRT definitions expression
                  ],
        testProperty "random click orders preserve evaluation through intermediate states" $
          forAll genScenario $ \(Scenario definitions globals expression) ->
            let expected = evaluate definitions globals expression
                walk remaining current
                  | remaining <= (0 :: Int) = property True
                  | null paths = property True
                  | otherwise =
                      forAll (elements paths) $ \path ->
                        case Reduce5.tryReduceAt definitions current path of
                          Nothing -> counterexample "marked path failed to reduce" False
                          Just result ->
                            counterexample ("intermediate expression: " <> show current) $
                              (evaluate definitions globals result === expected) .&&. walk (remaining - 1) result
                  where
                    paths = reduciblePathsWith Reduce5.redexRT definitions current
             in walk 12 expression,
        testProperty "full reduction preserves evaluation and reaches a normal form" $
          forAll genScenario $ \(Scenario definitions globals expression) ->
            case Reduce5.reduceAll 1000 definitions expression of
              Left partial -> counterexample ("unexpected exhaustion: " <> show partial) False
              Right result ->
                conjoin
                  [ evaluate definitions globals result === evaluate definitions globals expression,
                    reduciblePathsWith Reduce5.redexRT definitions result === []
                  ],
        testProperty "partial results preserve evaluation at any small budget" $
          forAll genScenario $ \(Scenario definitions globals expression) ->
            forAll (chooseInt (0, 8)) $ \budget ->
              let result = either id id (Reduce5.reduceAll budget definitions expression)
               in evaluate definitions globals result === evaluate definitions globals expression
      ]

data Scenario = Scenario Reduce5.DefnEnv [(Name, Integer)] T.Expr
  deriving (Show)

names :: [Name]
names = map (`Name` Nothing) ["x", "y", "z", "f", "g", "K", "?x_0"]

globalNames :: [Name]
globalNames = take 3 names

-- The definitions form a DAG, so budget exhaustion cannot be due to recursion.
-- A small name pool deliberately creates shadowing and capture opportunities.
genScenario :: Gen Scenario
genScenario = do
  values <- vectorOf 3 (chooseInteger (-2, 2))
  let x = Name "x" Nothing
      y = Name "y" Nothing
      f = Name "f" Nothing
      g = Name "g" Nothing
      k = Name "K" Nothing
  constant <- genExpr 2 [] []
  binary <- genExpr 2 [y, x] [(k, 0)]
  parameter <- elements names
  unary <- genExpr 2 [parameter] [(k, 0), (g, 2)]
  expression <- genExpr 4 [] [(k, 0), (g, 2), (f, 1)]
  pure $ Scenario [(k, constant), (g, lam x (lam y binary)), (f, lam parameter unary)] (zip globalNames values) expression

genExpr :: Int -> [Name] -> [(Name, Int)] -> Gen T.Expr
genExpr depth locals definitions
  | depth <= 0 = leaf
  | otherwise =
      frequency
        [ (3, leaf),
          (2, Op.add <$> sub <*> sub),
          ( 3,
            do
              keys <- take 2 <$> shuffle globalNames
              values <- vectorOf (length keys) sub
              T.Subst <$> sub <*> pure (zip keys values)
          ),
          ( 2,
            do
              binder <- elements names
              scrutinee <- sub
              body <- genExpr (depth - 1) (binder : locals) definitions
              pure (T.Case scrutinee [T.CaseClause (A.PattBinder binder) body] Nothing)
          ),
          ( 2,
            do
              binders <- take 2 <$> shuffle names
              scrutinee <- T.Tuple <$> vectorOf 2 sub
              body <- genExpr (depth - 1) (reverse binders <> locals) definitions
              pure (T.Case scrutinee [T.CaseClause (A.PattTuple (map A.PattBinder binders)) body] Nothing)
          ),
          ( 2,
            do
              binders <- take 2 <$> shuffle names
              body <- genExpr (depth - 1) (reverse binders <> locals) definitions
              let within name = Op.conj (Op.lte (Op.number (-1)) (Op.nameVar name tInt)) (Op.lte (Op.nameVar name tInt) (Op.number 1))
              pure (T.Quant sumOperator [(name, tInt) | name <- binders] (Op.conjunct (map within binders)) body Nothing)
          ),
          (1, T.OutT <$> elements [0, 1] <*> (T.Tuple <$> vectorOf 2 sub)),
          ( 1,
            do
              binder <- elements names
              scrutinee <- sub
              zero <- sub
              other <- genExpr (depth - 1) (binder : locals) definitions
              pure (T.Case scrutinee [T.CaseClause (A.PattLit (A.Num 0)) zero, T.CaseClause (A.PattBinder binder) other] Nothing)
          )
        ]
  where
    -- Branching does not grow the generated trees exponentially.
    sub = genExpr (depth `div` 2) locals definitions
    leaf =
      oneof $
        [ Op.number <$> chooseInt (-2, 2),
          Op.nameVar <$> elements (nub (locals <> globalNames)) <*> pure tInt,
          T.Const <$> elements (nub (locals <> globalNames)) <*> pure tInt <*> pure Nothing
        ]
          <> [ do
                 arguments <- vectorOf arity (genExpr (depth `div` 2) locals [])
                 let callee = Op.nameVar name (foldr (const (tFunc tInt)) tInt arguments)
                 pure (foldl (\function argument -> T.App function argument Nothing) callee arguments)
             | (name, arity) <- definitions,
               name `notElem` locals
             ]

lam :: Name -> T.Expr -> T.Expr
lam name body = T.Lam name tInt body Nothing

sumOperator :: T.Expr
sumOperator = T.Op (ArithOp (Add Nothing)) (tFunc tInt (tFunc tInt tInt))

data Value
  = Number Integer
  | Boolean Bool
  | Tuple [Value]
  | Closure [(Name, Value)] [(Name, Value)] Name T.Expr

evaluate :: Reduce5.DefnEnv -> [(Name, Integer)] -> T.Expr -> Integer
evaluate definitions globals = number . eval [(name, Number value) | (name, value) <- globals] []
  where
    number (Number value) = value
    number _ = error "oracle: expected a number"
    boolean (Boolean value) = value
    boolean _ = error "oracle: expected a boolean"
    eval state locals expression = case expression of
      T.Lit (A.Num value) _ _ -> Number (fromIntegral value)
      T.Lit (A.Bol value) _ _ -> Boolean value
      T.Var name _ _ -> case lookup name locals of
        Just value -> value
        Nothing -> case lookup name definitions of
          Just body -> eval state [] body
          Nothing -> global state name
      T.Const name _ _ -> maybe (global state name) id (lookup name locals)
      T.App (T.App (T.Op (ArithOp (Add _)) _) left _) right _ ->
        Number (number (eval state locals left) + number (eval state locals right))
      T.App (T.App (T.Op (ArithOp (ConjU _)) _) left _) right _ ->
        Boolean (boolean (eval state locals left) && boolean (eval state locals right))
      T.Chain (T.More (T.Pure left) (ChainOp (LTEU _)) _ right) ->
        Boolean (number (eval state locals left) <= number (eval state locals right))
      T.App function argument _ -> case eval state locals function of
        Closure capturedState capturedLocals binder body ->
          eval capturedState ((binder, eval state locals argument) : capturedLocals) body
        _ -> error "oracle: expected a function"
      T.Lam binder _ body _ -> Closure state locals binder body
      T.Tuple expressions -> Tuple (map (eval state locals) expressions)
      T.OutT index subject -> case eval state locals subject of
        Tuple values -> values !! index
        _ -> error "oracle: expected a tuple"
      T.Quant _ binders restriction body _ ->
        Number $
          sum
            [ number (eval state scoped body)
            | assignments <- sequence [[(name, Number value) | value <- [-1 .. 1]] | (name, _) <- binders],
              let scoped = reverse assignments <> locals,
              boolean (eval state scoped restriction)
            ]
      T.Case subject clauses _ -> choose (eval state locals subject) clauses
        where
          choose _ [] = error "oracle: non-exhaustive case"
          choose value (T.CaseClause pattern' body : rest) = case match value pattern' of
            Just assignments -> eval state (reverse assignments <> locals) body
            Nothing -> choose value rest
      T.Subst subject table ->
        let updated = [(name, eval state locals value) | (name, value) <- table]
         in eval (updated <> state) locals subject
      _ -> error ("oracle: unsupported expression " <> show expression)
    global state name = maybe (error ("oracle: unbound name " <> show name)) id (lookup name state)
    match value (A.PattBinder name) = Just [(name, value)]
    match (Number value) (A.PattLit (A.Num expected))
      | value == fromIntegral expected = Just []
      | otherwise = Nothing
    match (Tuple values) (A.PattTuple patterns)
      | length values == length patterns = concat <$> sequence (zipWith match values patterns)
    match _ _ = Nothing
