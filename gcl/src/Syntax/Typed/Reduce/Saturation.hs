-- | Deciding whether an application spine is a "saturated redex" -- the sole
--   judgement 'redexRT_sat' needs from this module.
--
--   __Contract.__ Given an expression that is an application spine, is it a
--   redex the UI should mark as clickable? Yes exactly when its head is a
--   reducible function (a defined 'Var' or a 'Lam') that has been applied to
--   enough arguments that its own result is no longer a function. Partial
--   applications (still function-typed) stay unmarked.
--
--   Assuming @add : Int -> Int -> Int@:
--
--   > add 2 3   result Int         => True    -- saturated, clickable
--   > add 2     result Int -> Int  => False   -- partial application
--   > 2 + 3     head is an Op       => False   -- arithmetic, left to the solver
--
--   Everything below 'saturatedRedex' is private implementation: a total
--   type-deriver ('exprType') that never faults the way the library's partial
--   @typeOf@ does, plus small helpers to peel it. Read them only when debugging
--   a mis-marked redex; the contract above is all a caller needs.
module Syntax.Typed.Reduce.Saturation
  ( saturatedRedex,
  )
where

import qualified Syntax.Abstract.Types as A
import Syntax.Common.Types (TypeOp (..))
import Syntax.Typed.Types

-- | Whether an application spine is a saturated redex: a reducible head (a
--   defined Var or a Lam) applied to enough arguments that the result is no
--   longer a function. Partial (function-typed) applications are not redexes.
saturatedRedex :: Expr -> Bool
saturatedRedex e = isReducibleHead (spineHead e) && exprArrows e == 0

-- | Head of an application spine.
spineHead :: Expr -> Expr
spineHead (App f _ _) = spineHead f
spineHead e = e

-- | Whether the spine head is a function we can unfold/apply.
isReducibleHead :: Expr -> Bool
isReducibleHead (Var {}) = True
isReducibleHead (Lam {}) = True
isReducibleHead _ = False

-- | Number of arguments an expression can still take before its result stops
--   being a function (@0@ = "already a non-function value"). An underivable
--   type counts as a non-function.
exprArrows :: Expr -> Int
exprArrows = maybe 0 arrowArity . exprType

-- | Number of leading function arrows of a type (handles both the TFunc and
--   the Arrow-application encodings that show up on typed nodes).
arrowArity :: A.Type -> Int
arrowArity (A.TFunc _ t2 _) = 1 + arrowArity t2
arrowArity (A.TApp (A.TApp (A.TOp (Arrow _)) _ _) t2 _) = 1 + arrowArity t2
arrowArity _ = 0

-- | Codomain of a function/array type. Arrays are @Int -> element@, and a
--   function type appears either as @TFunc@ or as the Arrow-application form
--   inference produces -- all three peel one argument. @Nothing@ if the type is
--   neither.
codomain :: A.Type -> Maybe A.Type
codomain (A.TFunc _ t _) = Just t
codomain (A.TApp (A.TApp (A.TOp (Arrow _)) _ _) t _) = Just t
codomain (A.TArray _ t _) = Just t
codomain _ = Nothing

-- | i-th component of a tuple type.
component :: Int -> A.Type -> Maybe A.Type
component i (A.TTuple ts) | i < length ts = Just (ts !! i)
component _ _ = Nothing

-- | An expression's own type, computed totally so it never faults like the
--   library's partial @typeOf@ (which rejects both @App (Lam ..) _@ and the
--   Arrow-application encoding of functions-as-arrays). Deriving the real type
--   -- rather than counting arrows structurally -- is what makes projections
--   correct at any nesting depth: @a[i][j]@ peels @codomain@ twice, so an
--   @array of array of (Int -> Int)@ still reports a function. @Nothing@ only
--   for genuinely underivable types, which do not arise in well-typed input.
exprType :: Expr -> Maybe A.Type
exprType (Lit _ ty _) = Just ty
exprType (Var _ ty _) = Just ty
exprType (Const _ ty _) = Just ty
exprType (Op _ ty) = Just ty
exprType (EHole (Hole _ _ ty _ _)) = Just ty
exprType (Lam _ t b _) = (\r -> A.TFunc t r Nothing) <$> exprType b
exprType (App f _ _) = codomain =<< exprType f
exprType (ArrIdx arr _ _) = codomain =<< exprType arr
exprType (OutT i e) = component i =<< exprType e
exprType (Subst e _) = exprType e
exprType (Quant _ _ _ b _) = exprType b
exprType (Case _ (CaseClause _ b : _) _) = exprType b
exprType (Case _ [] _) = Nothing
exprType (ArrUpd arr _ _ _) = exprType arr
exprType (Tuple es) = A.TTuple <$> traverse exprType es
exprType (Chain _) = Just (A.TBase A.TBool Nothing)
