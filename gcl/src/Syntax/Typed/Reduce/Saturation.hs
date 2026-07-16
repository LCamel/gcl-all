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
--   Everything below 'saturatedRedex' is private implementation: a
--   type-deriver ('exprType') for the well-typed AST received by this module,
--   plus small helpers to peel it. Read them only when debugging a mis-marked
--   redex; the contract above is all a caller needs.
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
--   being a function (@0@ = "already a non-function value").
--   exprArrows (add) = 2
--   exprArrows (add 2) = 1
--   exprArrows (add 2 3) = 0
exprArrows :: Expr -> Int
exprArrows = arrowArity . exprType

-- | Number of leading function arrows of a type (handles both the TFunc and
--   the Arrow-application encodings that show up on typed nodes).
--   arrowArity (Int -> Int -> Int) = 2
--   arrowArity (Int -> Int)        = 1
--   arrowArity Int                 = 0
arrowArity :: A.Type -> Int
arrowArity (A.TFunc _ t2 _) = 1 + arrowArity t2
arrowArity (A.TApp (A.TApp (A.TOp (Arrow _)) _ _) t2 _) = 1 + arrowArity t2
arrowArity _ = 0

-- | Codomain of a function/array type. Arrays are @Int -> element@, and a
--   function type appears either as @TFunc@ or as the Arrow-application form
--   inference produces -- all three peel one argument. Receiving any other
--   type here violates the typed-AST invariant.
--   codomain (Int -> Bool)       = Bool   -- TFunc or Arrow-app encoding
--   codomain (Array Int of Bool) = Bool   -- TArray
codomain :: A.Type -> A.Type
codomain (A.TFunc _ t _) = t
codomain (A.TApp (A.TApp (A.TOp (Arrow _)) _ _) t _) = t
codomain (A.TArray _ t _) = t
codomain _ = error "codomain: expected a function or array type in a typed expression"

-- | i-th component of a tuple type.
component :: Int -> A.Type -> A.Type
component i (A.TTuple ts)
  | 0 <= i && i < length ts = ts !! i
  | otherwise = error "component: tuple index out of bounds in a typed expression"
component _ _ = error "component: expected a tuple type in a typed expression"

-- | An expression's type, reconstructed from a well-typed AST. Deriving the
--   real type -- rather than counting arrows structurally -- is what makes
--   projections correct at any nesting depth: @a[i][j]@ peels @codomain@
--   twice, so an @array of array of (Int -> Int)@ still reports a function.
--   A shape for which no type can be reconstructed is an internal invariant
--   violation, not a normal result of querying a typed expression.
exprType :: Expr -> A.Type
exprType (Lit _ ty _) = ty
exprType (Var _ ty _) = ty
exprType (Const _ ty _) = ty
exprType (Op _ ty) = ty
exprType (EHole (Hole _ _ ty _ _)) = ty
exprType (Lam _ t b _) =
  A.TApp (A.TApp (A.TOp (Arrow Nothing)) t Nothing) (exprType b) Nothing
exprType (App f _ _) = codomain (exprType f)
exprType (ArrIdx arr _ _) = codomain (exprType arr)
exprType (OutT i e) = component i (exprType e)
exprType (Subst e _) = exprType e
exprType (Quant _ _ _ b _) = exprType b
exprType (Case _ (CaseClause _ b : _) _) = exprType b
exprType (Case _ [] _) = error "exprType: empty case in a typed expression"
exprType (ArrUpd arr _ _ _) = exprType arr
exprType (Tuple es) = A.TTuple (map exprType es)
exprType (Chain _) = A.TBase A.TBool Nothing
