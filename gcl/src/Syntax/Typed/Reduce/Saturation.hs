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
--   Everything below 'saturatedRedex' is private implementation: the type of
--   the whole spine comes from 'typeOf', plus small helpers to peel it. Read
--   them only when debugging a mis-marked redex; the contract above is all a
--   caller needs.
module Syntax.Typed.Reduce.Saturation
  ( saturatedRedex,
  )
where

import qualified Syntax.Abstract.Types as A
import Syntax.Common.Types (TypeOp (..))
import Syntax.Typed.Types
import Syntax.Typed.Util (typeOf)

-- | Whether an application spine is a saturated redex: a reducible head (a
--   defined Var or a Lam) applied to enough arguments that the result is no
--   longer a function. Partial (function-typed) applications are not redexes.
saturatedRedex :: Expr -> Bool
saturatedRedex e = isReducibleHead (spineHead e) && arrowArity (typeOf e) == 0

-- | Head of an application spine.
spineHead :: Expr -> Expr
spineHead (App f _ _) = spineHead f
spineHead e = e

-- | Whether the spine head is a function we can unfold/apply.
isReducibleHead :: Expr -> Bool
isReducibleHead (Var {}) = True
isReducibleHead (Lam {}) = True
isReducibleHead _ = False

-- | Number of leading Arrow applications of a type. @0@ means the type is not
--   a function, so an expression of this type is fully applied.
--   arrowArity (Int -> Int -> Int) = 2
--   arrowArity (Int -> Int)        = 1
--   arrowArity Int                 = 0
arrowArity :: A.Type -> Int
arrowArity (A.TApp (A.TApp (A.TOp (Arrow _)) _ _) t2 _) = 1 + arrowArity t2
arrowArity _ = 0
