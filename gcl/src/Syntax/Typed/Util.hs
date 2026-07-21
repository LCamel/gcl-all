{-# LANGUAGE OverloadedStrings #-}

module Syntax.Typed.Util where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T
import GCL.Range (MaybeRanged (..), (<--->))
import Syntax.Abstract.Types (Type)
import qualified Syntax.Abstract.Types as A
import Syntax.Common (Name (..), nameToText)
import Syntax.Common.Types (TypeOp (..))
import Syntax.Typed

getGuards :: [GdCmd] -> [Expr]
getGuards = fst . unzipGdCmds

unzipGdCmds :: [GdCmd] -> ([Expr], [[Stmt]])
unzipGdCmds = unzip . map (\(GdCmd x y _) -> (x, y))

wrapLam :: [(Name, Type)] -> Expr -> Expr
wrapLam [] body = body
wrapLam ((x, t) : xs) body = let b = wrapLam xs body in Lam x t b (maybeRangeOf x <---> maybeRangeOf b)

declaredNames :: [Declaration] -> [Name]
declaredNames decls = concat . map extractNames $ decls
  where
    extractNames (ConstDecl ns _ _ _) = ns
    extractNames (VarDecl ns _ _ _) = ns

declaredNamesTypes :: [Declaration] -> [(Name, Type)]
declaredNamesTypes decls = concat . map extractNames $ decls
  where
    extractNames (ConstDecl ns t _ _) = [(n, t) | n <- ns]
    extractNames (VarDecl ns t _ _) = [(n, t) | n <- ns]

-- | An expression's type, reconstructed from a well-typed AST. Deriving the
--   real type -- rather than reading a stored annotation -- is what makes
--   projections correct at any nesting depth: @a[i][j]@ peels 'codomain'
--   twice, so an @array of array of (Int -> Int)@ still reports a function.
--   A shape for which no type can be reconstructed is an internal invariant
--   violation, not a normal result of querying a typed expression.
typeOf :: Expr -> Type
typeOf (Lit _ t _) = t
typeOf (Var _ t _) = t
typeOf (Const _ t _) = t
typeOf (Op _ t) = t
-- A type-checked chain always has 'More' at its root; 'Pure' appears only as
-- the leftmost seed nested inside it. A complete chain therefore has type Bool.
typeOf (Chain _) = A.TBase A.TBool Nothing
typeOf (App f _ _) = codomain (typeOf f)
typeOf (Lam _ t e _) =
  A.TApp (A.TApp (A.TOp (Arrow Nothing)) t Nothing) (typeOf e) Nothing
typeOf (Tuple es) = A.TTuple (map typeOf es)
typeOf (OutT i e) = component i (typeOf e)
typeOf (Quant _ _ _ body _) = typeOf body
typeOf (ArrIdx arr _ _) = codomain (typeOf arr)
typeOf (ArrUpd arr _ _ _) = typeOf arr
typeOf (Case _ [] _) = error "typeOf: empty case in a typed expression"
typeOf (Case _ (CaseClause _ e : _) _) = typeOf e
typeOf (Subst e _) = typeOf e
typeOf (EHole h) = typeOfHole h

-- | Codomain of a function/array type. Arrays are @Int -> element@, and a
--   function type appears either as @TFunc@ or as the Arrow-application form
--   inference produces -- all three peel one argument. Receiving any other
--   type here violates the typed-AST invariant.
--   codomain (Int -> Bool)       = Bool   -- TFunc or Arrow-app encoding
--   codomain (Array Int of Bool) = Bool   -- TArray
codomain :: Type -> Type
codomain (A.TFunc _ t _) = t
codomain (A.TApp (A.TApp (A.TOp (Arrow _)) _ _) t _) = t
codomain (A.TArray _ t _) = t
codomain _ = error "codomain: expected a function or array type in a typed expression"

-- | i-th component of a tuple type.
component :: Int -> Type -> Type
component i (A.TTuple ts)
  | 0 <= i && i < length ts = ts !! i
  | otherwise = error "component: tuple index out of bounds in a typed expression"
component _ _ = error "component: expected a tuple type in a typed expression"

typeOfHole :: Hole -> Type
typeOfHole (Hole _ _ t _ _) = t

programToScopeForSubstitution :: Program -> Map Text (Maybe Expr)
programToScopeForSubstitution (Program defns decls _ _ _) =
  Map.mapKeys nameToText $
    foldMap extractDeclaration decls
      <> Map.fromList (extractDefinition defns)
  where
    extractDeclaration :: Declaration -> Map Name (Maybe Expr)
    extractDeclaration (ConstDecl names _ _ _) =
      Map.fromList (zip names (repeat Nothing))
    extractDeclaration (VarDecl names _ _ _) =
      Map.fromList (zip names (repeat Nothing))

    extractDefinition :: [Definition] -> [(Name, Maybe Expr)]
    extractDefinition [] = []
    extractDefinition (TypeDefn _ _ _ _ : ds) =
      extractDefinition ds
    extractDefinition (ValDefn n _ e : ds) =
      (n, Just e) : extractDefinition ds

syntaxSubst :: [Name] -> [Expr] -> Expr -> Expr
syntaxSubst xs es e = Subst e (zip xs es)

{-
  Since we allow holes in the LHS of assignments:

    { }₀ := e

  the induced substitution might have a hole as a denominator.
  However, substitutions are currently represented by [(Name, Expr)]
  where Names is just Text with a location.

  The hack below simply "prints" the hole into a piece of Text,
  e.g, a Text containing "{ }₀",and stores it into the substitution.

  The substitution certainly will not function correctly when an
  EHole representing { }₀ appears in an expression. However, this is
  probably okay for now, since { }₀ does not have a name, cannot
  be referred, and therefore probably won't appear in any pre/post
  conditions. Fix this if it turns out to be otherwise.
-}

syntaxSubst' :: [Either Name Hole] -> [Expr] -> Expr -> Expr
syntaxSubst' xs es e = Subst e (zip (map nameOf xs) es)

nameOf :: Either Name Hole -> Name
nameOf = either id holeToName

holeToName :: Hole -> Name
holeToName hole@(Hole _ _ _ r _) = Name (T.pack $ renderHole hole) (Just r)
  where
    renderHole (Hole _ holeNumber _ _ _) = "{! !}" ++ subscriptNumber holeNumber

    subscriptNumber :: Int -> String
    subscriptNumber = map digitToSubscript . show

    digitToSubscript :: Char -> Char
    digitToSubscript '0' = '₀'
    digitToSubscript '1' = '₁'
    digitToSubscript '2' = '₂'
    digitToSubscript '3' = '₃'
    digitToSubscript '4' = '₄'
    digitToSubscript '5' = '₅'
    digitToSubscript '6' = '₆'
    digitToSubscript '7' = '₇'
    digitToSubscript '8' = '₈'
    digitToSubscript '9' = '₉'
    digitToSubscript c = c
