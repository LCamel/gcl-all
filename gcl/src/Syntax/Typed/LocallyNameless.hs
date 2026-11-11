-- | Binding operations over typed expressions. Bound occurrences use zero-based
-- de Bruijn indices; free occurrences retain their names. Binder names and
-- variable headers are display hints/source metadata, never binding identities.
--
-- Children follow 'pathChildren'. A multi-binder scope is ordered like nested
-- lambdas: its last binder has index zero. Subst keys denote program globals,
-- so a Subst introduces no lexical scope. Holes and their source Envs remain
-- opaque, as in the existing named reducers.
module Syntax.Typed.LocallyNameless
  ( Term (..),
    fromExpr,
    toExpr,
    node,
    header,
    children,
    withChildren,
    scopes,
    freeNames,
    allNames,
    wellScoped,
    shift,
    open,
    close,
    instantiate,
    substituteFree,
    renameFree,
    availableName,
  )
where

import Data.List (elemIndex, (!?))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Syntax.Abstract.Types (extractBinder)
import Syntax.Common.Types (Name (..), nameToText)
import qualified Syntax.Typed.Structure as S
import Syntax.Typed.Types

-- Equality includes the retained source/display headers. It detects structural
-- changes for reduction; it is not an alpha-equivalence test.
data Term
  = Bound Int Expr
  | Node Expr [Term]
  deriving (Eq, Show)

-- | Store each child once. Expr supplies only the constructor, binder names,
-- types and ranges; its child slots contain placeholders. Use this constructor
-- helper when building nodes so equality does not depend on stale child trees.
node :: Expr -> [Term] -> Term
node expression terms
  | length (S.pathChildren expression) == length terms =
      Node (S.withPathChildren expression (map (const (Tuple [])) terms)) terms
  | otherwise = error "LocallyNameless.node: wrong number of children"

header :: Term -> Expr
header (Bound _ expression) = expression
header (Node expression _) = expression

children :: Term -> [Term]
children Bound {} = []
children (Node _ terms) = terms

withChildren :: Term -> [Term] -> Term
withChildren term@Bound {} [] = term
withChildren (Node expression _) terms = node expression terms
withChildren Bound {} _ = error "LocallyNameless.withChildren: bound variable has no children"

scopes :: Term -> [[Name]]
scopes Bound {} = []
scopes (Node expression _) = lexicalScopes expression

lexicalScopes :: Expr -> [[Name]]
lexicalScopes expression@Subst {} = map (const []) (S.pathChildren expression)
lexicalScopes expression = S.childBinders expression

fromExpr :: Expr -> Term
fromExpr = go []
  where
    go scope expression
      | Just name <- variable expression,
        Just index <- elemIndex name scope =
          Bound index expression
      | otherwise =
          node expression $
            zipWith (\names -> go (reverse names <> scope)) (lexicalScopes expression) (S.pathChildren expression)

variable :: Expr -> Maybe Name
variable (Var name _ _) = Just name
variable (Const name _ _) = Just name
variable _ = Nothing

renameOccurrence :: Name -> Expr -> Expr
renameOccurrence name (Var original t range) = Var (rename original) t range
  where
    rename (Name _ location) = Name (nameToText name) location
renameOccurrence name (Const original t range) = Const (rename original) t range
  where
    rename (Name _ location) = Name (nameToText name) location
renameOccurrence _ _ = error "LocallyNameless: bound occurrence is not a variable"

freeNames :: Term -> Set Name
freeNames Bound {} = Set.empty
freeNames (Node expression terms) = maybe Set.empty Set.singleton (variable expression) <> foldMap freeNames terms

allNames :: Term -> Set Text
allNames (Bound _ expression) = S.allNames expression
allNames (Node expression terms) = S.allNames expression <> foldMap allNames terms

-- | Validate a whole term with depth zero, or a detached fragment with the
-- number of surrounding binders. Negative or escaped indices are rejected.
wellScoped :: Int -> Term -> Bool
wellScoped depth (Bound index _) = index >= 0 && index < depth
wellScoped depth term =
  and (zipWith (\names -> wellScoped (depth + length names)) (scopes term) (children term))

-- | Shift references outside a fragment's own binders. A negative shift is
-- valid only when the removed slots are not referenced by that fragment.
shift :: Int -> Int -> Term -> Term
shift amount cutoff (Bound index expression)
  | index >= cutoff = Bound (index + amount) expression
  | otherwise = Bound index expression
shift amount cutoff term =
  withChildren term $
    zipWith (\names -> shift amount (cutoff + length names)) (scopes term) (children term)

-- | Remove one scope, replacing its variables. Values are expressed in the
-- surrounding context, not under the removed scope. Nested scopes lift them.
instantiate :: [Term] -> Term -> Term
instantiate values = removeScope (length values) (\index _ -> reverse values !! index)

-- | Remove a scope using caller-chosen free names, in binder declaration order.
-- Names must be distinct and fresh for the body and its surrounding context.
-- The original occurrence's type and source locations survive opening.
open :: [Name] -> Term -> Term
open names = removeScope (length names) (\index expression -> node (renameOccurrence (reverse names !! index) expression) [])

removeScope :: Int -> (Int -> Expr -> Term) -> Term -> Term
removeScope count replacement = go 0
  where
    go depth term@(Bound index expression)
      | index < depth = term
      | index < depth + count = shift depth 0 (replacement (index - depth) expression)
      | otherwise = Bound (index - count) expression
    go depth term =
      withChildren term $
        zipWith (\names -> go (depth + length names)) (scopes term) (children term)

-- | Add a scope around a fragment, closing the given free names. References
-- to an existing surrounding context shift outwards rather than being captured.
close :: [Name] -> Term -> Term
close names = go 0
  where
    go depth (Bound index expression) = Bound (if index >= depth then index + length names else index) expression
    go depth term@(Node expression _)
      | Just name <- variable expression,
        Just index <- elemIndex name (reverse names) =
          Bound (depth + index) expression
      | otherwise =
          withChildren term $
            zipWith (\binders -> go (depth + length binders)) (scopes term) (children term)

-- | Simultaneous free-variable substitution. Replacements may refer to the
-- surrounding context; descending under binders shifts those references.
-- State-table composition belongs to the reducer, not to this operation.
substituteFree :: [(Name, Term)] -> Term -> Term
substituteFree table = go 0
  where
    go _ term@Bound {} = term
    go depth term@(Node expression _)
      | Just name <- variable expression,
        Just value <- lookup name table =
          shift depth 0 value
      | otherwise =
          withChildren term $
            zipWith (\names -> go (depth + length names)) (scopes term) (children term)

renameFree :: [(Name, Name)] -> Term -> Term
renameFree _ term@Bound {} = term
renameFree renaming term@(Node expression terms)
  | Just name <- variable expression,
    Just target <- lookup name renaming =
      node (renameOccurrence target expression) []
  | otherwise = withChildren term (map (renameFree renaming) terms)

-- | Export a locally closed term. Recover binder hints unless that would
-- capture a free name, obscure a pending state key, or capture a referenced
-- outer binder. Fallback names avoid every name still present in the result.
-- The output depends only on the term, so equal terms always display alike.
toExpr :: Term -> Expr
toExpr term = go [] term
  where
    present = allNames term
    go scope (Bound index expression) = case scope !? index of
      Just name -> renameOccurrence name expression
      Nothing -> error "LocallyNameless.toExpr: escaped bound variable"
    go scope (Node expression terms) = S.withPathChildren renamed (zipWith go childScopes terms)
      where
        (renamed, childScopes) = foldl choose (expression, map (const scope) terms) (scopeGroups expression)
        choose (current, scopesSoFar) (slot, names, positions) =
          let region = [terms !! position | position <- positions]
              outerNames =
                Set.fromList
                  [ name
                  | child <- region,
                    index <- Set.toList (looseBounds child),
                    index >= length names,
                    Just name <- [scope !? (index - length names)]
                  ]
              protected = foldMap visibleNames region <> outerNames
              chosen = allocate protected (present <> Set.fromList (map nameToText scope)) names
              renaming = zip (map nameToText names) (map nameToText chosen)
              scope' = reverse chosen <> scope
           in ( renameHeader slot renaming current,
                [if position `elem` positions then scope' else existing | (position, existing) <- zip [0 ..] scopesSoFar]
              )
        allocate _ _ [] = []
        allocate protected avoid (name : rest) =
          let target
                | Set.member name protected = availableName avoid (nameToText name)
                | otherwise = nameToText name
              chosen = Name target Nothing
           in chosen : allocate (Set.insert chosen protected) (Set.insert target avoid) rest

-- | The first generated name @?prefix_k@, counting k from zero, that is not
-- already taken. The choice depends only on its arguments.
availableName :: Set Text -> Text -> Text
availableName taken prefix = candidate (until (\index -> Set.notMember (candidate index) taken) (+ 1) 0)
  where
    candidate :: Int -> Text
    candidate index = Text.cons '?' prefix <> Text.pack ('_' : show index)

-- Relative indices referring outside this term's own scopes.
looseBounds :: Term -> Set Int
looseBounds = go 0
  where
    go depth (Bound index _)
      | index >= depth = Set.singleton (index - depth)
      | otherwise = Set.empty
    go depth term = Set.unions (zipWith (\names -> go (depth + length names)) (scopes term) (children term))

visibleNames :: Term -> Set Name
visibleNames Bound {} = Set.empty
visibleNames (Node expression terms) = keys <> maybe Set.empty Set.singleton (variable expression) <> foldMap visibleNames terms
  where
    keys = case expression of
      Subst _ table -> Set.fromList (map fst table)
      _ -> Set.empty

scopeGroups :: Expr -> [(Int, [Name], [Int])]
scopeGroups (Lam name _ _ _) = [(0, [name], [0])]
scopeGroups (Quant _ binders _ _ _) = [(1, map fst binders, [1, 2])]
scopeGroups (Case _ clauses _) = [(index, extractBinder pattern', [index]) | (index, CaseClause pattern' _) <- zip [1 ..] clauses]
scopeGroups _ = []

renameHeader :: Int -> [(Text, Text)] -> Expr -> Expr
renameHeader _ renaming (Lam name t body range) = Lam (S.renameName renaming name) t body range
renameHeader _ renaming (Quant op binders restriction body range) =
  Quant op [(S.renameName renaming name, t) | (name, t) <- binders] restriction body range
renameHeader index renaming (Case scrutinee clauses range) =
  Case scrutinee [if position == index then CaseClause (S.renamePatternBinders renaming pattern') body else clause | (position, clause@(CaseClause pattern' body)) <- zip [1 ..] clauses] range
renameHeader _ _ expression = expression
