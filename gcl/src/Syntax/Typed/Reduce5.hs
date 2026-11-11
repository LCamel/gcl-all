-- | One-click and bounded full reduction using locally nameless terms.
-- The public AST, paths and lambda-free click contract are unchanged. Lexical
-- binders use indices internally; globals and state-table keys retain names.
-- Definitions remain opaque until clicked, without dependency analysis.
-- Holes retain pending global updates, but local hole environments are not
-- recorded: this deliberately has the same limitation as Reduce4.
-- Generated names take the first unused suffix rather than a counter, so a
-- result's display depends only on that result.
module Syntax.Typed.Reduce5
  ( DefnEnv,
    RedexPath,
    RTree (..),
    RT,
    tryReduceAt,
    reduceAll,
    redexRT,
  )
where

import Data.Bifunctor (bimap)
import Data.List ((!?))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Syntax.Abstract.Types (Pattern (..))
import Syntax.Common.Types (Name (..), nameToText)
import qualified Syntax.Typed.LocallyNameless as L
import Syntax.Typed.Structure (RT, RTree (..), RedexPath, replaceAt)
import Syntax.Typed.Types

type DefnEnv = [(Name, Expr)]

type Substitution = [(Name, L.Term)]

-- Opened slots avoid the definitions and the expression being reduced.
data Context = Context
  { bodies :: Map Name L.Term,
    definitionNames :: Set Text,
    reserved :: Set Text
  }

-- Immediate parent first. Terms at a selection may refer to these ancestors.
type Frame = (Int, L.Term)

compile :: DefnEnv -> Expr -> (Context, L.Term)
compile env expression = (reserving (Context compiled names Set.empty) term, term)
  where
    compiled = Map.fromList [(name, L.fromExpr body) | (name, body) <- env]
    term = L.fromExpr expression
    names = foldMap L.allNames compiled <> Set.fromList (map (nameToText . fst) env)

reserving :: Context -> L.Term -> Context
reserving context term = context {reserved = definitionNames context <> L.allNames term}

tryReduceAt :: DefnEnv -> Expr -> RedexPath -> Maybe Expr
tryReduceAt env expression path = do
  let (context, term) = compile env expression
  (selected, frames) <- focus term path
  reduceFocused context expression selected frames

-- | Root-first path order, counting successful clicks, including self-unfolds.
-- Left returns the partial result at the budget; Right has no clickable redex.
-- Keep indices throughout the run and choose display names only once at the end.
-- Each step reserves the names of its own input, including slots still pending.
reduceAll :: Int -> DefnEnv -> Expr -> Either Expr Expr
reduceAll limit env expression = bimap L.toExpr L.toExpr (go limit term)
  where
    (context, term) = compile env expression
    go remaining current = case reduceOnce (reserving context current) current of
      Nothing -> Right current
      Just result
        | remaining <= 0 -> Left current
        | otherwise -> go (remaining - 1) result

reduceOnce :: Context -> L.Term -> Maybe L.Term
reduceOnce context expression = search [(expression, [])]
  where
    search [] = Nothing
    search ((selected, frames) : pending) = case stepFocused context selected frames of
      Just same | isState selected && same == expression -> deeper
      Just result -> Just result
      Nothing -> deeper
      where
        deeper = search ([(child, (index, selected) : frames) | (index, child) <- zip [0 ..] (L.children selected)] <> pending)

redexRT :: DefnEnv -> Expr -> RT
redexRT env expression = go [] term
  where
    (context, term) = compile env expression
    go frames selected =
      Node
        (isJust (reduceFocused context expression selected frames))
        [go ((index, selected) : frames) child | (index, child) <- zip [0 ..] (L.children selected)]

reduceFocused :: Context -> Expr -> L.Term -> [Frame] -> Maybe Expr
reduceFocused context original selected frames = case L.toExpr <$> stepFocused context selected frames of
  Just result | isState selected && result == original -> Nothing
  result -> result

stepFocused :: Context -> L.Term -> [Frame] -> Maybe L.Term
stepFocused context selected frames = case selected of
  L.Node (Var name _ _) []
    | Just body <- definition context (hiddenDefinitions frames) name -> repair context body frames
  _ -> flip rebuild frames <$> localStep context (hiddenDefinitions frames) selected

repair :: Context -> L.Term -> [Frame] -> Maybe L.Term
-- Consume interposed state before beta, including defensive ASTs with a Subst
-- already over a lambda. A pending state over a reference or hole stays visible.
repair context replacement frames
  | Just (subject, table) <- stateTable replacement,
    leadingLambda subject =
      repair context (applyState context (hiddenDefinitions frames <> domain table) table subject) frames
repair context replacement ((0, parent) : frames)
  | Just (_, table) <- stateTable parent,
    leadingLambda replacement =
      repair context (applyState context (hiddenDefinitions frames <> domain table) table replacement) frames
repair context (L.Node (Lam name _ _ _) [body]) ((0, L.Node (App _ _ _) [_, argument]) : frames) =
  repair context (bindLocals context (hiddenDefinitions frames) [(name, argument)] body) frames
repair _ (L.Node Lam {} _) _ = Nothing
repair _ replacement frames = Just (rebuild replacement frames)

leadingLambda :: L.Term -> Bool
leadingLambda (L.Node Lam {} _) = True
leadingLambda expression = maybe False (leadingLambda . fst) (stateTable expression)

focus :: L.Term -> RedexPath -> Maybe (L.Term, [Frame])
focus expression [] = Just (expression, [])
focus expression (index : rest) = do
  child <- L.children expression !? index
  (selected, frames) <- focus child rest
  pure (selected, frames <> [(index, expression)])

rebuild :: L.Term -> [Frame] -> L.Term
rebuild = foldl plug
  where
    plug replacement (index, parent) = case replaceAt index replacement (L.children parent) of
      Just terms -> L.withChildren parent terms
      Nothing -> error "Reduce5: invalid saved frame"

stateTable :: L.Term -> Maybe (L.Term, Substitution)
stateTable (L.Node (Subst _ table) (subject : values)) = Just (subject, zip (map fst table) values)
stateTable _ = Nothing

isState :: L.Term -> Bool
isState = isJust . stateTable

pendingState :: L.Term -> Substitution -> L.Term
pendingState subject table = L.node (Subst (Tuple []) [(key, Tuple []) | (key, _) <- table]) (subject : map snd table)

hiddenDefinitions :: [Frame] -> Set Name
hiddenDefinitions frames = Set.unions [domain table | (0, parent) <- frames, Just (_, table) <- [stateTable parent]]

definition :: Context -> Set Name -> Name -> Maybe L.Term
definition context hidden name
  | Set.member name hidden = Nothing
  | otherwise = Map.lookup name (bodies context)

localStep :: Context -> Set Name -> L.Term -> Maybe L.Term
localStep _ _ (L.Node (OutT index _) [L.Node Tuple {} elements]) = elements !? index
localStep context hidden expression
  | Just (subject, table) <- stateTable expression = Just (applyState context (hidden <> domain table) table subject)
localStep context hidden (L.Node (Case _ clauses _) (scrutinee : terms)) = choose (zip clauses terms)
  where
    choose [] = Nothing
    choose ((CaseClause pattern' _, body) : rest) = case match scrutinee pattern' of
      Matched assignments -> Just (bindLocals context hidden assignments body)
      Refuted -> choose rest
      Undecided -> Nothing
localStep _ _ _ = Nothing

data Match = Matched Substitution | Refuted | Undecided

match :: L.Term -> Pattern -> Match
match expression (PattBinder name) = Matched [(name, expression)]
match _ (PattWildcard _) = Matched []
match (L.Node (Lit literal _ _) []) (PattLit expected)
  | literal == expected = Matched []
  | otherwise = Refuted
match _ (PattLit _) = Undecided
match (L.Node Tuple {} elements) (PattTuple patterns)
  | length elements == length patterns = foldr combine (Matched []) (zipWith match elements patterns)
  | otherwise = Refuted
match (L.Node Lit {} []) (PattTuple _) = Refuted
match _ (PattTuple _) = Undecided
match _ (PattConstructor _ _) = Undecided

combine :: Match -> Match -> Match
combine (Matched left) (Matched right) = Matched (left <> right)
combine Refuted _ = Refuted
combine _ Refuted = Refuted
combine Undecided _ = Undecided
combine _ Undecided = Undecided

domain :: Substitution -> Set Name
domain = Set.fromList . map fst

shiftTable :: Int -> Substitution -> Substitution
shiftTable depth = map (\(key, value) -> (key, L.shift depth 0 value))

-- State tables affect free program variables only. Entering a lexical scope
-- shifts outer-bound references in their values, without changing global keys.
applyState :: Context -> Set Name -> Substitution -> L.Term -> L.Term
applyState _ _ [] expression = expression
applyState context hidden table expression
  | opaque expression = case filter (not . identityEntry context hidden) table of
      [] -> expression
      entries -> pendingState expression entries
  where
    opaque (L.Node (Var name _ _) []) = isJust (definition context hidden name)
    opaque (L.Node EHole {} []) = True
    opaque _ = False
applyState _ _ table expression@(L.Node (Var name _ _) []) = maybe expression id (lookup name table)
applyState _ _ table expression@(L.Node (Const name _ _) []) = maybe expression id (lookup name table)
applyState context hidden table expression
  | Just (subject, earlier) <- stateTable expression =
      let values = [(key, applyState context hidden table value) | (key, value) <- earlier]
          remaining =
            [ entry
            | entry@(key, _) <- table,
              Set.notMember key (domain earlier),
              mayReadState context (hidden <> domain earlier) key subject
            ]
       in pendingState subject (values <> remaining)
applyState context hidden table expression =
  L.withChildren
    expression
    [applyState context hidden (shiftTable (length names) table) child | (names, child) <- zip (L.scopes expression) (L.children expression)]

identityEntry :: Context -> Set Name -> (Name, L.Term) -> Bool
identityEntry context hidden (key, L.Node (Var name _ _) []) = key == name && not (isJust (definition context hidden name))
identityEntry _ _ (key, L.Node (Const name _ _) []) = key == name
identityEntry _ _ _ = False

mayReadState :: Context -> Set Name -> Name -> L.Term -> Bool
mayReadState context hidden key (L.Node (Var name _ _) []) = isJust (definition context hidden name) || name == key
mayReadState _ _ key (L.Node (Const name _ _) []) = name == key
mayReadState _ _ _ (L.Node EHole {} []) = True
mayReadState context hidden key expression
  | Just (subject, table) <- stateTable expression =
      let hidden' = hidden <> domain table
       in (Set.notMember key (domain table) && mayReadState context hidden' key subject)
            || any (\(target, value) -> mayReadState context hidden' target subject && mayReadState context hidden key value) table
mayReadState context hidden key expression = any (mayReadState context hidden key) (L.children expression)

-- Open only the scope being consumed, not every binder in the expression.
-- Fresh free slots let lexical substitution defer an argument across a state
-- boundary. Ordinary nested binders continue to be represented by indices.
bindLocals :: Context -> Set Name -> Substitution -> L.Term -> L.Term
bindLocals context hidden assignments body =
  replaceLocals context hidden (zip names (map snd assignments)) (L.open names body)
  where
    names = allocate (reserved context <> L.allNames body <> foldMap (L.allNames . snd) assignments) (map fst assignments)
    allocate _ [] = []
    allocate avoid (name : rest) =
      let target = L.availableName avoid (nameToText name)
       in Name target Nothing : allocate (Set.insert target avoid) rest

-- The opened names are already fresh for every table in the body. If a caller
-- value would be changed by an existing state boundary, leave its free slot in
-- the subject and put the value in that table instead of substituting it there.
replaceLocals :: Context -> Set Name -> Substitution -> L.Term -> L.Term
replaceLocals _ _ [] expression = expression
replaceLocals _ _ table expression@(L.Node (Var name _ _) []) = maybe expression id (lookup name table)
replaceLocals _ _ table expression@(L.Node (Const name _ _) []) = maybe expression id (lookup name table)
replaceLocals context hidden table expression
  | Just (subject, earlier) <- stateTable expression =
      let active = [(key, value) | (key, value) <- table, Set.member key (L.freeNames subject)]
          exposed value key = Set.member key (L.freeNames value <> stateKeys value) || mayReadState context hidden key value
          delayed = [(key, value) | (key, value) <- active, any (exposed value . fst) earlier]
          immediate = [(key, value) | (key, value) <- table, Set.notMember key (domain delayed)]
          subject' = replaceLocals context (hidden <> domain earlier) immediate subject
          values = [(key, replaceLocals context hidden table value) | (key, value) <- earlier]
       in pendingState subject' (values <> delayed)
replaceLocals context hidden table expression =
  L.withChildren
    expression
    [replaceLocals context hidden (shiftTable (length names) table) child | (names, child) <- zip (L.scopes expression) (L.children expression)]

stateKeys :: L.Term -> Set Name
stateKeys expression = maybe Set.empty (domain . snd) (stateTable expression) <> foldMap stateKeys (L.children expression)
