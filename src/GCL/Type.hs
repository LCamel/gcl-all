{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module GCL.Type where

import           Control.Monad.Except
import           Control.Monad.State.Lazy
import           Control.Monad.Writer.Lazy
import           Data.Aeson                     ( ToJSON )
import           Data.Bifunctor                 ( Bifunctor (second) )
import           Data.Functor
import           Data.Maybe                     ( fromJust )
import qualified Data.Ord                      as Ord
import           Data.List
import           Data.Loc                       ( (<-->)
                                                , Loc(..)
                                                , Located
                                                , locOf
                                                )
import           Data.Foldable                  ( foldlM )
import qualified Data.Set                      as Set
import qualified Data.Map                      as Map
import qualified Data.Text                     as Text
import           GCL.Common
import           GHC.Generics                   ( Generic )
import           Prelude                 hiding ( EQ
                                                , GT
                                                , LT
                                                )

import           Syntax.Abstract
import           Syntax.Abstract.Util
import           Syntax.Common
import qualified Syntax.Typed                  as Typed

data TypeError
    = NotInScope Name
    | UnifyFailed Type Type Loc
    | KindUnifyFailed Kind Kind Loc -- TODO: Deal with this replication in a better way.
    | RecursiveType Name Type Loc
    | AssignToConst Name
    | UndefinedType Name
    | DuplicatedIdentifiers [Name]
    | RedundantNames [Name]
    | RedundantExprs [Expr]
    | MissingArguments [Name]
    deriving (Show, Eq, Generic)

instance ToJSON TypeError

instance Located TypeError where
  locOf (NotInScope n               ) = locOf n
  locOf (UnifyFailed _ _ l          ) = l
  locOf (KindUnifyFailed _ _ l      ) = l
  locOf (RecursiveType _ _ l        ) = l
  locOf (AssignToConst         n    ) = locOf n
  locOf (UndefinedType         n    ) = locOf n
  locOf (DuplicatedIdentifiers ns   ) = locOf ns
  locOf (RedundantNames        ns   ) = locOf ns
  locOf (RedundantExprs        exprs) = locOf exprs
  locOf (MissingArguments      ns   ) = locOf ns

data TypeInfo =
    TypeDefnCtorInfo Type
    | ConstTypeInfo Type
    | VarTypeInfo Type
    deriving (Eq, Show)

instance Substitutable (Subs Type) TypeInfo where
  subst s (TypeDefnCtorInfo t) = TypeDefnCtorInfo (subst s t)
  subst s (ConstTypeInfo    t) = ConstTypeInfo (subst s t)
  subst s (VarTypeInfo      t) = VarTypeInfo (subst s t)

duplicationCheck :: (MonadError TypeError m) => [Name] -> m ()
duplicationCheck ns =
  let ds = map head . filter ((> 1) . length) . groupBy (\(Name text1 _)(Name text2 _) -> text1 == text2) $ ns
  in  if null ds
        then return ()
        else throwError . DuplicatedIdentifiers $ ds

--------------------------------------------------------------------------------
-- The elaboration monad

type ElaboratorM = StateT (FreshState, [(Index, Kind)], [(Index, TypeInfo)]) (Except TypeError)

instance Counterous ElaboratorM where
  countUp = do
    (count, typeDefnInfo, typeInfo) <- get
    put (succ count, typeDefnInfo, typeInfo)
    return count

runElaboration
  :: Elab a => a -> Either TypeError (Typed a)
runElaboration a = do
  ((_, elaborated, _), _state) <- runExcept (runStateT (elaborate a mempty) (0, mempty, mempty))
  Right elaborated

--------------------------------------------------------------------------------
-- Collecting ids
-- The ids are collected by `CollectIds` into the state wrapped by `ElaboratorM`.
-- `collectIds` are thus called in the beginning of elaborating the whole program.

class CollectIds a where
    collectIds :: a -> ElaboratorM ()

{-
instance CollectIds a => CollectIds [a] where
  collectIds xs = mapM_ collectIds xs
-}


-- Currently (and hopefully in the future), we only modify the state of `ElaboratorM` during `collectIds`.

instance CollectIds [Definition] where
  collectIds defns = do
    -- First, we split variants of definitions because different kinds of definitions need to be processed differently.
    let (typeDefns, funcSigs, funcDefns) = split defns
    -- Check if there are duplications of definitions.
    -- While checking signatures and function definitions, we take account of the names of (term) constructors.
    duplicationCheck $ (\(TypeDefn name _ _ _) -> name) <$> typeDefns
    duplicationCheck $ ((\(FuncDefnSig name _ _ _) -> name) <$> funcSigs) <> gatherCtorNames typeDefns
    duplicationCheck $ ((\(FuncDefn name _) -> name) <$> funcDefns) <> gatherCtorNames typeDefns
    -- Gather the type definitions.
    -- Type definitions are collected first because signatures and function definitions may depend on them.
    collectTypeDefns typeDefns
    -- Add signatures into the state one by one.
    collectFuncSigs funcSigs
    -- Get the original explicit signatures.
    -- We will try to restrict polymorphic functions to the types of the corresponding signatures.
    (_, _, infos) <- get
    let sigEnv = second typeInfoToType <$> infos
    -- Give each function definition a fresh name.
    let defined = concatMap (\case
                                (FuncDefn name _exprs) -> [Index name]
                                _ -> []
                            ) defns
    freshVars <- replicateM (length defined) freshVar
    let gathered = second ConstTypeInfo <$> zip defined freshVars
    modify (\(freshState, typeDefnInfos, origInfos) -> (freshState, typeDefnInfos, gathered <> origInfos))
    -- Get the previously gathered type infos.
    (_, _, infos') <- get
    let env = second typeInfoToType <$> infos'
    -- Elaborate multiple definitions simultaneously.
    -- For instance, while elaborating 2 definitions, the typing rule is:
    --
    -- Γ ⊢ e1 ↑ (s1, t1)
    -- s1 Γ ⊢ e2 ↑ (s2, t2)
    ---- Simul2 ------------------------
    -- (e1, e2) ↑ (s2 . s1, (s2 t1, t2))
    --
    -- For 3 definitions, the typing rule is:
    -- Γ ⊢ e1 ↑ (s1, t1)
    -- s1 Γ ⊢ e2 ↑ (s2, t2)
    -- s2 s1 Γ ⊢ e3 ↑ (s3, t3)
    ---- Simul3 -----------------------
    -- ((e1, e2), e3) ↑ (s3 . s2 . s1, (s3 (s2 t1, t2), t3))
    --
    -- And it goes on and on ...
    -- Notice that Simul3 is merely doing Simul2 twice.
    -- Therefore, we need to do a `foldlM` to elaborate definitions. 
    (_, names, tys, _sub) <-
      foldlM (\(context, names, tys, sub) funcDefn -> do
        case funcDefn of
          (FuncDefn name expr) -> do
            (ty, _, sub1) <- elaborate expr context -- Calling `head` is safe for the meantime.
            unifySub <- unifyType (subst sub1 (fromJust $ lookup (Index name) context)) (fromJust ty) (locOf name) -- the first `fromJust` should also be safe.
            -- We see if there are signatures restricting the type of function definitions.
            case lookup (Index name) sigEnv of
              -- If there is, we save the restricted type.
              Just ty' -> do
                _ <- unifyType (fromJust ty) ty' (locOf name)
                return (subst (unifySub `compose` sub1) context, name : names, subst unifySub <$> (ty' : (subst sub1 <$> tys)), unifySub `compose` sub1 `compose` sub)
              -- If not, we proceed as if it's normal.
              Nothing -> return (subst (unifySub `compose` sub1) context, name : names, subst unifySub <$> (subst sub1 (fromJust ty) : (subst sub1 <$> tys)), unifySub `compose` sub1 `compose` sub)
          _ -> return (context, names, tys, sub)
      ) (env, mempty, mempty, mempty) funcDefns
    -- Generalize the types of definitions, i.e. change free type variables into metavariables.
    mapM_ (\(name, ty) -> do
            ty' <- generalize ty env -- TODO: Why???
            let info = (Index name, ConstTypeInfo ty')
            modify (\(freshState, typeDefnInfos, origInfos) -> (freshState, typeDefnInfos, info : origInfos))
          ) (zip names tys)
    where
      split :: [Definition] -> ([Definition], [Definition], [Definition])
      split defs = foldr (
          \def (typeDefns, sigs, funcDefns)  -> case def of
            d @ TypeDefn {} -> (d : typeDefns, sigs, funcDefns)
            d @ FuncDefnSig {} -> (typeDefns, d : sigs, funcDefns)
            d @ FuncDefn {} -> (typeDefns, sigs, d : funcDefns)
        ) mempty defs

      gatherCtorNames :: [Definition] -> [Name]
      gatherCtorNames defs = do
        def <- defs
        case def of
          TypeDefn _ _ ctors _ -> do
            ctor <- ctors
            let TypeDefnCtor name _ = ctor
            return name
          _ -> []
      
      -- Type definitions are processed here.
      -- We follow the approach described in the paper "Kind Inference for Datatypes": https://dl.acm.org/doi/10.1145/3371121
      -- `collectTypeDefns` is an entry for "Typing Program", presented in page 53:8 in the paper. 
      collectTypeDefns :: [Definition] -> ElaboratorM ()
      collectTypeDefns typeDefns = do
        freshMetaVars <- replicateM (length typeDefns) freshKindName
        let annos = (\(TypeDefn name _args _ctors _loc, kinds) -> KindAnno name kinds) <$> zip typeDefns (KMetaVar <$> freshMetaVars)
        let initEnv = reverse annos <> reverse (UnsolvedUni <$> freshMetaVars)
        (newTypeInfos, newTypeDefnInfos) <- inferDataTypes (mempty, initEnv) ((\(TypeDefn name args ctors loc) -> (name, args, ctors, loc)) <$> typeDefns)
        let newTypeInfos' = second TypeDefnCtorInfo <$> subst newTypeDefnInfos newTypeInfos
        let newTypeDefnInfos' =
             (\case
                KindAnno name kind -> (Index name, kind)
                UnsolvedUni _name -> error "Unsolved KMetaVar."
                SolvedUni name kind -> (Index name, kind)) <$> subst newTypeDefnInfos newTypeDefnInfos
        modify (\(freshState, origTypeDefnInfos, origTypeInfos) -> (freshState, newTypeDefnInfos' <> origTypeDefnInfos, newTypeInfos' <> origTypeInfos))
        where
          -- This is an entry for "Typing Datatype Decl." several times, presented in page 53:8.
          inferDataTypes :: (Fresh m, MonadError TypeError m) => (TypeEnv, KindEnv) -> [(Name, [Name], [TypeDefnCtor], Loc)] -> m (TypeEnv, KindEnv)
          inferDataTypes (typeEnv, kindEnv) [] = do
            -- throwError $ UndefinedType $ Name (Text.pack $ show (typeEnv, defaultMeta kindEnv)) NoLoc
            return (typeEnv, defaultMeta kindEnv) -- TODO: Check if this is correct.
            where
              defaultMeta :: KindEnv -> KindEnv
              defaultMeta env =
                (\case
                  KindAnno name kind -> KindAnno name kind
                  UnsolvedUni name -> SolvedUni name $ KStar $ locOf name
                  SolvedUni name kind -> SolvedUni name kind
                ) <$> env
          inferDataTypes (typeEnv, kindEnv) ((tyName, tyParams, ctors, loc) : dataTypesInfo) = do
            (typeEnv', kindEnv') <- inferDataType kindEnv tyName tyParams ctors loc
            (typeEnv'', kindEnv'') <- inferDataTypes (typeEnv', kindEnv') dataTypesInfo
            return (typeEnv <> typeEnv' <> typeEnv'', kindEnv'')

          -- This is an entry for "Typing Datatype Decl.", presented in page 53:8.
          inferDataType :: (Fresh m, MonadError TypeError m) => KindEnv -> Name -> [Name] -> [TypeDefnCtor] -> Loc -> m (TypeEnv, KindEnv)
          inferDataType env tyName tyParams ctors loc = do
            case find (isKindAnno tyName) env of
              Just (KindAnno _name k) -> do
                metaVarNames <- replicateM (length tyParams) freshKindName
                let newEnv = (UnsolvedUni <$> reverse metaVarNames) <> env
                -- We do a unification here.
                newEnv' <- unifyKind newEnv (subst env k) (wrapKFunc (KMetaVar <$> reverse metaVarNames) (KStar NoLoc)) loc
                let solvedEnv = (\(SolvedUni _ kind) -> kind) <$> take (length tyParams) newEnv'
                let envForInferingCtors = zipWith KindAnno (reverse tyParams) solvedEnv <> drop (length tyParams) newEnv'
                (inferedTypes, finalEnv) <- inferCtors envForInferingCtors tyName tyParams ctors
                let ctorIndices = (\(TypeDefnCtor name _) -> Index name) <$> ctors
                return (zip ctorIndices inferedTypes, drop (length tyParams) finalEnv)
              _ -> throwError $ UndefinedType tyName -- TODO: Fix bug.
            where
              wrapKFunc :: [Kind] -> Kind -> Kind
              wrapKFunc [] k = k
              wrapKFunc (k : ks) k' = wrapKFunc ks (KFunc k k' $ k <--> k')

              formTy con params =
                case params of
                  [] -> con
                  n : ns -> formTy (TApp con n $ con <--> n) ns

              -- This is an entry for "Typing Data Constructor Decl." several times, presented in page 53:8.
              inferCtors :: (Fresh m, MonadError TypeError m) => KindEnv -> Name -> [Name] -> [TypeDefnCtor] -> m ([Type], KindEnv)
              inferCtors env' _ _ [] = return (mempty, env')
              inferCtors env' tyName' tyParamNames ctors' = do
                -- Give type variables fresh names to prevent name collision.
                freshNames <- mapM freshName' $ (\(Name text _) -> "Type." <> text) <$> tyParamNames
                inferCtors' env' tyName' tyParamNames freshNames ctors'
                where
                  -- Recursion happens here.
                  inferCtors' :: (Fresh m, MonadError TypeError m) => KindEnv -> Name -> [Name] -> [Name] -> [TypeDefnCtor] -> m ([Type], KindEnv)
                  inferCtors' env'' _ _ _ [] = return (mempty, env'')
                  inferCtors' env'' tyName'' tyParamNames' freshNames (ctor : restOfCtors) = do
                    (ty, newEnv) <- inferCtor env'' tyName'' tyParamNames freshNames ctor
                    (tys, anotherEnv) <- inferCtors' newEnv tyName'' tyParamNames' freshNames restOfCtors
                    return (ty : tys, newEnv <> anotherEnv)
              
              -- This is an entry for "Typing Data Constructor Decl.", presented in page 53:8.
              inferCtor :: (Fresh m, MonadError TypeError m) => KindEnv -> Name -> [Name] -> [Name] -> TypeDefnCtor -> m (Type, KindEnv)
              inferCtor env' tyName' tyParamNames freshNames (TypeDefnCtor _conName params) = do
                let sub = Map.fromList . zip tyParamNames $ freshNames
                let sub' = Map.fromList . zip tyParamNames $ TMetaVar <$> freshNames <*> pure NoLoc
                let ty = subst sub' $ wrapTFunc params (formTy (TData tyName' (locOf tyName')) (TMetaVar <$> tyParamNames <*> pure NoLoc))
                -- Here, we enter the world for infering kinds.
                (_kind, env'') <- inferKind (renameKindEnv sub env') ty
                return (ty, env'')
                where
                  renameKindEnv :: Map.Map Name Name -> KindEnv -> KindEnv
                  renameKindEnv sub env'' = 
                    (\case
                      KindAnno name kind -> case Map.lookup name sub of
                        Nothing -> KindAnno name kind
                        Just name' -> KindAnno name' kind
                      UnsolvedUni name -> UnsolvedUni name
                      SolvedUni name kind -> SolvedUni name kind
                    ) <$> env''

      collectFuncSigs :: [Definition] -> ElaboratorM ()
      collectFuncSigs funcSigs =
        mapM_ (\(FuncDefnSig n t _ _) -> do
          let infos = (Index n, ConstTypeInfo t)
          modify (\(freshState, typeDefnInfos, origInfos) -> (freshState, typeDefnInfos, infos : origInfos))
        ) funcSigs

      generalize :: Fresh m => Type -> TypeEnv -> m Type
      generalize ty' env' = do
        let free = Set.toList (freeVars ty') \\ Set.toList (freeVars env')
        metaVars <- replicateM (length free) freshMetaVar
        let sub = zip free metaVars
        return $ subst (Map.fromList sub) ty'

instance CollectIds Declaration where
  collectIds (ConstDecl ns t _ _) = modify (\(freshState, typeDefnInfos, origInfos) -> (freshState, typeDefnInfos, infos <> origInfos))
    where infos = map ((, ConstTypeInfo t) . Index) ns
  collectIds (VarDecl   ns t _ _) = modify (\(freshState, typeDefnInfos, origInfos) -> (freshState, typeDefnInfos, infos <> origInfos))
    where infos = map ((, VarTypeInfo t) . Index) ns


--------------------------------------------------------------------------------
-- Elaboration


-- The type family `Typed` turns data into its typed version.
type family Typed untyped where
  Typed Definition = Typed.TypedDefinition
  Typed Declaration = Typed.TypedDeclaration
  Typed TypeDefnCtor = Typed.TypedTypeDefnCtor
  Typed Program = Typed.TypedProgram
  Typed Stmt = Typed.TypedStmt
  Typed GdCmd = Typed.TypedGdCmd
  Typed Expr = Typed.TypedExpr
  Typed Chain = Typed.TypedChain
  Typed Name = Name
  Typed ChainOp = Op
  Typed ArithOp = Op
  Typed TypeOp = Op
  Typed Type = ()
  Typed Interval = ()
  Typed Endpoint = ()
  Typed [a] = [Typed a]
  Typed (Maybe a) = Maybe (Typed a)

class Located a => Elab a where
    elaborate :: a -> TypeEnv -> ElaboratorM (Maybe Type, Typed a, Subs Type)


-- Note that we pass the collected ids into each sections of the program.
-- After `collectIds`, we don't need to change the state.
instance Elab Program where
  elaborate (Program defns decls exprs stmts loc) _env = do
    mapM_ collectIds decls
    -- The `reverse` here shouldn't be needed now. In the past, it was a trick to make things work.
    -- I still keep it as-is in case of future refactoring / rewriting.
    collectIds $ reverse defns
    (_, _, infos) <- get
    typedDefns <- mapM (\defn -> do
                          typedDefn <- elaborate defn $ second typeInfoToType <$> infos
                          let (_, typed, _) = typedDefn
                          return typed
                       ) defns
    typedDecls <- mapM (\decl -> do
                          typedDecl <- elaborate decl $ second typeInfoToType <$> infos
                          let (_, typed, _) = typedDecl
                          return typed
                       ) decls
    typedExprs <- mapM (\expr -> do
                          typedExpr <- elaborate expr $ second typeInfoToType <$> infos
                          let (_, typed, _) = typedExpr
                          return typed
                       ) exprs
    typedStmts <- mapM (\stmt -> do
                          typedStmt <- elaborate stmt $ second typeInfoToType <$> infos
                          let (_, typed, _) = typedStmt
                          return typed
                       ) stmts
    return (Nothing, Typed.Program typedDefns typedDecls typedExprs typedStmts loc, mempty)

instance Elab Definition where
  elaborate (TypeDefn name args ctors loc) env = do
    let m = Set.fromList args
    mapM_ (\(TypeDefnCtor _ ts) -> mapM_ (scopeCheck m) ts) ctors
    ctors' <- mapM (\ctor -> do
                      (_, typed, _) <- elaborate ctor env
                      return typed
                   ) ctors
    return (Nothing, Typed.TypeDefn name args ctors' loc, mempty)
   where
    scopeCheck :: MonadError TypeError m => Set.Set Name -> Type -> m ()
    scopeCheck ns t = mapM_ (\n -> if Set.member n ns then return () else throwError $ NotInScope n) (freeVars t)
  elaborate (FuncDefnSig name ty maybeExpr loc) env = do
    expr' <- mapM (\expr -> do
                    (_, typed, _) <- elaborate expr env
                    return typed
                  ) maybeExpr
    return (Nothing, Typed.FuncDefnSig name ty expr' loc, mempty)
  elaborate (FuncDefn name expr) env = do
    (_, typed, _) <- elaborate expr env
    return (Nothing, Typed.FuncDefn name typed, mempty)

instance Elab TypeDefnCtor where
  elaborate (TypeDefnCtor name ts) _ = do
    return (Nothing, Typed.TypedTypeDefnCtor name ts, mempty)

instance Elab Declaration where
  elaborate (ConstDecl names ty prop loc) env =
    case prop of
      Just p -> do
        (_, p', _) <- elaborate p env
        return (Nothing, Typed.ConstDecl names ty (Just p') loc, mempty)
      Nothing -> return (Nothing, Typed.ConstDecl names ty Nothing loc, mempty)
  elaborate (VarDecl names ty prop loc) env =
    case prop of
      Just p -> do
        (_, p', _) <- elaborate p env
        return (Nothing, Typed.VarDecl names ty (Just p') loc, mempty)
      Nothing -> return (Nothing, Typed.VarDecl names ty Nothing loc, mempty)

-- This function is used during elaborating stmts.
checkAssign :: [(Index, TypeInfo)] -> Name -> ElaboratorM Type
checkAssign infos name = do
  case lookup (Index name) infos of
    Just (VarTypeInfo t) -> pure t
    Just _               -> throwError $ AssignToConst name
    Nothing              -> throwError $ NotInScope name

instance Elab Stmt where
  elaborate (Skip  loc     ) _ = return (Nothing, Typed.Skip loc, mempty)
  elaborate (Abort loc     ) _ = return (Nothing, Typed.Abort loc, mempty)
  elaborate (Assign names exprs loc) env = do
    duplicationCheck names
    let ass = zip names exprs
    let an  = length ass
    if
      | an < length exprs -> throwError $ RedundantExprs (drop an exprs)
      | an < length names -> throwError $ RedundantNames (drop an names)
      | otherwise      -> do
        (_, _, infos) <- get
        exprs' <- mapM (\(name, expr) -> do
                          ty <- checkAssign infos name
                          (ty', typedExpr, _) <- elaborate expr env
                          _ <- unifyType ty (fromJust ty') $ locOf expr
                          return typedExpr
                       ) ass
        return (Nothing, Typed.Assign names exprs' loc, mempty)
  elaborate (AAssign arr index e loc) env = do
    tv <- freshVar
    (arrTy, typedArr, arrSub) <- elaborate arr env
    (indexTy, typedIndex, indexSub) <- elaborate index $ subst arrSub env
    uniSubIndex <- unifyType (subst indexSub $ fromJust indexTy) (tInt NoLoc) (locOf index)
    -- TODO: Wrap type-level application of operators into a function.
    uniSubArr <- unifyType (subst (indexSub `compose` uniSubIndex) (fromJust arrTy)) (tInt NoLoc ~-> tv) (locOf arr)
    (eTy, typedE, eSub) <- elaborate e $ subst (uniSubArr `compose` uniSubIndex `compose` indexSub `compose` arrSub) env
    _ <- unifyType (subst eSub $ fromJust eTy) (subst uniSubArr tv) (locOf e)
    return (Nothing, Typed.AAssign typedArr typedIndex typedE loc, mempty)
  elaborate (Assert expr loc        ) env = do
    (ty, _, sub) <- elaborate expr env
    _ <- unifyType (subst sub $ fromJust ty) (tBool NoLoc) (locOf expr)
    (_, typedExpr, _) <- elaborate expr env
    return (Nothing, Typed.Assert typedExpr loc, mempty)
  elaborate (LoopInvariant e1 e2 loc) env = do
    (ty1, _, sub1) <- elaborate e1 env
    _ <- unifyType (subst sub1 $ fromJust ty1) (tBool NoLoc) (locOf e1)
    (_, e1', _) <- elaborate e1 env
    (ty2, _, sub2) <- elaborate e2 env
    _ <- unifyType (subst sub2 $ fromJust ty2) (tInt NoLoc) (locOf e2)
    (_, e2', _) <- elaborate e2 env
    return (Nothing, Typed.LoopInvariant e1' e2' loc, mempty)
  elaborate (Do gds loc) env = do
    gds' <- mapM (\gd -> do
                  (_, typed, _) <- elaborate gd env
                  return typed
                 ) gds
    return (Nothing, Typed.Do gds' loc, mempty)
  elaborate (If gds loc) env = do
    gds' <- mapM (\gd -> do
                  (_, typed, _) <- elaborate gd env
                  return typed
                 ) gds
    return (Nothing, Typed.If gds' loc, mempty)
  elaborate (Spec text range) _ = return (Nothing, Typed.Spec text range, mempty)
  elaborate (Proof text1 text2 range) _ = return (Nothing, Typed.Proof text1 text2 range, mempty)
  elaborate (Alloc var exprs loc) env = do
    (_, _, infos) <- get
    ty <- checkAssign infos var
    _ <- unifyType ty (tInt NoLoc) $ locOf var
    typedExprs <-
      mapM
        (\expr -> do
          (ty', typedExpr, _) <- elaborate expr env
          _ <- unifyType (fromJust ty') (tInt NoLoc) (locOf expr)
          return typedExpr
        ) exprs
    return (Nothing, Typed.Alloc var typedExprs loc, mempty)
  elaborate (HLookup name expr loc) env = do
    (_, _, infos) <- get
    ty <- checkAssign infos name
    _ <- unifyType ty (tInt NoLoc) $ locOf name
    (ty', typedExpr, _) <- elaborate expr env
    _ <- unifyType (fromJust ty') (tInt NoLoc) (locOf expr)
    return (Nothing, Typed.HLookup name typedExpr loc, mempty)
  elaborate (HMutate left right loc) env = do
    (ty, typedLeft, _) <- elaborate left env
    _ <- unifyType (fromJust ty) (tInt NoLoc) (locOf left)
    (ty', typedRight, _) <- elaborate right env
    _ <- unifyType (fromJust ty') (tInt NoLoc) (locOf right)
    return (Nothing, Typed.HMutate typedLeft typedRight loc, mempty)
  elaborate (Dispose expr loc) env = do
    (ty, typedExpr, _) <- elaborate expr env
    _ <- unifyType (fromJust ty) (tInt NoLoc) (locOf expr)
    return (Nothing, Typed.Dispose typedExpr loc, mempty)
  elaborate Block {} env = undefined -- TODO: Implement blocks.

instance Elab GdCmd where
  elaborate (GdCmd expr stmts loc) env = do
    (ty, _, sub) <- elaborate expr env
    _ <- unifyType (subst sub $ fromJust ty) (tBool NoLoc) (locOf expr)
    (_, e', _) <- elaborate expr env
    s' <- mapM (\stmt -> do
                  (_, typed, _) <- elaborate stmt env
                  return typed
               ) stmts
    return (Nothing, Typed.TypedGdCmd e' s' loc, mempty)

instantiate :: Fresh m => Type -> m Type
instantiate ty = do
  let freeMeta = Set.toList (freeMetaVars ty)
  new <- replicateM (length freeMeta) freshVar
  return $ subst (Map.fromList $ zip freeMeta new) ty

-- You can freely use `fromJust` below to extract the underlying `Type` from the `Maybe Type` you got.
-- You should also ensure that `elaborate` in `Elab Expr` returns a `Just` when it comes to the `Maybe Type` value.
-- TODO: Maybe fix this?

-- The typing rules below are written by SCM.

-- Γ ⊢ e ↑ (s, u)
-- v = unify (u, t)
---- Checking ------
-- Γ ⊢ e : t ↓ (v . s)

instance Elab Expr where
  elaborate (Lit lit loc) _ = let ty = litTypes lit loc in return (Just ty, Typed.Lit lit ty loc, mempty)
  -- x : t ∈ Γ
  -- t ⊑ u
  ---- Var, Const, Op --
  -- Γ ⊢ x ↑ (∅, t)
  elaborate (Var x loc) env = case lookup (Index x) env of
      Just ty -> do
        ty' <- instantiate ty
        return (Just ty', Typed.Var x ty' loc, mempty)
      Nothing -> throwError $ NotInScope x
  elaborate (Const x loc) env = case lookup (Index x) env of
      Just ty -> do
        ty' <- instantiate ty
        return (Just ty', Typed.Const x ty' loc, mempty)
      Nothing -> throwError $ NotInScope x
  elaborate (Op o) env = do
    (ty, op, sub) <- elaborate o env
    ty' <- instantiate $ fromJust ty
    return (Just ty', subst sub (Typed.Op op ty'), sub)
  elaborate (Chain ch) env = (\(ty, typed, sub) -> (ty, Typed.Chain typed, sub)) <$> elaborate ch env
  -- Γ ⊢ e1 ↑ (s1, t1)
  -- s1 Γ ⊢ e2 ↑ (s2, t2)
  -- b fresh   v = unify (s2 t1, t2 -> b)
  ---- App -----------------------------------
  -- Γ ⊢ e1 e2 ↑ (v . s2 . s1, v b)
  elaborate (App e1 e2 loc) env = do
    tv <- freshVar
    (ty1, typedExpr1, sub1) <- elaborate e1 env
    (ty2, typedExpr2, sub2) <- elaborate e2 $ subst sub1 env
    sub3 <- unifyType (subst sub2 $ fromJust ty1) (fromJust ty2 ~-> tv) loc
    let sub = sub3 `compose` sub2 `compose` sub1
    return (Just $ subst sub3 tv, subst sub (Typed.App typedExpr1 typedExpr2 loc), sub)
  -- a fresh
  -- Γ, x : a ⊢ e ↑ (s, t)
  ---- Lam ----------------------
  -- Γ ⊢ (λ x . e) ↑ (s, s a -> t)
  elaborate (Lam bound expr loc) env = do
    tv <- freshVar
    let newEnv = (Index bound, tv) : env
    (ty1, typedExpr1, sub1) <- elaborate expr newEnv
    let returnTy = subst sub1 tv ~-> fromJust ty1
    return (Just returnTy, subst sub1 (Typed.Lam bound (subst sub1 tv) typedExpr1 loc), sub1)
  elaborate (Func name clauses l) env = undefined
  -- Γ ⊢ e1 ↑ (s1, t1)
  -- s1 Γ ⊢ e2 ↑ (s2, t2)
  ---- Tuple -----------------------------
  -- Γ ⊢ (e1, e2) ↑ (s2 . s1, (s2 t1, t2))
  elaborate (Tuple xs) env = undefined
  elaborate (Quant quantifier bound restriction inner loc) env = do
    duplicationCheck bound
    tv <- freshVar
    (quantTy, quantTypedExpr, quantSub) <- elaborate quantifier env
    -- TODO: Write out the typing rule.
    case quantifier of
      Op (Hash _) -> do
        tvs <- replicateM (length bound) freshVar
        let newEnv = subst quantSub env
        (resTy, resTypedExpr, resSub) <- elaborate restriction $ zip (Index <$> bound) tvs <> newEnv
        uniSub2 <- unifyType (fromJust resTy) (tBool NoLoc) (locOf restriction)
        let newEnv' = subst (uniSub2 `compose` resSub) newEnv
        (innerTy, innerTypedExpr, innerSub) <- elaborate inner $ zip (Index <$> bound) (subst (uniSub2 `compose` resSub) <$> tvs) <> newEnv'
        uniSub3 <- unifyType (subst innerSub $ fromJust innerTy) (subst (uniSub2 `compose` resSub `compose` quantSub) tv) (locOf inner)
        let sub = uniSub3 `compose` innerSub `compose` uniSub2 `compose` resSub `compose` quantSub
        return (Just $ subst quantSub tv, subst sub (Typed.Quant quantTypedExpr bound resTypedExpr innerTypedExpr loc), sub)
      -- a fresh   Γ ⊢ ⊕ : (a -> a -> a) ↓ s⊕
      -- b fresh   s⊕ Γ, i : b ⊢ R : Bool ↓ sR
      -- sR (s⊕ Γ), i : sR b ⊢ B : sR (s⊕ a) ↓ sB
      ---- Quant -------------------------------------------
      -- Γ ⊢ ⟨⊕ i : R : B⟩ ↑ (sB . sR , sB (sR (s⊕ a)))
      _ -> do
        uniSub <- unifyType (subst quantSub $ fromJust quantTy) (tv ~-> tv ~-> tv) (locOf quantifier)
        tvs <- replicateM (length bound) freshVar
        let newEnv = subst (uniSub `compose` quantSub) env
        (resTy, resTypedExpr, resSub) <- elaborate restriction $ zip (Index <$> bound) tvs <> newEnv
        uniSub2 <- unifyType (fromJust resTy) (tBool NoLoc) (locOf restriction)
        let newEnv' = subst (uniSub2 `compose` resSub) newEnv
        (innerTy, innerTypedExpr, innerSub) <- elaborate inner $ zip (Index <$> bound) (subst (uniSub2 `compose` resSub) <$> tvs) <> newEnv'
        uniSub3 <- unifyType (subst innerSub $ fromJust innerTy) (subst (uniSub2 `compose` resSub `compose` uniSub `compose` quantSub) tv) (locOf inner)
        return (Just $ subst (uniSub3 `compose` innerSub `compose` uniSub2 `compose` resSub `compose` uniSub `compose` quantSub) tv,
                subst (uniSub3 `compose` innerSub `compose` uniSub2 `compose` resSub `compose` uniSub `compose` quantSub) (Typed.Quant quantTypedExpr bound resTypedExpr innerTypedExpr loc),
                uniSub3 `compose` innerSub `compose` uniSub2 `compose` resSub)
  elaborate (RedexShell _ expr) env = undefined
  elaborate (RedexKernel n _ _ _) env = undefined
  -- b fresh    Γ ⊢ a : Array .. of b ↓ sa
  -- sa Γ ⊢ i : Int ↓ si
  ---- ArrIdx ----------------------------
  -- Γ ⊢ a[i] ↑ (si . sa, si (sa b))
  elaborate (ArrIdx e1 e2 loc) env = do -- I didn't follow the above typing rules. Hopefully this is correct.
    tv <- freshVar
    (ty1, typedExpr1, sub1) <- elaborate e1 env
    (ty2, typedExpr2, sub2) <- elaborate e2 (subst sub1 env)
    sub3 <- unifyType (subst sub2 $ fromJust ty2) (tInt NoLoc) (locOf e2)
    sub4 <- unifyType (subst (sub3 `compose` sub2) (fromJust ty1)) (tInt NoLoc ~-> tv) loc
    let sub = sub4 `compose` sub3 `compose` sub2 `compose` sub1
    return (Just $ subst sub3 tv, subst sub (Typed.ArrIdx typedExpr1 typedExpr2 loc), sub)
  -- b fresh    Γ ⊢ a : Array .. of b ↓ sa
  -- sa Γ ⊢ i : Int ↓ si
  -- si (sa Γ) ⊢ e : si (sa b) ↓ se
  ---- ArrUpd --------------------------------------
  -- Γ ⊢ (a : i ↦ e) ↑ (se . si . sa, se (si (sa b)))
  elaborate (ArrUpd arr index e loc) env = do -- I didn't follow the above typing rules. Hopefully this is correct.
    tv <- freshVar
    (arrTy, typedArr, arrSub) <- elaborate arr env
    (indexTy, typedIndex, indexSub) <- elaborate index $ subst arrSub env
    uniSubIndex <- unifyType (subst indexSub $ fromJust indexTy) (tInt NoLoc) (locOf index)
    uniSubArr <- unifyType (subst (indexSub `compose` uniSubIndex) (fromJust arrTy)) (tInt NoLoc ~-> tv) (locOf arr)
    (eTy, typedE, eSub) <- elaborate e $ subst (uniSubArr `compose` uniSubIndex `compose` indexSub `compose` arrSub) env
    uniSubExpr <- unifyType (subst eSub $ fromJust eTy) (subst uniSubArr tv) (locOf e)
    let sub = uniSubExpr `compose` eSub `compose` uniSubArr `compose` uniSubIndex `compose` indexSub `compose` arrSub
    return (subst uniSubArr arrTy, subst sub (Typed.ArrUpd typedArr typedIndex typedE loc), sub)
  elaborate (Case expr cs l) env = undefined -- TODO: Implement pattern matching.

instance Elab Chain where -- TODO: Make sure the below implementation is correct.
  elaborate (More (More ch' op1 e1 loc1) op2 e2 loc2) env = do
    tv <- freshVar
    (_chainTy, typedChain, chainSub) <- elaborate (More ch' op1 e1 loc1) env
    (opTy, opTyped, opSub) <- elaborate op2 env
    opTy' <- instantiate $ fromJust opTy
    (ty1, _typedExpr1, sub1) <- elaborate e1 $ subst chainSub env
    (ty2, typedExpr2, sub2) <- elaborate e2 $ subst (chainSub <> sub1) env
    unifyTy <- unifyType (fromJust ty1 ~-> fromJust ty2 ~-> tv) opTy' loc2
    let sub = chainSub <> opSub <> sub1 <> sub2
    return (Just $ subst unifyTy tv, subst sub $ Typed.More typedChain opTyped (subst unifyTy opTy') typedExpr2, sub)
  elaborate (More (Pure e1 _loc1) op e2 loc2) env = do
    tv <- freshVar
    (opTy, opTyped, opSub) <- elaborate op env
    opTy' <- instantiate $ fromJust opTy
    (ty1, typedExpr1, sub1) <- elaborate e1 env
    (ty2, typedExpr2, sub2) <- elaborate e2 $ subst sub1 env
    unifyTy <- unifyType (fromJust ty1 ~-> fromJust ty2 ~-> tv) opTy' loc2
    let sub = unifyTy <> sub2 <> sub1 <> opSub
    return (Just $ subst unifyTy tv, subst sub $ Typed.More (Typed.Pure typedExpr1) opTyped (subst unifyTy opTy') typedExpr2, sub)
  elaborate (Pure _expr _loc) _ = error "Chain of length 1 shouldn't exist."

instance Elab ChainOp where
  elaborate (EQProp  l) _ = return (Just $ tBool .-> tBool .-> tBool $ l, ChainOp $ EQProp l, mempty)
  elaborate (EQPropU l) _ = return (Just $ tBool .-> tBool .-> tBool $ l, ChainOp $ EQPropU l, mempty)
  elaborate (EQ      l) _ = do
    x <- freshMetaVar
    return (Just $ const x .-> const x .-> tBool $ l, ChainOp $ EQ l, mempty)
  elaborate (NEQ  l) _ = do
    x <- freshMetaVar
    return (Just $ const x .-> const x .-> tBool $ l, ChainOp $ NEQ l, mempty)
  elaborate (NEQU l) _ = do
    x <- freshMetaVar
    return (Just $ const x .-> const x .-> tBool $ l, ChainOp $ NEQU l, mempty)
  elaborate (LTE  l) _ = return (Just $ tInt .-> tInt .-> tBool $ l, ChainOp $ LTE l, mempty)
  elaborate (LTEU l) _ = return (Just $ tInt .-> tInt .-> tBool $ l, ChainOp $ LTEU l, mempty)
  elaborate (GTE  l) _ = return (Just $ tInt .-> tInt .-> tBool $ l, ChainOp $ GTE l, mempty)
  elaborate (GTEU l) _ = return (Just $ tInt .-> tInt .-> tBool $ l, ChainOp $ GTEU l, mempty)
  elaborate (LT   l) _ = return (Just $ tInt .-> tInt .-> tBool $ l, ChainOp $ LT l, mempty)
  elaborate (GT   l) _ = return (Just $ tInt .-> tInt .-> tBool $ l, ChainOp $ GT l, mempty)

instance Elab ArithOp where
  elaborate (Implies  l) _ = return (Just $ tBool .-> tBool .-> tBool $ l, ArithOp $ Implies l, mempty)
  elaborate (ImpliesU l) _ = return (Just $ tBool .-> tBool .-> tBool $ l, ArithOp $ ImpliesU l, mempty)
  elaborate (Conj     l) _ = return (Just $ tBool .-> tBool .-> tBool $ l, ArithOp $ Conj l, mempty)
  elaborate (ConjU    l) _ = return (Just $ tBool .-> tBool .-> tBool $ l, ArithOp $ ConjU l, mempty)
  elaborate (Disj     l) _ = return (Just $ tBool .-> tBool .-> tBool $ l, ArithOp $ Disj l, mempty)
  elaborate (DisjU    l) _ = return (Just $ tBool .-> tBool .-> tBool $ l, ArithOp $ DisjU l, mempty)
  elaborate (Neg      l) _ = return (Just $ tBool .-> tBool $ l, ArithOp $ Neg l, mempty)
  elaborate (NegU     l) _ = return (Just $ tBool .-> tBool $ l, ArithOp $ NegU l, mempty)
  elaborate (NegNum   l) _ = return (Just $ tInt .-> tInt $ l, ArithOp $ NegNum l, mempty)
  elaborate (Add      l) _ = return (Just $ tInt .-> tInt .-> tInt $ l, ArithOp $ Add l, mempty)
  elaborate (Sub      l) _ = return (Just $ tInt .-> tInt .-> tInt $ l, ArithOp $ Sub l, mempty)
  elaborate (Mul      l) _ = return (Just $ tInt .-> tInt .-> tInt $ l, ArithOp $ Mul l, mempty)
  elaborate (Div      l) _ = return (Just $ tInt .-> tInt .-> tInt $ l, ArithOp $ Div l, mempty)
  elaborate (Mod      l) _ = return (Just $ tInt .-> tInt .-> tInt $ l, ArithOp $ Mod l, mempty)
  elaborate (Max      l) _ = return (Just $ tInt .-> tInt .-> tInt $ l, ArithOp $ Max l, mempty)
  elaborate (Min      l) _ = return (Just $ tInt .-> tInt .-> tInt $ l, ArithOp $ Min l, mempty)
  elaborate (Exp      l) _ = return (Just $ tInt .-> tInt .-> tInt $ l, ArithOp $ Exp l, mempty)
  elaborate (Hash     l) _ = return (Just $ tBool .-> tInt $ l, ArithOp $ Hash l, mempty)
  elaborate (PointsTo l) _ = return (Just $ tInt .-> tInt .-> tInt $ l, ArithOp $ PointsTo l, mempty)
  elaborate (SConj    l) _ = return (Just $ tBool .-> tBool .-> tBool $ l, ArithOp $ SConj l, mempty)
  elaborate (SImp     l) _ = return (Just $ tBool .-> tBool .-> tBool $ l, ArithOp $ SImp l, mempty)

instance Elab TypeOp where
  elaborate (Arrow _) _ = undefined -- We do not have a kind system yet.

--------------------------------------------------------------------------------
-- Kind inference

-- This is "Kinding" mentioned in 53:10 in the paper "Kind Inference for Datatypes".
inferKind :: (Fresh m, MonadError TypeError m) => KindEnv -> Type -> m (Kind, KindEnv)
inferKind env (TBase _ loc) = return (KStar loc, env)
inferKind env (TArray _ _ loc) = return (KStar loc, env)
inferKind env (TTuple int) = return (kindFromArity int, env)
  where
    kindFromArity :: Int -> Kind
    kindFromArity 0 = KStar NoLoc
    kindFromArity n = KFunc (KStar NoLoc) (kindFromArity $ n - 1) NoLoc
inferKind env (TOp (Arrow loc)) = return (KFunc (KStar loc) (KFunc (KStar loc) (KStar loc) loc) loc, env)
inferKind env (TData name _) =
  case find (isKindAnno name) env of
    Just (KindAnno _name kind) -> return (kind, env)
    _ -> throwError $ UndefinedType name
inferKind env (TApp t1 t2 _) = do
  (k1, env') <- inferKind env t1
  (k2, env'') <- inferKind env' t2
  (k3, env''') <- inferKApp env'' (subst env'' k1) (subst env'' k2)
  return (k3 ,env''')
inferKind env (TVar name _) =
  case find (isKindAnno name) env of
    Just (KindAnno _name kind) -> return (kind, env)
    _ -> throwError $ UndefinedType name
inferKind env (TMetaVar name _) =
  case find (isKindAnno name) env of
    Just (KindAnno _name kind) -> return (kind, env)
    _ -> throwError $ UndefinedType name

isKindAnno :: Name -> KindItem -> Bool
isKindAnno name (KindAnno name' _kind) = name == name'
isKindAnno _ _ = False

-- This is "Application Kinding" mentioned in 53:10 in the paper "Kind Inference for Datatypes".
inferKApp :: (Fresh m, MonadError TypeError m) => KindEnv -> Kind -> Kind -> m (Kind, KindEnv)
inferKApp env (KFunc k1 k2 _) k = do
  env' <- unifyKind env k1 k $ k1 <--> k
  return (k2, env')
inferKApp env (KMetaVar a) k = do
  case nameIndex of
    Nothing -> throwError $ NotInScope a
    Just nameIndex' -> do
      a1 <- freshKindName
      a2 <- freshKindName
      let env' = let (list1, list2) = splitAt nameIndex' env
                 in list1 ++ [SolvedUni a $ KFunc (KMetaVar a1) (KMetaVar a2) $ a1 <--> a2, UnsolvedUni a2, UnsolvedUni a1] ++ tail list2
      env'' <- unifyKind env' (KMetaVar a1) k $ locOf k
      return (KMetaVar a2, env'')
  where
    nameIndex = findIndex (predicate a) env

    predicate name (UnsolvedUni name') = name == name'
    predicate _ _ = False
inferKApp _ k1 k2 = do
  ret <- freshKindName
  throwError $ KindUnifyFailed k1 (KFunc k2 (KMetaVar ret) $ locOf k2) $ locOf k1

--------------------------------------------------------------------------------
-- Unification

unifyType :: MonadError TypeError m => Type -> Type -> Loc -> m (Subs Type)
unifyType (TBase t1 _) (TBase t2 _) _ | t1 == t2 = return mempty
unifyType (TArray _ t1 _) (TArray _ t2 _) l = unifyType t1 t2 l {-  | i1 == i2 = unifies t1 t2 -}
  -- SCM: for now, we do not check the intervals
-- view array of type `t` as function type of `Int -> t`
unifyType (TArray _ t1 _) (TApp (TApp (TOp (Arrow _)) i _) t2 _) l = do
  s1 <- unifyType i (tInt NoLoc) l
  s2 <- unifyType t1 t2 l
  return (s2 `compose` s1)
-- TODO: Deal with any possible type operators.
unifyType (TOp (Arrow _)) (TOp (Arrow _)) _ = pure mempty
unifyType t1@(TData name1 _) t2@(TData name2 _) l = if name1 == name2 then pure mempty else throwError $ UnifyFailed t1 t2 l
unifyType (TApp (TApp (TOp (Arrow _)) i _) t1 _) (TArray _ t2 _) l = do
  s1 <- unifyType i (tInt NoLoc) l
  s2 <- unifyType t1 t2 l
  return (s2 `compose` s1)
unifyType (TApp t1 t2 _) (TApp t3 t4 _) l = do
  s1 <- unifyType t1 t3 l
  s2 <- unifyType (subst s1 t2) (subst s1 t4) l
  return (s2 `compose` s1)
unifyType (TVar x _)     t              l = bind x t l
unifyType t              (TVar x _)     l = bind x t l
unifyType (TMetaVar x _) t              l = bind x t l
unifyType t              (TMetaVar x _) l = bind x t l
unifyType t1             t2             l = throwError $ UnifyFailed t1 t2 l

bind :: MonadError TypeError m => Name -> Type -> Loc -> m (Map.Map Name Type)
bind x t l | same t $ TVar x NoLoc = return mempty
           | occurs x t  = throwError $ RecursiveType x t l
           | otherwise   = return (Map.singleton x t)
  where
    same (TVar v1 _) (TVar v2 _) = v1 == v2
    same _ _ = False

-- This is "Kind Unification" mentioned in 53:10 in the paper "Kind Inference for Datatypes".
unifyKind :: (Fresh m, MonadError TypeError m) => KindEnv -> Kind -> Kind -> Loc -> m KindEnv
unifyKind env (KStar _) (KStar _) _ = return env
unifyKind env (KFunc k1 k2 _) (KFunc k3 k4 _) _ = do
  env' <- unifyKind env k1 k3 (locOf k1)
  unifyKind env' (subst env' k2) (subst env' k4) (locOf k2)
unifyKind env (KMetaVar a) k _ = do
  case aIndex of
    -- The below 4 lines have implementation different from what is written on the paper.
    -- I put the original (probably incorrect) implementation that I think is what the paper describes in comments.
    Nothing -> return env -- throwError $ NotInScope a
    Just aIndex' -> do
      -- let (list1, list2) = splitAt aIndex' env
      (k2, env') <- promote env a k -- (k2, env') <- promote (list1 ++ tail list2) a k
      let aIndex2 = findIndex (predicate a) env'
      case aIndex2 of
        Nothing -> throwError $ NotInScope a
        Just aIndex2' -> do
          let (list1', list2') = splitAt aIndex2' env'
          return $ list1' ++ [SolvedUni a k2] ++ tail list2'
  where
    -- Notice the `fromJust`. This part crashes when `a` is not present in `env`. (They should)
    aIndex = findIndex (predicate a) env

    predicate name (UnsolvedUni name') = name == name'
    predicate _ _ = False
unifyKind env k (KMetaVar a) loc = unifyKind env (KMetaVar a) k loc
unifyKind _env k1 k2 loc = throwError $ KindUnifyFailed k1 k2 loc

-- This is "Promotion" mentioned in 53:10 in the paper "Kind Inference for Datatypes".
promote :: (Fresh m, MonadError TypeError m) => KindEnv -> Name -> Kind -> m (Kind, KindEnv)
promote env _ (KStar loc) = return (KStar loc, env)
promote env name (KFunc k1 k2 loc) = do
  (k3, env') <- promote env name k1
  (k4, env'') <- promote env' name (subst env' k2)
  return (KFunc k3 k4 loc, env'')
promote env a (KMetaVar b) =
  case compare aIndex bIndex of
    Ord.LT -> return (KMetaVar b, env)
    Ord.EQ -> return (KMetaVar b, env) -- TODO: This is possibly wrong since this case isn't mentioned in the paper.
    Ord.GT -> do
      b1 <- freshKindName
      case aIndex of
        Nothing -> throwError $ NotInScope a
        Just aIndex' -> do
          let env' = let (list1, list2) = splitAt aIndex' env in list1 ++ [UnsolvedUni a, UnsolvedUni b1] ++ tail list2
          case bIndex of
            Nothing -> throwError $ NotInScope b
            Just bIndex' -> do
              let env'' = let (list1, list2) = splitAt bIndex' env' in list1 ++ [SolvedUni b (KMetaVar b1)] ++ tail list2
              return (KMetaVar b1, env'')
  where
    aIndex = findIndex (predicate a) env
    bIndex = findIndex (predicate b) env

    predicate name (UnsolvedUni name') = name == name'
    predicate _ _ = False

--------------------------------------------------------------------------------
-- helper combinators

typeInfoToType :: TypeInfo -> Type
typeInfoToType (TypeDefnCtorInfo t) = t
typeInfoToType (ConstTypeInfo    t) = t
typeInfoToType (VarTypeInfo      t) = t

freshVar :: Fresh m => m Type
freshVar = TVar <$> freshName "Type.var" NoLoc <*> pure NoLoc

freshMetaVar :: Fresh m => m Type
freshMetaVar = TMetaVar <$> freshName "Type.metaVar" NoLoc <*> pure NoLoc

freshKindName :: Fresh m => m Name
freshKindName = freshName "Kind.metaVar" NoLoc

litTypes :: Lit -> Loc -> Type
litTypes (Num _) l = tInt l
litTypes (Bol _) l = tBool l
litTypes (Chr _) l = tChar l
litTypes Emp     l = tBool l

tBool, tInt, tChar :: Loc -> Type
tBool = TBase TBool
tInt = TBase TInt
tChar = TBase TChar

(.->) :: (Loc -> Type) -> (Loc -> Type) -> (Loc -> Type)
(t1 .-> t2) l = TApp (TApp (TOp (Arrow NoLoc)) (t1 l) NoLoc) (t2 l) l
infixr 1 .->

(~->) :: Type -> Type -> Type
t1 ~-> t2 = TApp (TApp (TOp (Arrow NoLoc)) t1 NoLoc) t2 NoLoc
infixr 1 ~->

emptyInterval :: Interval
emptyInterval = Interval (Including zero) (Excluding zero) NoLoc
  where zero = Lit (Num 0) NoLoc

-- A class for substitution not needing a Fresh monad.
-- Used only in this module.
-- Moved from GCL.Common to here.
--  SCM: think about integrating it with the other substitution.

class Substitutable a b where
  subst :: a -> b -> b

compose :: Substitutable (Subs a) a => Subs a -> Subs a -> Subs a
s1 `compose` s2 = s1 <> Map.map (subst s1) s2

instance (Substitutable a b, Functor f) => Substitutable a (f b) where
  subst = fmap . subst

instance Substitutable (Subs Type) Type where
  subst _ t@TBase{}        = t
  subst s (TArray i t l  ) = TArray i (subst s t) l
  subst _ (TTuple arity  ) = TTuple arity
  subst _ (TOp op        ) = TOp op
  subst s (TApp l r loc  ) = TApp (subst s l) (subst s r) loc
  subst _ t@TData{}        = t
  subst s t@(TVar n _    ) = Map.findWithDefault t n s
  subst s t@(TMetaVar n _) = Map.findWithDefault t n s

instance Substitutable (Subs Type) Typed.TypedExpr where
  subst s (Typed.Lit lit ty loc) = Typed.Lit lit (subst s ty) loc
  subst s (Typed.Var name ty loc) = Typed.Var name (subst s ty) loc
  subst s (Typed.Const name ty loc) = Typed.Const name (subst s ty) loc
  subst s (Typed.Op op ty) = Typed.Op op $ subst s ty
  subst s (Typed.Chain ch) = Typed.Chain $ subst s ch
  subst s (Typed.App e1 e2 loc) = Typed.App (subst s e1) (subst s e2) loc
  subst s (Typed.Lam name ty expr loc) = Typed.Lam name (subst s ty) (subst s expr) loc
  subst s (Typed.Quant quantifier vars restriction inner loc) = Typed.Quant (subst s quantifier) vars (subst s restriction) (subst s inner) loc
  subst s (Typed.ArrIdx arr index loc) = Typed.ArrIdx (subst s arr) (subst s index) loc
  subst s (Typed.ArrUpd arr index expr loc) = Typed.ArrUpd (subst s arr) (subst s index) (subst s expr) loc

instance Substitutable (Subs Type) Typed.TypedChain where
  subst s (Typed.Pure expr) = Typed.Pure $ subst s expr
  subst s (Typed.More ch op ty expr) = Typed.More (subst s ch) op (subst s ty) (subst s expr)

instance Substitutable KindEnv Kind where
  subst _ (KStar loc) = KStar loc
  subst env (KMetaVar name) = case find (predicate name) env of
    Just (SolvedUni _ kind) -> kind
    _ -> KMetaVar name
    where
      predicate name1 (SolvedUni name2 _kind) = name1 == name2
      predicate _ _ = False
  subst env (KFunc k1 k2 loc) = KFunc (subst env k1) (subst env k2) loc

instance {-# OVERLAPPING #-} Substitutable KindEnv TypeEnv where
  subst a b = b -- FIXME:

instance {-# OVERLAPPING #-} Substitutable KindEnv KindEnv where
  subst a b = b -- FIXME: