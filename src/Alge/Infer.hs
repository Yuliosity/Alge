{-# LANGUAGE LambdaCase #-}

module Alge.Infer (inferProgram, inferExpression, Inference(..)) where

import Alge.Syntax
import Alge.Type
import Control.Monad (foldM, forM, forM_, unless, when, void, zipWithM, (>=>))
import Control.Monad.State.Strict
import Data.List (intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S

data Inference = Inference
  { inferredTypes :: TypeEnv
  , inferredAliases :: Aliases
  } deriving (Eq, Show)

data TcState = TcState
  { nextId :: Int
  , typeSubst :: Map Variable Type
  , rowSubst :: Map Variable Row
  , absentLabels :: Map Variable (Set Name)
  , constraints :: [Constraint]
  , aliases :: Aliases
  , annotationVars :: Map Name Type
  , revision :: Int
  }

type Tc = StateT TcState (Either TypeError)

initialState :: Aliases -> TcState
initialState as = TcState 0 M.empty M.empty M.empty [] as M.empty 0

failure :: String -> Tc a
failure = lift . Left . TypeError

freshId :: Tc Variable
freshId = do
  v <- gets nextId
  modify' (\s -> s {nextId = v + 1})
  pure v

freshType :: Tc Type
freshType = TV <$> freshId

freshRow :: Tc Row
freshRow = Row M.empty . Just <$> freshId

touch :: Tc ()
touch = modify' (\s -> s {revision = revision s + 1})

emitConstraint :: Constraint -> Tc ()
emitConstraint c = modify' (\s -> s {constraints = c : constraints s})

zonk :: Type -> Tc Type
zonk = zonkBound S.empty

zonkBound :: Set Variable -> Type -> Tc Type
zonkBound bound = \case
  TInt -> pure TInt
  TV v | v `S.member` bound -> pure (TV v)
  TV v -> do
    replacement <- gets (M.lookup v . typeSubst)
    maybe (pure (TV v)) (zonkBound bound) replacement
  TRecord r -> TRecord <$> zonkRowBound bound r
  TVariant r -> TVariant <$> zonkRowBound bound r
  TFun a b -> TFun <$> zonkBound bound a <*> zonkBound bound b
  TNamed n ts -> TNamed n <$> mapM (zonkBound bound) ts
  TRec v bodyType -> TRec v <$> zonkBound (S.insert v bound) bodyType

zonkRow :: Row -> Tc Row
zonkRow = zonkRowBound S.empty

zonkRowBound :: Set Variable -> Row -> Tc Row
zonkRowBound bound (Row fs rest) = do
  fields <- mapM (zonkBound bound) fs
  case rest of
    Nothing -> pure (Row fields Nothing)
    Just v -> do
      replacement <- gets (M.lookup v . rowSubst)
      case replacement of
        Nothing -> pure (Row fields (Just v))
        Just r -> do
          Row more tailVar <- zonkRowBound bound r
          unless (M.null (M.intersection fields more)) $ failure "duplicate label in a row substitution"
          pure (Row (M.union fields more) tailVar)

zonkConstraint :: Constraint -> Tc Constraint
zonkConstraint = \case
  Merge k a b c -> Merge k <$> zonkRow a <*> zonkRow b <*> zonkRow c
  Lacks l r -> Lacks l <$> zonkRow r

zonkScheme :: Scheme -> Tc Scheme
zonkScheme (Scheme vs cs t) = Scheme vs <$> mapM zonkConstraint cs <*> zonk t

bindType :: Variable -> Type -> Tc ()
bindType v t = do
  t' <- zonk t
  unless (t' == TV v) $ do
    recursive <- if v `S.member` freeType t'
      then if guarded v False t'
        then pure (TRec v t')
        else failure "infinite inferred type without a guarding labeled field"
      else pure t'
    modify' (\s -> s {typeSubst = M.insert v recursive (typeSubst s)})
    touch

-- Regular recursive data can be inferred; recursive function equations such
-- as the type of `x x` still fail the occurs check.
guarded :: Variable -> Bool -> Type -> Bool
guarded v underLabel t = case t of
  TV w -> v /= w || underLabel
  TInt -> True
  TRecord (Row fs _) -> all (guarded v True) (M.elems fs)
  TVariant (Row fs _) -> all (guarded v True) (M.elems fs)
  TFun a b -> not (v `S.member` (freeType a `S.union` freeType b))
  TNamed _ ts -> all (guarded v underLabel) ts
  TRec binder bodyType -> binder == v || guarded v underLabel bodyType

substituteBound :: Variable -> Type -> Type -> Type
substituteBound variable replacement = go
  where
    go = \case
      TInt -> TInt
      TV v -> if v == variable then replacement else TV v
      TRecord r -> TRecord (row r)
      TVariant r -> TVariant (row r)
      TFun a b -> TFun (go a) (go b)
      TNamed n ts -> TNamed n (map go ts)
      t@(TRec v bodyType) -> if v == variable then t else TRec v (go bodyType)
    row (Row fs rest) = Row (M.map go fs) rest

requireLacks :: Name -> Row -> Tc ()
requireLacks label row = do
  Row fs rest <- zonkRow row
  when (M.member label fs) $ failure ("duplicate label '" ++ label ++ "'")
  case rest of
    Nothing -> pure ()
    Just v -> do
      old <- gets (M.findWithDefault S.empty v . absentLabels)
      unless (label `S.member` old) $ do
        modify' (\s -> s {absentLabels = M.insert v (S.insert label old) (absentLabels s)})
        touch

wellFormedRow :: Row -> Tc ()
wellFormedRow (Row fs rest) = case rest of
  Nothing -> pure ()
  Just v -> mapM_ (\l -> requireLacks l (Row M.empty (Just v))) (M.keys fs)

bindRow :: Variable -> Row -> Tc ()
bindRow v row = do
  r@(Row fs rest) <- zonkRow row
  unless (r == Row M.empty (Just v)) $ do
    when (v `S.member` freeRow r) $ failure "infinite row or inconsistent row remainder"
    forbidden <- gets (M.findWithDefault S.empty v . absentLabels)
    unless (S.null (M.keysSet fs `S.intersection` forbidden)) $
      failure ("duplicate label in row: " ++ intercalate ", " (S.toList (M.keysSet fs `S.intersection` forbidden)))
    case rest of
      Nothing -> pure ()
      Just tailVar -> mapM_ (\l -> requireLacks l (Row M.empty (Just tailVar))) (S.toList forbidden ++ M.keys fs)
    modify' (\s -> s {rowSubst = M.insert v r (rowSubst s)})
    touch

unifyRows :: Set (Type,Type) -> Row -> Row -> Tc ()
unifyRows seen left right = do
  a@(Row af at) <- zonkRow left
  b@(Row bf bt) <- zonkRow right
  wellFormedRow a
  wellFormedRow b
  mapM_ (uncurry (unifySeen seen)) (M.elems (M.intersectionWith (,) af bf))
  let onlyA = af M.\\ bf
      onlyB = bf M.\\ af
      mismatch = failure ("record/variant fields do not match; extra or missing labels: " ++
        intercalate ", " (M.keys onlyA ++ M.keys onlyB))
  case (at,bt) of
    (Nothing,Nothing) -> unless (M.null onlyA && M.null onlyB) mismatch
    (Just x,Nothing) -> do
      unless (M.null onlyA) mismatch
      bindRow x (Row onlyB Nothing)
    (Nothing,Just y) -> do
      unless (M.null onlyB) mismatch
      bindRow y (Row onlyA Nothing)
    (Just x,Just y)
      | x == y -> unless (M.null onlyA && M.null onlyB) mismatch
      | otherwise -> do
          tailVar <- freshId
          bindRow x (Row onlyB (Just tailVar))
          bindRow y (Row onlyA (Just tailVar))

headType :: Type -> Tc Type
headType = go S.empty
  where
    go seen t = do
      t' <- zonk t
      case t' of
        recursive@(TRec v bodyType) -> go seen (substituteBound v recursive bodyType)
        TNamed n args -> do
          when (n `S.member` seen) $ failure ("unguarded recursive type synonym '" ++ n ++ "'")
          as <- gets aliases
          case M.lookup n as of
            Nothing -> failure ("unknown type '" ++ n ++ "'")
            Just (Alias params syntax) -> do
              unless (length params == length args) $ failure ("wrong number of type arguments for '" ++ n ++ "'")
              compiled <- compileWith (M.fromList (zip params args)) syntax
              go (S.insert n seen) compiled
        _ -> pure t'

unify :: Type -> Type -> Tc ()
unify = unifySeen S.empty

unifySeen :: Set (Type,Type) -> Type -> Type -> Tc ()
unifySeen seen left right = do
  a <- zonk left
  b <- zonk right
  unless (a == b || (a,b) `S.member` seen || (b,a) `S.member` seen) $ do
    let nextSeen = S.insert (a,b) seen
    case (a,b) of
      (TV v,t) -> bindType v t
      (t,TV v) -> bindType v t
      (TRec _ _,_) -> headType a >>= \t -> unifySeen nextSeen t b
      (_,TRec _ _) -> headType b >>= unifySeen nextSeen a
      (TNamed _ _,_) -> headType a >>= \t -> unifySeen nextSeen t b
      (_,TNamed _ _) -> headType b >>= unifySeen nextSeen a
      (TFun x y,TFun u v) -> unifySeen nextSeen x u >> unifySeen nextSeen y v
      (TRecord r,TRecord s) -> unifyRows nextSeen r s
      (TVariant r,TVariant s) -> unifyRows nextSeen r s
      _ -> failure ("type mismatch: " ++ prettyType a ++ " versus " ++ prettyType b)

asRecord :: Type -> Tc Row
asRecord t = do
  t' <- headType t
  case t' of
    TRecord r -> zonkRow r
    TV v -> do
      r <- freshRow
      bindType v (TRecord r)
      pure r
    _ -> failure ("only products of labeled atoms can be composed; got " ++ prettyType t')

functionParts :: Type -> Tc (Type,Type)
functionParts t = do
  t' <- headType t
  case t' of
    TFun a b -> pure (a,b)
    TV v -> do
      a <- freshType
      b <- freshType
      bindType v (TFun a b)
      pure (a,b)
    _ -> failure ("expected a function, got " ++ prettyType t')

compileType :: SType -> Tc Type
compileType syntax = gets annotationVars >>= \vars -> compileWith vars syntax

compileWith :: Map Name Type -> SType -> Tc Type
compileWith vars syntax = case syntax of
  SInt -> pure TInt
  SVoid -> pure (TVariant emptyRow)
  SUnit -> pure unitType
  SVar "_" -> freshType
  SVar n -> case M.lookup n vars of
    Just t -> pure t
    Nothing -> do
      existing <- gets (M.lookup n . annotationVars)
      case existing of
        Just t -> pure t
        Nothing -> do
          t <- freshType
          modify' (\s -> s {annotationVars = M.insert n t (annotationVars s)})
          pure t
  SName n args -> do
    as <- gets aliases
    case M.lookup n as of
      Nothing -> failure ("unknown type '" ++ n ++ "'")
      Just (Alias params _) -> unless (length params == length args) $
        failure ("wrong number of type arguments for '" ++ n ++ "'")
    TNamed n <$> mapM (compileWith vars) args
  SField n payload -> do
    t <- compileWith vars payload
    pure (TRecord (Row (M.singleton n t) Nothing))
  SProduct ts -> do
    rs <- mapM (compileWith vars >=> asRecord) ts
    TRecord <$> foldM combineType emptyRow rs
  SSum ts -> do
    rs <- mapM (compileWith vars >=> asSum) ts
    TVariant <$> foldM combineType emptyRow rs
  SArrow a b -> TFun <$> compileWith vars a <*> compileWith vars b
  SOpen t -> do
    Row fs rest <- compileWith vars t >>= asRecord
    case rest of
      Just _ -> pure (TRecord (Row fs rest))
      Nothing -> do
        tailVar <- freshId
        let r = Row fs (Just tailVar)
        wellFormedRow r
        pure (TRecord r)
  where
    asSum t = do
      t' <- headType t
      case t' of
        TVariant r -> pure r
        TRecord r@(Row fs Nothing) | M.size fs == 1 -> pure r
        _ -> failure "sum alternatives must be atoms or sums; mixing a multi-field product into a sum is not supported"

combineType :: Row -> Row -> Tc Row
combineType left right = do
  a@(Row af at) <- zonkRow left
  b@(Row bf bt) <- zonkRow right
  case (at,bt) of
    (Nothing,Nothing) -> do
      mapM_ (uncurry unify) (M.elems (M.intersectionWith (,) af bf))
      pure (Row (M.union af bf) Nothing)
    (Nothing,Just v) | M.null bf -> do
      mapM_ (`requireLacks` b) (M.keys af)
      pure (Row af (Just v))
    (Just v,Nothing) | M.null af -> do
      mapM_ (`requireLacks` a) (M.keys bf)
      pure (Row bf (Just v))
    _ -> do
      result <- freshRow
      emitConstraint (Merge Compatible a b result)
      pure result

assign :: Type -> Type -> Tc ()
assign = assignSeen S.empty

assignSeen :: Set (Type,Type) -> Type -> Type -> Tc ()
assignSeen seen actual expected = do
  originalA <- zonk actual
  originalB <- zonk expected
  unless (originalA == originalB || (originalA,originalB) `S.member` seen) $ do
    a <- headType originalA
    b <- headType originalB
    let nextSeen = S.insert (originalA,originalB) seen
    case (a,b) of
      (TRecord (Row fs Nothing),TVariant row) | M.size fs == 1 -> do
        let (label,payload) = M.findMin fs
        target <- lookupField label row
        assignSeen nextSeen payload target
      (TRecord ra,TRecord rb) -> do
        Row af at <- zonkRow ra
        right@(Row bf _) <- zonkRow rb
        mapM_ (uncurry (assignSeen nextSeen)) (M.elems (M.intersectionWith (,) af bf))
        -- Shape equality is still exact. Only payloads may be injected into
        -- their expected variants, recursively (e.g. the tail of a list).
        let checkedLeft = M.union (M.intersection bf af) (af M.\\ bf)
        unifyRows S.empty (Row checkedLeft at) right
      _ -> unify a b

lookupField :: Name -> Row -> Tc Type
lookupField name row = do
  Row fields rest <- zonkRow row
  case M.lookup name fields of
    Just t -> pure t
    Nothing -> case rest of
      Nothing -> failure ("missing field or alternative '" ++ name ++ "'")
      Just v -> do
        t <- freshType
        tailVar <- freshId
        bindRow v (Row (M.singleton name t) (Just tailVar))
        pure t

instantiate :: Scheme -> Tc Type
instantiate (Scheme vars cs t) = do
  replacements <- mapM (const freshId) vars
  let renaming = M.fromList (zip vars replacements)
  mapM_ (emitConstraint . renameConstraint renaming) cs
  pure (renameType renaming t)

bindPattern :: Pattern -> Type -> Tc TypeEnv
bindPattern pat expected = case pat of
  PVar n -> pure (M.singleton n (Scheme [] [] expected))
  PWildcard -> pure M.empty
  PInt _ -> unify expected TInt >> pure M.empty
  PUnit -> unify expected unitType >> pure M.empty
  PAnn p syntax -> do
    annotation <- compileType syntax
    unify expected annotation
    bindPattern p annotation
  PField n p -> do
    t <- freshType
    unify expected (TRecord (Row (M.singleton n t) Nothing))
    bindPattern p t
  PProduct ps -> do
    let flattened = concatMap flatten ps
        fields = [(n,p) | PField n p <- flattened]
        remainders = [p | p <- flattened, not (isField p), p /= PUnit]
    when (length remainders > 1) $ failure "a product pattern may have only one remainder pattern"
    when (length fields /= S.size (S.fromList (map fst fields))) $ failure "duplicate label in pattern"
    types <- mapM (const freshType) fields
    tailVar <- if null remainders then pure Nothing else Just <$> freshId
    let row = Row (M.fromList (zip (map fst fields) types)) tailVar
    wellFormedRow row
    unify expected (TRecord row)
    bindings <- zipWithM (\(_,p) t -> bindPattern p t) fields types
    restBindings <- case (remainders,tailVar) of
      ([p],Just v) -> (:[]) <$> bindPattern p (TRecord (Row M.empty (Just v)))
      _ -> pure []
    combineBindings (bindings ++ restBindings)
  where
    flatten = \case
      PProduct xs -> concatMap flatten xs
      p -> [p]
    isField = \case
      PField _ _ -> True
      _ -> False

combineBindings :: [TypeEnv] -> Tc TypeEnv
combineBindings = foldM step M.empty
  where step a b = do
          unless (M.null (M.intersection a b)) $ failure "duplicate variable binding in pattern"
          pure (M.union a b)

infer :: TypeEnv -> Expr -> Tc Type
infer env expr = case expr of
  EInt _ -> pure TInt
  EUnit -> pure unitType
  EVar n -> maybe (failure ("unbound value '" ++ n ++ "'")) instantiate (M.lookup n env)
  EField n e -> do
    t <- infer env e
    pure (TRecord (Row (M.singleton n t) Nothing))
  EProduct es -> do
    rs <- mapM (infer env >=> asRecord) es
    TRecord <$> foldM mergeValue emptyRow rs
  EProject e n -> infer env e >>= asRecord >>= lookupField n
  ELambda p e -> do
    arg <- freshType
    bindings <- bindPattern p arg
    result <- infer (M.union bindings env) e
    pure (TFun arg result)
  EApply f x -> do
    function <- infer env f
    (arg,result) <- functionParts function
    check env x arg
    solve
    pure result
  EAnn e syntax -> do
    t <- compileType syntax
    check env e t
    pure t
  EBinary op a b -> do
    check env a TInt
    check env b TInt
    pure (if op `elem` ["==","!=","<",">","<=",">="] then boolType else TInt)
  EIf condition yes no -> do
    check env condition boolType
    a <- infer env yes
    b <- infer env no
    joinTypes a b
  EMatch subject cases -> inferMatch env subject cases Nothing

check :: TypeEnv -> Expr -> Type -> Tc ()
check env expr expected = case expr of
  ELambda p bodyExpr -> do
    (arg,result) <- functionParts expected
    bindings <- bindPattern p arg
    check (M.union bindings env) bodyExpr result
  EMatch subject cases -> do
    t <- headType expected
    case t of
      TV _ -> inferMatch env subject cases Nothing >>= (`assign` expected)
      _ -> void (inferMatch env subject cases (Just expected))
  EIf condition yes no -> do
    t <- headType expected
    case t of
      TV _ -> infer env expr >>= (`assign` expected)
      _ -> check env condition boolType >> check env yes expected >> check env no expected
  EField label payload -> do
    target <- headType expected
    case target of
      TVariant row -> lookupField label row >>= check env payload
      _ -> infer env expr >>= (`assign` expected)
  _ -> infer env expr >>= (`assign` expected)

joinTypes :: Type -> Type -> Tc Type
joinTypes left right = do
  a <- headType left
  b <- headType right
  case (a,b) of
    (TRecord ra@(Row af Nothing),TRecord rb@(Row bf Nothing))
      | M.size af == 1 && M.size bf == 1 && M.keys af /= M.keys bf -> TVariant <$> combineType ra rb
    (TVariant ra,TRecord rb@(Row bf Nothing)) | M.size bf == 1 -> TVariant <$> combineType ra rb
    (TRecord ra@(Row af Nothing),TVariant rb) | M.size af == 1 -> TVariant <$> combineType ra rb
    (TVariant ra,TVariant rb) -> TVariant <$> combineType ra rb
    _ -> unify left right >> pure left

inferMatch :: TypeEnv -> Expr -> [(Pattern,Expr)] -> Maybe Type -> Tc Type
inferMatch env subject cases target = do
  when (null cases) $ failure "empty match"
  input <- infer env subject
  inputHead <- headType input
  let labels = [n | (PField n _,_) <- cases]
      catchesAll = any (\(p,_) -> case p of PVar _ -> True; PWildcard -> True; _ -> False) cases
  variant <- case inputHead of
    TVariant r -> pure (Just r)
    TV v | not (null labels) -> do
      payloads <- mapM (const freshType) labels
      let r = Row (M.fromList (zip labels payloads)) Nothing
      bindType v (TVariant r)
      pure (Just r)
    TRecord r@(Row fs Nothing) | M.size fs == 1 && not (null labels) -> do
      payloads <- mapM (const freshType) labels
      let alternatives = Row (M.fromList (zip labels payloads)) Nothing
      assign (TRecord r) (TVariant alternatives)
      pure (Just alternatives)
    _ -> pure Nothing
  outputs <- forM cases $ \(p,e) -> do
    bindings <- case (variant,p) of
      (Just r,PField n payload) -> lookupField n r >>= bindPattern payload
      _ -> bindPattern p input
    case target of
      Just t -> check (M.union bindings env) e t >> pure t
      Nothing -> infer (M.union bindings env) e
  -- First type the patterns: a unit pattern can determine a fresh payload's
  -- type, so coverage must be checked after these constraints are known.
  case variant of
    Just row -> do
      Row fields rest <- zonkRow row
      unless catchesAll $ do
        unless (rest == Nothing) $ failure "matching an open sum requires a catch-all pattern"
        covered <- forM [(n,p) | (PField n p,_) <- cases] $ \(n,p) -> do
          payload <- lookupField n row
          complete <- irrefutable p payload
          pure [n | complete]
        unless (M.keysSet fields `S.isSubsetOf` S.fromList (concat covered)) $ failure "non-exhaustive match"
    Nothing -> unless catchesAll $ failure "matching integers or records requires a catch-all pattern"
  case target of
    Just t -> pure t
    Nothing -> case outputs of
      first:rest -> foldM joinTypes first rest
      [] -> failure "empty match"

-- Seeing a tag is insufficient: `some = 0` does not cover `some = 1`.
-- This conservative check accepts a tag only when its payload pattern covers
-- every payload; several integer patterns alone can never exhaust int.
irrefutable :: Pattern -> Type -> Tc Bool
irrefutable pat expected = case pat of
  PVar _ -> pure True
  PWildcard -> pure True
  PInt _ -> pure False
  PAnn p _ -> irrefutable p expected
  PUnit -> do
    t <- headType expected
    pure (t == unitType)
  PField n p -> do
    t <- headType expected
    case t of
      TRecord (Row fs Nothing) | M.keys fs == [n] -> irrefutable p (fs M.! n)
      _ -> pure False
  PProduct ps -> do
    t <- headType expected
    case t of
      TRecord (Row fs rest) -> do
        let fields = [(n,p) | PField n p <- ps]
            remainder = [p | p <- ps, case p of PField _ _ -> False; PUnit -> False; _ -> True]
        complete <- and <$> mapM (\(n,p) -> maybe (pure False) (irrefutable p) (M.lookup n fs)) fields
        let hasRemainder = case remainder of [PVar _] -> True; [PWildcard] -> True; _ -> False
        pure (complete && (hasRemainder || (rest == Nothing && M.keysSet fs == S.fromList (map fst fields))))
      _ -> pure False

mergeValue :: Row -> Row -> Tc Row
mergeValue a b = do
  result <- freshRow
  emitConstraint (Merge Disjoint a b result)
  solve
  zonkRow result

-- Qualified HM inference retains an unsolved merge in the function scheme.
-- At an application, a known full row and one known fragment determine the
-- other fragment. Compatible type composition deliberately has no such inverse.
solve :: Tc ()
solve = do
  before <- gets revision
  pending <- gets constraints
  modify' (\s -> s {constraints = []})
  remaining <- fmap concat $ forM pending $ \c -> do
    c' <- zonkConstraint c
    done <- solveOne c'
    pure [c' | not done]
  generated <- gets constraints
  modify' (\s -> s {constraints = remaining ++ generated})
  after <- gets revision
  when (after /= before) solve

solveOne :: Constraint -> Tc Bool
solveOne (Lacks label row) = requireLacks label row >> pure True
solveOne (Merge mode a@(Row af at) b@(Row bf bt) out@(Row ofields ot)) = do
  let common = M.intersectionWith (,) af bf
  if mode == Disjoint
    then do
      unless (M.null common) $ failure ("duplicate label in value composition: " ++ intercalate ", " (M.keys common))
      mapM_ (`requireLacks` b) (M.keys af)
      mapM_ (`requireLacks` a) (M.keys bf)
    else mapM_ (uncurry unify) (M.elems common)
  case (at,bt) of
    (Nothing,Nothing) -> unifyRows S.empty out (Row (M.union af bf) Nothing) >> pure True
    (Nothing,_) | M.null af -> unifyRows S.empty b out >> pure True
    (_,Nothing) | M.null bf -> unifyRows S.empty a out >> pure True
    (Nothing,_) | mode == Disjoint && ot == Nothing -> split af b ofields
    (_,Nothing) | mode == Disjoint && ot == Nothing -> split bf a ofields
    _ -> pure False
  where
    split known unknown full = do
      unless (M.keysSet known `S.isSubsetOf` M.keysSet full) $ failure "provided fields are not accepted by the function"
      mapM_ (uncurry unify) (M.elems (M.intersectionWith (,) known full))
      unifyRows S.empty unknown (Row (full M.\\ known) Nothing)
      pure True

generalize :: TypeEnv -> Type -> Tc Scheme
generalize env t = do
  solve
  t' <- zonk t
  cs <- gets constraints >>= mapM zonkConstraint
  env' <- mapM zonkScheme env
  let envFree = S.unions (map freeScheme (M.elems env'))
      allFree = freeType t' `S.union` S.unions (map freeConstraint cs)
      quantified = allFree S.\\ envFree
  lacks <- gets absentLabels
  let restrictions = [Lacks l (Row M.empty (Just v)) | v <- S.toList quantified,
                         l <- S.toList (M.findWithDefault S.empty v lacks)]
  modify' (\s -> s {constraints = []})
  pure (Scheme (S.toAscList quantified) (cs ++ restrictions) t')

-- Signature variables are universally quantified, not holes that a body may
-- specialize. We check after solving that each still denotes an independent
-- variable of its original kind (including open row tails).
signatureVariables :: Type -> (Set Variable, Set Variable)
signatureVariables = \case
  TInt -> (S.empty,S.empty)
  TV v -> (S.singleton v,S.empty)
  TFun a b -> unionKinds (signatureVariables a) (signatureVariables b)
  TNamed _ ts -> foldr (unionKinds . signatureVariables) (S.empty,S.empty) ts
  TRec v bodyType -> let (types,rows) = signatureVariables bodyType in (S.delete v types,rows)
  TRecord r -> rowKinds r
  TVariant r -> rowKinds r

rowKinds :: Row -> (Set Variable, Set Variable)
rowKinds (Row fields rest) =
  foldr (unionKinds . signatureVariables) (S.empty,maybe S.empty S.singleton rest) (M.elems fields)

unionKinds :: (Set Variable,Set Variable) -> (Set Variable,Set Variable) -> (Set Variable,Set Variable)
unionKinds (a,b) (c,d) = (a `S.union` c,b `S.union` d)

verifySignature :: (Set Variable,Set Variable) -> Tc ()
verifySignature (types,rows) = do
  solve
  typeIds <- forM (S.toList types) $ \v -> do
    t <- zonk (TV v)
    case t of
      TV w -> pure w
      _ -> failure "polymorphic signature is more general than its implementation"
  rowIds <- forM (S.toList rows) $ \v -> do
    r <- zonkRow (Row M.empty (Just v))
    case r of
      Row fs (Just w) | M.null fs -> pure w
      _ -> failure "open-row signature is more general than its implementation"
  let ids = typeIds ++ rowIds
  unless (length ids == S.size (S.fromList ids)) $
    failure "independent signature variables were unified by the implementation"

-- Only cycles outside a labeled payload are rejected. Recursive list aliases
-- remain finite syntax and are compared coinductively by unifySeen.
validateAliases :: Aliases -> Tc ()
validateAliases as = mapM_ (visit S.empty) (M.keys as)
  where
    visit seen n = do
      when (n `S.member` seen) $ failure ("unguarded recursive type synonym '" ++ n ++ "'")
      case M.lookup n as of
        Nothing -> failure ("unknown type '" ++ n ++ "'")
        Just (Alias params syntax) -> do
          unless (length params == S.size (S.fromList params)) $ failure ("duplicate type parameter in '" ++ n ++ "'")
          checkNames n (S.fromList params) syntax
          mapM_ (visit (S.insert n seen)) (unguarded syntax)
    unguarded = \case
      SName n ts -> n : concatMap unguarded ts
      SProduct ts -> concatMap unguarded ts
      SSum ts -> concatMap unguarded ts
      SArrow a b -> unguarded a ++ unguarded b
      SOpen t -> unguarded t
      _ -> []
    checkNames owner bound syntax = case syntax of
      SVar n -> unless (n == "_" || n `S.member` bound) $ failure ("unbound type parameter '" ++ n ++ "'")
      SName n ts -> do
        case M.lookup n as of
          Nothing -> failure ("unknown type '" ++ n ++ "'")
          Just (Alias ps _) -> unless (length ps == length ts) $ failure ("wrong number of type arguments for '" ++ n ++ "'")
        when (reaches S.empty n owner && not (all (simpleParameter bound) ts)) $
          failure "non-regular recursive aliases are not supported; recursive arguments must be type parameters"
        mapM_ (checkNames owner bound) ts
      SField _ t -> checkNames owner bound t
      SProduct ts -> mapM_ (checkNames owner bound) ts
      SSum ts -> mapM_ (checkNames owner bound) ts
      SArrow a b -> checkNames owner bound a >> checkNames owner bound b
      SOpen t -> checkNames owner bound t
      _ -> pure ()
    simpleParameter bound (SVar n) = n `S.member` bound
    simpleParameter _ _ = False
    reaches seen from target
      | from == target = True
      | from `S.member` seen = False
      | otherwise = case M.lookup from as of
          Nothing -> False
          Just (Alias _ t) -> any (\n -> reaches (S.insert from seen) n target) (references t)
    references = \case
      SName n ts -> n : concatMap references ts
      SField _ t -> references t
      SProduct ts -> concatMap references ts
      SSum ts -> concatMap references ts
      SArrow a b -> references a ++ references b
      SOpen t -> references t
      _ -> []

inferProgram :: Program -> Either TypeError Inference
inferProgram (Program decls) = do
  as <- foldM collect M.empty decls
  evalStateT (do
    validateAliases as
    -- Validate even unused aliases, without recursively expanding payloads.
    forM_ (M.toList as) $ \(_,Alias params syntax) -> do
      modify' (\s -> s {annotationVars = M.empty})
      args <- mapM (const freshType) params
      void (compileWith (M.fromList (zip params args)) syntax)
      solve
      pending <- gets constraints
      unless (null pending) $ failure "type aliases with abstract product composition are not supported yet"
    (env,signatures) <- foldM declarationStep (M.empty,M.empty) decls
    unless (M.null signatures) $ failure ("signature without definition: " ++ intercalate ", " (M.keys signatures))
    pure (Inference env as)) (initialState as)
  where
    collect acc (DType n ps t)
      | M.member n acc = Left (TypeError ("duplicate type declaration '" ++ n ++ "'"))
      | otherwise = Right (M.insert n (Alias ps t) acc)
    collect acc _ = Right acc
    declarationStep (env,sigs) decl = case decl of
      DType {} -> pure (env,sigs)
      DSignature n t -> do
        when (M.member n sigs || M.member n env) $ failure ("duplicate signature or value '" ++ n ++ "'")
        pure (env,M.insert n t sigs)
      DValue n args resultAnnotation bodyExpr -> do
        when (M.member n env) $ failure ("duplicate value declaration '" ++ n ++ "'")
        modify' (\s -> s {annotationVars = M.empty, constraints = []})
        let valueExpr = lambdaArgs args (maybe bodyExpr (EAnn bodyExpr) resultAnnotation)
        when (n `S.member` freeValues valueExpr && not (isFunction valueExpr)) $
          failure "recursive value definitions must be functions"
        let declaredSignature = case M.lookup n sigs of
              Just syntax -> Just syntax
              Nothing -> if null args then resultAnnotation else Nothing
        expected <- maybe freshType compileType declaredSignature
        normalizedSignature <- zonk expected
        let signatureKinds = signatureVariables normalizedSignature
        let recursiveEnv = M.insert n (Scheme [] [] expected) env
        check recursiveEnv valueExpr expected
        case declaredSignature of
          Just _ -> verifySignature signatureKinds
          Nothing -> pure ()
        scheme <- generalize env expected
        pure (M.insert n scheme env,M.delete n sigs)

inferExpression :: Inference -> Expr -> Either TypeError Scheme
inferExpression context expr = evalStateT action start
  where
    allIds = S.unions [S.fromList vs `S.union` allTypeVariables t `S.union` S.unions (map allConstraintVariables cs)
                     | Scheme vs cs t <- M.elems (inferredTypes context)]
    start = (initialState (inferredAliases context)) {nextId = maybe 0 (+1) (S.lookupMax allIds)}
    action = infer (inferredTypes context) expr >>= generalize (inferredTypes context)

isFunction :: Expr -> Bool
isFunction = \case
  ELambda _ _ -> True
  EAnn e _ -> isFunction e
  _ -> False

freeValues :: Expr -> Set Name
freeValues expression = case expression of
  EInt _ -> S.empty
  EUnit -> S.empty
  EVar n -> S.singleton n
  EField _ e -> freeValues e
  EProduct es -> S.unions (map freeValues es)
  EProject e _ -> freeValues e
  ELambda p e -> freeValues e S.\\ patternBindings p
  EApply f x -> freeValues f `S.union` freeValues x
  EIf c a b -> S.unions (map freeValues [c,a,b])
  EMatch e cases -> freeValues e `S.union` S.unions [freeValues rhs S.\\ patternBindings p | (p,rhs) <- cases]
  EBinary _ a b -> freeValues a `S.union` freeValues b
  EAnn e _ -> freeValues e

patternBindings :: Pattern -> Set Name
patternBindings = \case
  PVar n -> S.singleton n
  PField _ p -> patternBindings p
  PProduct ps -> S.unions (map patternBindings ps)
  PAnn p _ -> patternBindings p
  _ -> S.empty
