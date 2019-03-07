{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR terms into PLC.
module Language.PlutusIR.Compiler.Term (compileTerm) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Datatype
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Recursion
import           Language.PlutusIR.Compiler.Types

import           Control.Monad
import           Control.Monad.Error.Lens
import           Control.Monad.Reader

import qualified Language.PlutusCore                   as PLC
import qualified Language.PlutusCore.MkPlc             as PLC

import           Data.List

-- | Compile a 'Term' into a PLC Term. Note: the result does *not* have globally unique names.
compileTerm :: Compiling m e a => PIRTerm a -> m (PLCTerm a)
compileTerm = \case
    Let p r bs body -> local (const $ LetBinding r p) $ do
        body' <- compileTerm body
        case r of
            NonRec -> compileNonRecBindings r body' bs
            Rec    -> compileRecBindings r body' bs
    Var x n -> pure $ PLC.Var x n
    TyAbs x n k t -> PLC.TyAbs x n k <$> compileTerm t
    LamAbs x n ty t -> PLC.LamAbs x n ty <$> compileTerm t
    Apply x t1 t2 -> PLC.Apply x <$> compileTerm t1 <*> compileTerm t2
    Constant x c -> pure $ PLC.Constant x c
    Builtin x bi -> pure $ PLC.Builtin x bi
    TyInst x t ty -> PLC.TyInst x <$> compileTerm t <*> pure ty
    Error x ty -> pure $ PLC.Error x ty
    IWrap x tn ty t -> PLC.IWrap x tn ty <$> compileTerm t
    Unwrap x t -> PLC.Unwrap x <$> compileTerm t

-- | Removes all the recursive term and type bindings in a 'Term' (but not Datatype bindings)
eliminateRecBindings :: Compiling m e a => PIRTerm a -> m (PIRTerm a)
eliminateRecBindings = \case
    Let p r bs body -> do
        body' <- eliminateRecBindings body
        case r of
            Rec -> local (const $ LetBinding r p) $ compileRecBindings' body' bs
            NonRec -> do
                bs' <- sequence $ map elimBody bs
                pure $ Let p r bs' body'
        where elimBody (TermBind p v t)     = TermBind p v <$> eliminateRecBindings t
              elimBody b@(TypeBind _ _ _)   = pure b
              elimBody b@(DatatypeBind _ _) = pure b
    Var x n -> pure $ Var x n
    TyAbs x n k t -> TyAbs x n k <$> eliminateRecBindings t
    LamAbs x n ty t -> LamAbs x n ty <$> eliminateRecBindings t
    Apply x t1 t2 -> Apply x <$> eliminateRecBindings t1 <*> eliminateRecBindings t2
    t@(Constant x c) -> pure t
    t@(Builtin x bi) -> pure t
    TyInst x t ty -> TyInst x <$> eliminateRecBindings t <*> pure ty
    Error x ty -> pure $ Error x ty
    IWrap x tn ty t -> IWrap x tn ty <$> eliminateRecBindings t
    Unwrap x t -> Unwrap x <$> eliminateRecBindings t

compileNonRecBindings :: Compiling m e a => Recursivity -> PLCTerm a -> [Binding TyName Name (Provenance a)] -> m (PLCTerm a)
compileNonRecBindings r = foldM (compileSingleBinding r)

compileRecBindings :: Compiling m e a => Recursivity -> PLCTerm a -> [Binding TyName Name (Provenance a)] -> m (PLCTerm a)
compileRecBindings r body bs =
    let
        partitionBindings = partition (\case { TermBind {} -> True ; _ -> False; })
        (termBinds, typeBinds) = partitionBindings bs
    in do
        tysBound <- compileRecTypeBindings r body typeBinds
        compileRecTermBindings r tysBound termBinds

compileRecBindings' :: Compiling m e a => PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileRecBindings' body bs =
    let (termBinds, otherBinds) = partition (\case { TermBind {} -> True; _ -> False }) bs
        typeBinds = filter (\case {TypeBind {} -> True; _ -> False}) otherBinds
    in do
        tysBound <- compileRecTypeBindings' body typeBinds
        compileRecTermBindings' tysBound termBinds

compileRecTermBindings :: Compiling m e a => Recursivity -> PLCTerm a -> [Binding TyName Name (Provenance a)] -> m (PLCTerm a)
compileRecTermBindings _ body bs = case bs of
    [] -> pure body
    _ -> do
        binds <- forM bs $ \case
            TermBind _ vd rhs -> pure $ PLC.Def vd rhs
            _ -> ask >>= \p -> throwing _Error $ CompilationError p "Internal error: type binding in term binding group"
        compileRecTerms body binds

compileRecTermBindings' :: Compiling m e a => PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileRecTermBindings' body bs = case bs of
    [] -> pure body
    _  -> do
        binds <- forM bs $ \case
            TermBind _ vd rhs -> pure $ (vd, rhs)
            _ -> ask >>= \p -> throwing _Error $ CompilationError p "Internal error: type binding in term binding group"
        compileRecTerms' body binds

compileRecTypeBindings :: Compiling m e a => Recursivity -> PLCTerm a -> [Binding TyName Name (Provenance a)] -> m (PLCTerm a)
compileRecTypeBindings r body bs = case bs of
    []  -> pure body
    [b] -> compileSingleBinding r body b
    _   -> ask >>= \p -> throwing _Error $ UnsupportedError p "Mutually recursive datatypes"

compileRecTypeBindings' :: Compiling m e a => PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileRecTypeBindings' body bs = case bs of
    []  -> pure body
    [b] -> compileSingleBinding' Rec body b
    _   -> ask >>= \p -> throwing _Error $ UnsupportedError p "Mutually recursive types are not supported"

compileSingleBinding :: Compiling m e a => Recursivity -> PLCTerm a -> Binding TyName Name (Provenance a) ->  m (PLCTerm a)
compileSingleBinding r body b =  case b of
    TermBind x d rhs -> local (const x) $ case r of
        Rec -> compileRecTerms body [PLC.Def d rhs]
        NonRec -> local (TermBinding (varDeclNameString d)) $ do
            def <- PLC.Def d <$> compileTerm rhs
            PLC.mkTermLet <$> ask <*> pure def <*> pure body
    TypeBind x d rhs -> local (const x) $ local (TypeBinding (tyVarDeclNameString d)) $ do
        let def = PLC.Def d rhs
        PLC.mkTypeLet <$> ask <*> pure def <*> pure body
    DatatypeBind x d -> local (const x) $ local (TypeBinding (datatypeNameString d)) $
        compileDatatype r body d

compileSingleBinding' :: Compiling m e a => Recursivity -> PIRTerm a -> Binding TyName Name (Provenance a) ->  m (PIRTerm a)
compileSingleBinding' r body b =  case b of
    TermBind x d@(VarDecl x2 name ty) rhs -> local (const x) $ case r of
        Rec -> compileRecTerms' body [(d, rhs)]
        NonRec -> local (TermBinding (varDeclNameString d)) $
            Apply <$> ask <*> pure (LamAbs x2 name ty body) <*> pure rhs
    TypeBind x d@(TyVarDecl x2 name k) rhs -> local (const x) $ local (TypeBinding (tyVarDeclNameString d)) $
        TyInst <$> ask <*> pure (TyAbs x2 name k body) <*> pure rhs
    DatatypeBind x d -> local (const x) $ local (TypeBinding (datatypeNameString d)) $
        compileDatatype' r body d

{- WIP

-- | Remove all the non-recursive bindings in a 'Term'
eliminateNonRecBindings :: Compiling m e a => PIRTerm a -> m (PIRTerm a)
eliminateNonRecBindings = \case
    Let p r bs body -> do
        body' <- eliminateNonRecBindings body
        case r of
            NonRec -> local (const $ LetBinding r p) $ compileNonRecBindings' r body' bs
            Rec    -> do
                bs' <- sequence $ map elimBody bs
                pure $ Let p r bs' body'
        where elimBody (TermBind p v t) = TermBind p v <$> eliminateNonRecBindings t
              elimBody b@(TypeBind _ _ _) = pure b
              elimBody b@(DatatypeBind _ _) = pure b
    Var x n -> pure $ Var x n
    TyAbs x n k t -> TyAbs x n k <$> eliminateNonRecBindings t
    LamAbs x n ty t -> LamAbs x n ty <$> eliminateNonRecBindings t
    Apply x t1 t2 -> Apply x <$> eliminateNonRecBindings t1 <*> eliminateNonRecBindings t2
    t@(Constant x c) -> pure t
    t@(Builtin x bi) -> pure t
    TyInst x t ty -> TyInst x <$> eliminateNonRecBindings t <*> pure ty
    Error x ty -> pure $ Error x ty
    IWrap x tn ty t -> IWrap x tn ty <$> eliminateNonRecBindings t
    Unwrap x t -> Unwrap x <$> eliminateNonRecBindings t

compileNonRecBindings' :: Compiling m e a => Recursivity -> PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileNonRecBindings' r = foldM compileNonRecBinding


compileNonRecBinding :: Compiling m e a => PIRTerm a -> Binding TyName Name (Provenance a) ->  m (PIRTerm a)
compileNonRecBinding body b = case b of
    TermBind x d@(VarDecl x2 name ty) rhs -> local (const x) $ local (TermBinding (varDeclNameString d)) $
        Apply <$> ask <*> pure (LamAbs x2 name ty body) <*> pure rhs
    TypeBind x d@(TyVarDecl x2 name k) rhs -> local (const x) $ local (TypeBinding (tyVarDeclNameString d)) $
        TyInst <$> ask <*> pure (TyAbs x2 name k body) <*> pure rhs
    DatatypeBind _ _ ->
        ask >>= \p -> throwing _Error $ CompilationError p "Datatype binding found in non-recursive let elimination phase"
-}
