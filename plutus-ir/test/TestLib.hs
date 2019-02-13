{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module TestLib where

import           Common
import           PlcTestUtils
import           PlutusPrelude                hiding ((</>))

import           Control.Exception
import           Control.Monad.Except
import qualified Control.Monad.Reader         as Reader

import qualified Language.PlutusCore.DeBruijn as PLC
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusIR
import           Language.PlutusIR.Parser     as Parser

import           System.FilePath              ((</>))

import           Text.Megaparsec.Error        as Megaparsec

import qualified Data.Text                    as T
import qualified Data.Text.IO                 as T

withGoldenFileM :: String -> (T.Text -> IO T.Text) -> TestNested
withGoldenFileM name op = do
    currentPath <- Reader.ask
    let filename = foldr (</>) (name ++ ".plc") currentPath
    nestedGoldenVsTextM name (op =<< T.readFile filename)

goldenPir :: Pretty b => (a -> b) -> Parser a -> String -> TestNested
goldenPir op = goldenPirM (return . op)

goldenPirM :: Pretty b => (a -> IO b) -> Parser a -> String -> TestNested
goldenPirM op parser name = withGoldenFileM name parseOrError
    where parseOrError = either (return . T.pack . parseErrorPretty) (fmap prettyText . op)
                         . parse parser name

ppThrow :: PrettyBy PrettyConfigPlc a => ExceptT SomeException IO a -> IO T.Text
ppThrow = fmap docText . rethrow . fmap prettyPlcClassicDebug

goldenPlcFromPir :: GetProgram a => Parser a -> String -> TestNested
goldenPlcFromPir = goldenPirM (\ast -> ppThrow $ do
                                p <- getProgram ast
                                withExceptT toException $ PLC.deBruijnProgram p)

ppCatch :: PrettyPlc a => ExceptT SomeException IO a -> IO T.Text
ppCatch value = docText <$> (either (pretty . show) prettyPlcClassicDebug <$> runExceptT value)

goldenPlcFromPirCatch :: GetProgram a => Parser a -> String -> TestNested
goldenPlcFromPirCatch = goldenPirM (\ast -> ppCatch $ do
                                           p <- getProgram ast
                                           withExceptT toException $ PLC.deBruijnProgram p)

goldenEvalPir :: (GetProgram a) => Parser a -> String -> TestNested
goldenEvalPir = goldenPirM (\ast -> ppThrow $ runPlc [ast])

maybeDatatype :: Quote (Datatype TyName Name ())
maybeDatatype = do
    m <- freshTyName () "Maybe"
    a <- freshTyName () "a"
    match <- freshName () "match_Maybe"
    nothing <- freshName () "Nothing"
    just <- freshName () "Just"

    pure $
        Datatype ()
            (TyVarDecl () m (KindArrow () (Type ()) (Type ())))
            [
                TyVarDecl () a (Type ())
            ]
        match
        [
            VarDecl () nothing (TyApp () (TyVar () m) (TyVar () a)),
            VarDecl () just (TyFun () (TyVar () a) (TyApp () (TyVar () m) (TyVar () a)))
        ]

listDatatype :: Quote (Datatype TyName Name ())
listDatatype = do
    m <- freshTyName () "List"
    a <- freshTyName () "a"
    let ma = TyApp () (TyVar () m) (TyVar () a)
    match <- freshName () "match_List"
    nil <- freshName () "Nil"
    cons <- freshName () "Cons"

    pure $
        Datatype ()
            (TyVarDecl () m (KindArrow () (Type ()) (Type ())))
            [
                TyVarDecl () a (Type ())
            ]
        match
        [
            VarDecl () nil ma,
            VarDecl () cons (TyFun () (TyVar () a) (TyFun () ma ma))
        ]

treeForestDatatype :: Quote (Datatype TyName Name (), Datatype TyName Name ())
treeForestDatatype = do
    tree <- freshTyName () "Tree"
    a <- freshTyName () "a"
    let treeA arg = TyApp () (TyVar () tree) (TyVar () arg)
    node <- freshName () "Node"
    matchTree <- freshName () "match_Tree"

    forest <- freshTyName () "Forest"
    a2 <- freshTyName () "a"
    let forestA arg = TyApp () (TyVar () forest) (TyVar () arg)
    nil <- freshName () "Nil"
    cons <- freshName () "Cons"
    matchForest <- freshName () "match_Forest"

    let treeDt = Datatype ()
          (TyVarDecl () tree (KindArrow () (Type ()) (Type ())))
          [
              TyVarDecl () a (Type ())
          ]
          matchTree
          [
              VarDecl () node (TyFun () (TyVar () a) (TyFun () (forestA a) (treeA a)))
          ]
    let forestDt = Datatype ()
          (TyVarDecl () forest (KindArrow () (Type ()) (Type ())))
          [
              TyVarDecl () a2 (Type ())
          ]
          matchForest
          [
              VarDecl () nil (forestA a2),
              VarDecl () cons (TyFun () (treeA a2) (TyFun () (forestA a2) (forestA a2)))
          ]
    pure (treeDt, forestDt)
