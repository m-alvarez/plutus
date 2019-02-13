{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module TestLib where

import           Common
import           Control.Exception
import           Control.Monad.Except
import           PlcTestUtils
import           PlutusPrelude                hiding ((</>))

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

-- Sadly necessary: since parseQuoted returns Quote (Either Error a), and there's no good way
-- of commutting Quote and Either, we just throw an exception inside the Quote and immediately
-- catch it outside.
parseQuotedExcept :: Parser a -> String -> T.Text -> IO (Either Parser.Error (Quote a))
parseQuotedExcept parser name = try . return . fmap throwIfError . parseQuoted parser name
    where throwIfError = either throw id

goldenPir :: Pretty a => String -> a -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ pretty value

withGoldenFileM :: String -> (T.Text -> IO T.Text) -> TestNested
withGoldenFileM name op = do
    currentPath <- Reader.ask
    let filename = foldr (</>) (name ++ ".plc") currentPath
    nestedGoldenVsTextM name (op =<< T.readFile filename)

withGoldenFile :: String -> (T.Text -> T.Text) -> TestNested
withGoldenFile name op = withGoldenFileM name (return . op)

goldenPir' :: Pretty b => (a -> b) -> Parser a -> String -> TestNested
goldenPir' op = goldenPirQ (return . op . runQuote)

goldenPirQ :: Pretty b => (Quote a -> IO b) -> Parser a -> String -> TestNested
goldenPirQ op parser name = withGoldenFileM name parseOrError
    where parseOrError src = either (return . T.pack . parseErrorPretty) (fmap prettyText . op)
                             =<< parseQuotedExcept parser name src

ppThrow :: PrettyBy PrettyConfigPlc a => ExceptT SomeException IO a -> IO T.Text
ppThrow = fmap docText . rethrow . fmap prettyPlcClassicDebug

goldenPlc' :: (GetProgram (Quote a)) => Parser a -> String -> TestNested
goldenPlc' = goldenPirQ (\ast -> ppThrow $ do
                                p <- getProgram ast
                                withExceptT toException $ PLC.deBruijnProgram p)

goldenEval' :: (GetProgram (Quote a)) => Parser a -> String -> TestNested
goldenEval' = goldenPirQ (\ast -> ppThrow $ runPlc [ast])

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
