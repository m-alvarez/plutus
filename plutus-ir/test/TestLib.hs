{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
module TestLib where

import           Common
import           Control.Exception
import           Control.Monad.Except
import           PlutusPrelude             hiding ((</>))

import qualified Control.Monad.Reader      as Reader

import           Language.PlutusCore.Quote
import           Language.PlutusIR
import           Language.PlutusIR.Parser  as Parser

import           System.FilePath           ((</>))

import           Text.Megaparsec.Error     as Megaparsec

import qualified Data.Text                 as T
import qualified Data.Text.IO              as T

goldenPir :: Pretty a => String -> a -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ pretty value

goldenParse :: Pretty b => (a -> b) -> Parser a -> String -> TestNested
goldenParse op parser name = do
    currentPath <- Reader.ask
    let filename = foldr (</>) (name ++ ".plc") currentPath
        result = do
                code <- T.readFile filename
                return $ case parse parser name code of
                    Left err  -> T.pack $ parseErrorPretty err
                    Right ast -> prettyText $ op ast
    nestedGoldenVsTextM name result

goldenParseGetProgram :: Pretty b => (Quote a -> ExceptT SomeException IO b) -> Parser a -> String -> TestNested
goldenParseGetProgram op parser name = do
    currentPath <- Reader.ask
    let filename = foldr (</>) (name ++ ".plc") currentPath
        result = do
                code <- T.readFile filename
                output <- try $ runExceptT $ op $ throwIfError <$> parseQuoted parser name code
                          :: IO (Either (Megaparsec.ParseError Char Parser.ParseError) _)
                return $ case output of
                    Left err         -> T.pack $ show err
                    Right (Left err) -> T.pack $ show err
                    Right (Right ok) -> prettyText ok
    nestedGoldenVsTextM name result
    where throwIfError (Left err)  = throw err
          throwIfError (Right ast) = ast

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
