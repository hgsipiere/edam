{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Test.Hspec.Megaparsec

import Text.Megaparsec

import Type
import Parser

varPrsTest = parse prsVar "" "id_num9" `shouldParse` EVar "id_num9"
numPrsTest = parse prsNum "" "912" `shouldParse` ENum 912
packPrsTest = parse prsPack "" "Pack{ 12 , 14 }" `shouldParse` EConstr 12 14
parens9PrsTest = parse prsParensExpr "" "(9)" `shouldParse` ENum 9
packAExprPrsTest = parse prsAExpr "" "Pack{ 15, 0}" `shouldParse` EConstr 15 0

letPrsTest = parse prsLet "" "let <x = 5> 2" `shouldParse`
 (ELet nonRecursive [("x",ENum 5)] $ ENum 2)
letrecPrsTest = parse prsLetrec "" "letrec <telle = x y> 12" `shouldParse`
 (ELet recursive [("telle",EAp (EVar "x") (EVar "y"))] $ ENum 12)
casePrsTest = parse prsCase "" "|x| <1> hello -> 2" `shouldParse`
 (ECase (EVar "x") [(1, ["hello"], ENum 2)])
apPrsTest = parse prsApp "" "id 2" `shouldParse` EAp (EVar "id") (ENum 2)
apExprPrsTest = parse prsExpr "" "k i" `shouldParse` EAp (EVar "k") (EVar "i")

parsingTests = describe "parsing" $ do 
  describe "atomics" $ do
    it "parse \"id_num9\" as a variable" varPrsTest
    it "parse \"912\" as a numeric literal" numPrsTest
    it "parse \"Pack{ 12 , 14 }\" as a pack" packPrsTest
    it "parse \"(9)\" as a bracketed expression" parens9PrsTest
    it "parse \"Pack{ 15, 0}\" as an atomic expression" packAExprPrsTest
  describe "non-atomics" $ do
    it "parse \"id 2\" as an application" apPrsTest
    it "parse \"k i\" as an expression" apExprPrsTest
    it "parse \"let <x = 5> 2\" as a let expression" letPrsTest
    it "parse \"letrec <telle = x y> 12\" as a recursive let expression" letrecPrsTest
    it "parse \"|x| <1> hello -> 2\" as a case expression" casePrsTest

varsPpTest = (show.ppExpr $ EVar "sk_9") `shouldBe` "sk_9"
numPpTest = (show.ppExpr $ ENum 19) `shouldBe` "19"
packPpTest = (show.ppExpr $ EConstr 17 12) `shouldBe` "Pack{17,12}"
appPpTest = (show.ppExpr $ EAp (EVar "id") (EVar "x")) `shouldBe` "id x"
letPpTest = (show.ppExpr $ ELet False [("x",ENum 9)] (EVar "x"))
  `shouldBe` "let <x = 9> x"
letrecPpTest = (show.ppExpr $
  ELet True [("x",EVar "k"), ("a",ENum 9)] (EVar "x"))
  `shouldBe` "letrec <x = k; a = 9> x"

casePpTest = (show.ppExpr $
  ECase (EVar "n") [(1,["x"],ENum 9),(2,["x","y"],ENum 12)])
  `shouldBe` "case n of <1> x -> 9;\n<2> x y -> 12;"
  

prettyPrintingTests = describe "pretty printing" $ do
    it "pretty print EVar \"sk_9\" " varsPpTest
    it "pretty print ENum 19" numPpTest
    it "pretty print EConstr 17 12" packPpTest
    it "pretty print EAp (EVar \"id\") (EVar \"x\")" appPpTest
    it "pretty print : let <x = 9> x" letPpTest
    it "pretty print : let <x = k; a = 9> x" letrecPpTest
    it "pretty print : multi-tag case" casePpTest

-- TODO Tests for evaluation
-- Laziness termination, let/letrec, enum, id/k application
-- Termination can be found by seeing if the length of evaluation states is below
-- some very large number; in a way this is also a crude performance benchmark.
main :: IO ()
main = hspec.parallel $ do
  parsingTests
  prettyPrintingTests
