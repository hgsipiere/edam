{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Test.Hspec.Megaparsec

import Text.Megaparsec

import Lib
import Type
import Parser

evalFinalNode :: CoreProgram -> Node
evalFinalNode expr = hLookup (getHeap state) (head $ getStack state)
  where state = (last.limitList 10000.eval.compile) $ expr

to_main :: CoreExpr -> CoreProgram
to_main expr = [("main",[],expr)]

vars = EVar "sk_9"
num = ENum 19
pack = EConstr 17 12
app = EAp (EVar "id") (EVar "x")
appId10 = EAp (EVar "i") (ENum 10)
letExpr = ELet False [("x", ENum 9)] (EVar "x")
letrec = ELet recursive [("x", EVar "k"), ("a",ENum 9)] $ EAp (EAp (EVar "x") (EVar "a")) (ENum 12)
caseExpr = ECase (EVar "n") [(1,["x"],ENum 9),(2,["x","y"],ENum 12)]
addLetExpr =  ELet nonRecursive [("x", ENum 5), ("a", ENum 9)] $ EAp (EAp (EVar "plus") (EVar "a")) (EVar "x")
subLetExpr =  ELet nonRecursive [("x", ENum 5), ("a", ENum 9)] $ EAp (EAp (EVar "sub") (EVar "a")) (EVar "x")
fixConst3Prog = [
  ("const3", ["x"], ENum 3),
  ("fix", ["f"], EAp (EAp (EVar "fix") (EVar "const3")) (ENum 7)),
  ("main", [], EAp (EAp (EVar "fix") (EVar "const3")) (ENum 12)) ]

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
ppExprTester expr expected = (show.ppExpr $ expr) `shouldBe` expected

varsPpTest = ppExprTester vars "sk_9"
numPpTest = ppExprTester num "19"
packPpTest = ppExprTester pack "Pack{17,12}"
appPpTest = ppExprTester app "id x"
letPpTest = ppExprTester letExpr "let <x = 9> x"
letrecPpTest = ppExprTester letrec "letrec <x = k; a = 9> x a 12"
casePpTest = ppExprTester caseExpr "case n of <1> x -> 9;\n<2> x y -> 12;"

prettyPrintingTests = describe "pretty printing" $ do
    it "pretty print EVar \"sk_9\" " varsPpTest
    it "pretty print ENum 19" numPpTest
    it "pretty print EConstr 17 12" packPpTest
    it "pretty print EAp (EVar \"id\") (EVar \"x\")" appPpTest
    it "pretty print : let <x = 9> x" letPpTest
    it "pretty print : let <x = k; a = 9> x a 12" letrecPpTest
    it "pretty print : multi-tag case" casePpTest

numEvalTest = (show.evalFinalNode.to_main $ num) `shouldBe` "NNum 19"
appId10EvalTest = (show.evalFinalNode.to_main $ appId10) `shouldBe` "NNum 10"
letExprEvalTest = (show.evalFinalNode.to_main $ letExpr) `shouldBe` "NNum 9"
letrecEvalTest = (show.evalFinalNode.to_main $ letrec) `shouldBe` "NNum 9"
addLetExprTest = (show.evalFinalNode.to_main $ addLetExpr) `shouldBe` "NNum 14"
subLetExprTest = (show.evalFinalNode.to_main $ subLetExpr) `shouldBe` "NNum 4"

fixConst3ProgTest = (show.evalFinalNode $ fixConst3Prog) `shouldBe` "NNum 3"

evalTests = describe "evaluation" $ do
  it "eval, main = 19" numEvalTest
  it "eval, main = i 10" appId10EvalTest
  it "eval, main = let <x = 9> x" letExprEvalTest
  it "eval, main = letrec <x = k; a = 9> x a 12" letrecEvalTest
  it "eval, fixConst3Prog" fixConst3ProgTest
  it "eval, 9 + 5 = 14" addLetExprTest
  it "eval, 9 - 5 = 4" subLetExprTest
-- TODO Tests for evaluation
-- Laziness termination, let/letrec, enum, id/k application
-- Termination can be found by seeing if the length of evaluation states is below
-- some very large number; in a way this is also a crude performance benchmark.


main :: IO ()
main = hspec.parallel $ do
  parsingTests
  prettyPrintingTests
  evalTests
