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

prSh = show.evalFinalNode.to_main

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

ifTrue7_9 = EAp (EAp (EAp (EVar "if") (ENum 1)) (ENum 7)) (ENum 9)
ifFalse7_9 = EAp (EAp (EAp (EVar "if") (ENum 0)) (ENum 7)) (ENum 9)
ifTrue7_9Test = prSh ifTrue7_9 `shouldBe` "NNum 7"
ifFalse7_9Test = prSh ifFalse7_9 `shouldBe` "NNum 9"


negExpr = EAp (EVar "neg") (ENum 7)
letx5a9ap op = ELet nonRecursive [("x", ENum 5), ("a", ENum 9)] $ EAp (EAp (EVar op) (EVar "a")) (EVar "x")
addLet = letx5a9ap "plus"
subLet = letx5a9ap "sub"
mulLet = letx5a9ap "mul"
divLet = letx5a9ap "div"
modLet = letx5a9ap "mod"

dyTest :: String -> Int -> Int -> String -> Expectation
dyTest op a b expected = (prSh (EAp (EAp (EVar op) (ENum a)) (ENum b))) `shouldBe` expected

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

numEvalTest = (prSh $ num) `shouldBe` "NNum 19"
appId10EvalTest = (prSh $ appId10) `shouldBe` "NNum 10"
letExprEvalTest = (prSh $ letExpr) `shouldBe` "NNum 9"
letrecEvalTest = (prSh $ letrec) `shouldBe` "NNum 9"
addLetTest = (prSh $ addLet) `shouldBe` "NNum 14"
subLetTest = (prSh $ subLet) `shouldBe` "NNum 4"
mulLetTest = (prSh $ mulLet) `shouldBe` "NNum 45"
divLetTest = (prSh $ divLet) `shouldBe` "NNum 1"
modLetTest = (prSh $ modLet) `shouldBe` "NNum 4"

fixConst3ProgTest = (show.evalFinalNode $ fixConst3Prog) `shouldBe` "NNum 3"

evalTests = describe "evaluation" $ do
  it "eval, main = 19" numEvalTest
  it "eval, main = i 10" appId10EvalTest
  it "eval, main = let <x = 9> x" letExprEvalTest
  it "eval, main = letrec <x = k; a = 9> x a 12" letrecEvalTest
  it "eval, fixConst3Prog" fixConst3ProgTest
  it "eval, 9 + 5 = 14" addLetTest
  it "eval, 9 - 5 = 4" subLetTest
  it "eval, 9*5 = 40" mulLetTest
  it "eval, div 9 5 = 1" divLetTest
  it "eval, mod 9 5 = 4" modLetTest
  it "eval, if True 7 9" ifTrue7_9Test
  it "eval, if False 7 9" ifFalse7_9Test

dyadicTests = describe "dyadic" $ do
  it "1 == 1 is True"  $ dyTest "eq" 1 1 "NNum 1"
  it "1 == 2 is False" $ dyTest "eq" 1 2 "NNum 0"
  it "1 \\= 1 is False"  $ dyTest "neq" 1 1 "NNum 0"
  it "1 \\= 2 is True" $ dyTest "neq" 1 2 "NNum 1"
  it "1 < 1 is False" $ dyTest "lt" 1 1 "NNum 0"
  it "1 < 2 is True" $ dyTest "lt" 1 2 "NNum 1"
  it "1 > 1 is False" $ dyTest "gt" 1 1 "NNum 0"
  it "1 <= 1 is True" $ dyTest "le" 1 1 "NNum 1"
  it "1 >= 0 is True" $ dyTest "ge" 1 0 "NNum 1"


main :: IO ()
main = hspec.parallel $ do
  parsingTests
  prettyPrintingTests
  evalTests
  dyadicTests
