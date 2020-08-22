{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Test.Hspec.Megaparsec

import Text.Megaparsec

import Type
import Parser

var = parse prsVar "" "id_num9" `shouldParse` EVar "id_num9"
num = parse prsNum "" "912" `shouldParse` ENum 912
pack = parse prsPack "" "Pack{ 12 , 14 }" `shouldParse` EConstr 12 14
parens9 = parse prsParensExpr "" "(9)" `shouldParse` ENum 9
packAExpr = parse prsAExpr "" "Pack{ 15, 0}" `shouldParse` EConstr 15 0

ap = parse prsApp "" "id 2" `shouldParse` EAp (EVar "id") (ENum 2)
apExpr = parse prsExpr "" "k i" `shouldParse` EAp (EVar "k") (EVar "i")

main :: IO ()
main = hspec $ do
  describe "atomics" $ do
    it "parse \"id_num9\" as a variable" var
    it "parse \"912\" as a numeric literal" num
    it "parse \"Pack{ 12 , 14 }\" as a pack" pack
    it "parse \"(9)\" as a bracketed expression" parens9
    it "parse \"Pack{ 15, 0}\" as an atomic expression" packAExpr
  describe "non-atomics" $ do
    it "parse \"id 2\" as an application" ap
    it "parse \"k i\" as an expression" apExpr
