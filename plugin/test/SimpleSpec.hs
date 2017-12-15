{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_GHC -fdicts-strict          #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module SimpleSpec where

import ConCat.AltCat (toCcc)
import Test.Hspec
import Types

import ConCat.Rebox ()
import ConCat.Misc ()
import ConCat.Rep  ()
import ConCat.AltCat ()
-- import ConCat.AltCat
import ConCat.AltCat ()
import ConCat.Rep ()
import ConCat.Rebox () -- necessary for reboxing rules to fire
import Data.Either (isLeft)




spec :: Spec
spec = describe "free syntactic ccc" $ do
  it "id" $ toCcc id `shouldBe` CId

  it "const float" $
    toCcc (const @Float 5)
      `shouldBe`
        CConst 5

  it "const inequal bools" $
    toCcc (const True)
      `shouldNotBe`
        CConst False

  it "compose consts (simplified)" $
    toCcc (\x -> const False (const True x))
      `shouldBe`
        CConst False

  -- fails: "(const ())"
  --   nb: this "()" is haskell's unit, not 'it'
  -- NOTE(sandy): the plugin does not seem to ever emit 'it'
  it "const unit" $
    toCcc (const ())
      `shouldBe`
        CTerm

--   -- fails: "(comp app (and (curry exr) exl)))"
--   it "exl" $
--     toCcc fst
--       `shouldBe`
--         CExl

--   -- fails: "(comp app (and (curry exr) exr)))"
--   it "exr" $
--     toCcc (\(_, b) -> b)
--       `shouldBe`
--         CExr

  -- fails: "Oops: toCcc' called"
  it "inl" $
    toCcc isLeft
      `shouldBe`
        CBottom

  -- fails: "Oops: toCcc' called"
  it "inr" $
    toCcc Right
      `shouldBe`
        CInr

  it "twice" $
    toCcc (\(x :: Float) -> x + x)
      `shouldBe`
        CComp CAdd (CId `CPAnd` CId)

  it "head" $
    toCcc (horner @Float [1,3,5])
      `shouldBe`
        CBottom

head2 :: [a] -> [a]
head2 [] = []
head2 (_ : as) = as


horner :: Num a => [a] -> a -> a
horner []     _ = 0
horner (c:cs) a = c + a * horner cs a

