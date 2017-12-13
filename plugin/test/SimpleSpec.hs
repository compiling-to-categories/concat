{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_GHC -fdicts-strict          #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module SimpleSpec where

import ConCat.AltCat (toCcc)
import Test.Hspec
import Types
import ConCat.Rebox ()


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

  -- fails: "(comp app (and (curry exr) exl)))"
  it "exl" $
    toCcc fst
      `shouldBe`
        CExl

  -- fails: "(comp app (and (curry exr) exr)))"
  it "exr" $
    toCcc (\(_, b) -> b)
      `shouldBe`
        CExr

  -- fails: "Oops: toCcc' called"
  it "inl" $
    toCcc Left
      `shouldBe`
        CInl

  -- fails: "Oops: toCcc' called"
  it "inr" $
    toCcc Right
      `shouldBe`
        CInr

  it "twice" $
    toCcc (\(x :: Float) -> x + x)
      `shouldBe`
        CComp CAdd (CId `CPAnd` CId)

