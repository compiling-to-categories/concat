{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_GHC -fdicts-strict          #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module SimpleSpec where

import ConCat.AltCat (toCcc)
import Test.Hspec
import Types


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

  -- fails: "(const False)"
  -- NOTE(sandy): this is caused by GHC simplifying
  it "compose consts (not simplified)" $
    toCcc (\x -> const False (const True x))
      `shouldBe`
        CComp (CConst False) (CConst True)

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

  -- -- fails to compile: "panic! lam Case of boxer: bare unboxed var"
  -- it "twice" $
  --   toCcc (double @Float)
  --     `shouldBe`
  --       CComp CAdd (CId `CPAnd` CId)

