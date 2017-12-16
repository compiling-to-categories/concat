{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_GHC -fdicts-strict          #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module SimpleSpec where

import Control.Exception (evaluate)
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


butShouldBe :: a -> b -> a
butShouldBe = const

butCouldBeSimplifiedTo :: a -> b -> a
butCouldBeSimplifiedTo = const

isInFact :: (Show a, Eq a) => a -> a -> Expectation
isInFact = shouldBe

expectCccFailure :: a -> Expectation
expectCccFailure = flip shouldThrow (errorCall "Oops: toCcc' called") . evaluate

don'tTryToCompileItBecauseItWon'tWork :: a -> Expectation
don'tTryToCompileItBecauseItWon'tWork _ = pure ()

broken :: Example a => String -> a -> SpecWith (Arg a)
broken = it


spec :: Spec
spec = do
  describe "trivialities" $ do
    it "id" $ toCcc id `shouldBe` CId

    it "const float" $
      toCcc (const @Float 5)
        `shouldBe`
          CConst 5

    it "const inequal bools" $
      toCcc (const True)
        `shouldNotBe`
          CConst False

    it "compose consts" $
      toCcc (\x -> const False (const True x))
        `shouldBe`
          CConst False

    broken "const unit" $
      toCcc (const ())
        `isInFact`
          CConst ()
        `butShouldBe`
          CTerm



  describe "products" $ do
    it "exl" $
      toCcc fst
        `isInFact`
          CComp CApply (CCurry CExr `CPAnd` CExl)
        `butCouldBeSimplifiedTo`
          CExl

    it "exr" $
      toCcc (\(_, b) -> b)
        `isInFact`
          CComp CApply (CCurry CExr `CPAnd` CExr)
        `butCouldBeSimplifiedTo`
          CExr

    broken "extract 3rd" $
      {-
        When trying RuleFired pair fst snd
        To increase the limit, use -fsimpl-tick-factor=N (default 100)
        If you need to do this, let GHC HQ know, and what factor you needed
        To see detailed counts use -ddump-simpl-stats
        Total ticks: 126240
      -}
      don'tTryToCompileItBecauseItWon'tWork $
        toCcc (\(_, _, c) -> c)
          `shouldBe`
            CBottom

    broken "sum 3" $
      {-
        When trying RuleFired toCcc'
        To increase the limit, use -fsimpl-tick-factor=N (default 100)
        If you need to do this, let GHC HQ know, and what factor you needed
        To see detailed counts use -ddump-simpl-stats
        Total ticks: 128964
      -}
      don'tTryToCompileItBecauseItWon'tWork $
        toCcc (\(a, b, c) -> a + b + c :: Float)
          `shouldBe`
            CBottom

    broken "extract 4th" $
      expectCccFailure $
        toCcc (\(_a1, _a2, _a3, a4) -> a4)

    broken "sum 4" $
      expectCccFailure $
        toCcc (\(a1, a2, a3, a4) -> a1 + a2 + a3 + a4 :: Float)

    broken "extract 16th" $
      expectCccFailure $
        toCcc (\( _a1, _a2, _a3, _a4, _a5, _a6, _a7, _a8, _a9, _a10, _a11, _a12
                , _a13, _a14, _a15, a16) -> a16)



  describe "coproducts" $ do
    it "inl" $
      toCcc Left
        `shouldBe`
          CInl

    it "inr" $
      toCcc Right
        `shouldBe`
          CInr

    it "if..then" $ toCcc
      (\z ->
        if z
           then 5 :: Float
           else 0)
        `shouldBe`
          CComp CIf (CId `CPAnd` (CConst 5 `CPAnd` CConst 0))

    it "choose" $ toCcc
      (\z ->
        case z of
          Right (y :: Int) -> y + y
          Left  x          -> x)
        `shouldBe`
          CCOr CId (CComp CAdd (CId `CPAnd` CId))



  describe "miscellany" $ do
    it "twice" $
      toCcc (\(x :: Float) -> x + x)
        `shouldBe`
          CComp CAdd (CId `CPAnd` CId)

    broken "head" $
      expectCccFailure $
        toCcc (horner @Float [1,3,5])

    it "const float" $
      toCcc (\_z -> 15 :: Float)
        `shouldBe`
          CConst (15 :: Float)

    broken "spin forever on const addition" $
      {-
        Loops indefinitely.
      -}
      don'tTryToCompileItBecauseItWon'tWork $
        toCcc @FreeSyn (\_z -> 5 + 10 :: Float)
          `isInFact`
            undefined
          `butShouldBe`
            CConst (15 :: Float)


horner :: Num a => [a] -> a -> a
horner []     _ = 0
horner (c:cs) a = c + a * horner cs a

