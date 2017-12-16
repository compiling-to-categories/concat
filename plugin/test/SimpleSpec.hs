{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_GHC -fdicts-strict          #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module SimpleSpec where

import ConCat.AltCat ()
import ConCat.AltCat ()
import ConCat.AltCat (toCcc)
import ConCat.Misc ()
import ConCat.Rebox ()
import ConCat.Rep  ()
import ConCat.Rep ()
import Control.Exception (evaluate)
import Test.Hspec
import Types


------------------------------------------------------------------------------
-- | Synonym for 'shouldBe' that reads better for the following combinators.
isInFact :: (Show a, Eq a) => a -> a -> Expectation
isInFact = shouldBe


------------------------------------------------------------------------------
-- | Expresses that a 'toCcc' expression doesn't fail, but produces the wrong
-- value.
butShouldBe :: a -> b -> a
butShouldBe = const


------------------------------------------------------------------------------
-- | Expresses that a 'toCcc' expression outputs a non-optimal result.
butCouldBeSimplifiedTo :: a -> b -> a
butCouldBeSimplifiedTo = const


------------------------------------------------------------------------------
-- | The following test "succeeds", but is broken because it should have the
-- value its 'butShouldBe' branch.
broken :: Example a => String -> a -> SpecWith (Arg a)
broken = it . ("(broken) " ++)


------------------------------------------------------------------------------
-- | The following test fails to 'toCcc' with an "oops".
failsCcc :: String -> (a -> b) -> SpecWith ()
failsCcc s = it ("(fails-ccc) " ++ s)
           . flip shouldThrow
                  (errorCall "Oops: toCcc' called")
           . evaluate
           . toCcc


------------------------------------------------------------------------------
-- | Helper function for tests that are so broken we shouldn't even try to
-- compile them. These tests will vacuously return successful in the
-- test-suite.
reallyBroken :: String -> String -> a -> SpecWith ()
reallyBroken x s _ = it ("(" ++ x ++ ") " ++ s) $ pure @IO ()


------------------------------------------------------------------------------
-- | The following test would cause a compiler panic if we attemped to 'toCcc'
-- it.
panics :: String -> a -> SpecWith ()
panics = reallyBroken "panics"


------------------------------------------------------------------------------
-- | The following test loops forever at runtime.
spins :: String -> a -> SpecWith ()
spins = reallyBroken "spins"


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



  describe "lambdas" $ do
    it "add \\a b" $
      toCcc (\a b -> a + b :: Float)
        `shouldBe`
          CCurry CAdd

    it "add \\a \\b" $
      toCcc (\a -> \b -> a + b :: Float)
        `shouldBe`
          CCurry CAdd

    it "add \\a b c" $
      toCcc (\a b c -> a + b + c :: Float)
        `shouldBe`
          CCurry (CCurry (CComp CAdd (CComp CAdd CExl `CPAnd` CExr)))

    it "add \\a \\b \\c" $
      toCcc (\a -> \b -> \c -> a + b + c :: Float)
        `shouldBe`
          CCurry (CCurry (CComp CAdd (CComp CAdd CExl `CPAnd` CExr)))

    it "add \\a \\b c" $
      toCcc (\a -> \b c -> a + b + c :: Float)
        `shouldBe`
          CCurry (CCurry (CComp CAdd (CComp CAdd CExl `CPAnd` CExr)))

    it "add \\a b \\c" $
      toCcc (\a b -> \c -> a + b + c :: Float)
        `shouldBe`
          CCurry (CCurry (CComp CAdd (CComp CAdd CExl `CPAnd` CExr)))



  describe "products" $ do
    it "exl" $
      toCcc fst
        `isInFact`
          CComp CApply (CCurry CExr `CPAnd` CExl)
        `butCouldBeSimplifiedTo`
          CExl



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

    panics "extract 3rd" $
      {-
        Simplifier ticks exhausted
        When trying RuleFired pair fst snd
        To increase the limit, use -fsimpl-tick-factor=N (default 100)
        If you need to do this, let GHC HQ know, and what factor you needed
        To see detailed counts use -ddump-simpl-stats
        Total ticks: 126240
      -}
      toCcc (\(_, _, c) -> c)
        `shouldBe`
          CBottom

    panics "sum 3" $
      {-
        Simplifier ticks exhausted
        When trying RuleFired toCcc'
        To increase the limit, use -fsimpl-tick-factor=N (default 100)
        If you need to do this, let GHC HQ know, and what factor you needed
        To see detailed counts use -ddump-simpl-stats
        Total ticks: 128964
      -}
      toCcc (\(a, b, c) -> a + b + c :: Float)
        `shouldBe`
          CBottom

    failsCcc "extract 4th" $
      \(_a1, _a2, _a3, a4) -> a4

    failsCcc "sum 4" $
      \(a1, a2, a3, a4) -> a1 + a2 + a3 + a4 :: Float

    failsCcc "extract 16th" $
      \( _a1, _a2, _a3, _a4, _a5, _a6, _a7, _a8, _a9, _a10, _a11, _a12
       , _a13, _a14, _a15, a16) -> a16



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



  describe "math" $ do
    it "sub" $
      toCcc (\a b -> a - b :: Float)
        `shouldBe`
          CCurry (CComp CAdd (CComp CId CExl `CPAnd` CComp CNeg CExr))

    it "sub pointfree" $
      toCcc ((-) @Float)
        `shouldBe`
          CCurry (CComp CAdd (CComp CId CExl `CPAnd` CComp CNeg CExr))

    it "mult" $
      toCcc (\a b -> a * b :: Float)
        `shouldBe`
          CCurry CMul

    it "mult pointfree" $
      toCcc ((*) @Float)
        `shouldBe`
          CCurry CMul

    panics "square" $
      {-
        Simplifier ticks exhausted
        When trying RuleFired toCcc'
        To increase the limit, use -fsimpl-tick-factor=N (default 100)
        If you need to do this, let GHC HQ know, and what factor you needed
        To see detailed counts use -ddump-simpl-stats
        Total ticks: 262241
      -}
      toCcc (\(a :: Float) -> a ^^ (2 :: Int))
        `shouldBe`
          CBottom

    panics "raise power" $
      {-
        Simplifier ticks exhausted
        When trying RuleFired toCcc'
        To increase the limit, use -fsimpl-tick-factor=N (default 100)
        If you need to do this, let GHC HQ know, and what factor you needed
        To see detailed counts use -ddump-simpl-stats
        Total ticks: 237320
      -}
      toCcc (\(a :: Float) (b :: Int) -> a ^^ b)
        `shouldBe`
          CBottom



  describe "miscellany" $ do
    it "twice" $
      toCcc (\(x :: Float) -> x + x)
        `shouldBe`
          CComp CAdd (CId `CPAnd` CId)

    failsCcc "head" $
      horner @Float [1,3,5]

    it "const float" $
      toCcc (\_z -> 15 :: Float)
        `shouldBe`
          CConst (15 :: Float)

    spins "bottom on const addition" $
      toCcc @FreeSyn (\_z -> 5 + 10 :: Float)
        `isInFact`
          undefined
        `butShouldBe`
          CConst (15 :: Float)


horner :: Num a => [a] -> a -> a
horner []     _ = 0
horner (c:cs) a = c + a * horner cs a

