# To do

*   In `Plugin`, maybe float/subst when an expression is only used once.
    I think this one change would save a lot of work and lead to smaller CCC expressions.
*   Fix `reCat` in `Plugin` to fail gracefully if the target category doesn't inhabit the needed `Category` subclass.
    Then fix the `ConstCat (->)` instance in `Category`, and replace `P.const` by `const` in `Circuit` and `Lambda`.
*   I think I'll want to rename `ProductCat`, `CoproductCat`, and `ClosedCat` to "`Cartesian`", "`Cocartesian`", and "`Closed`".
    What about other `Category` subclasses?
*   Handle `newtype` better, and change some `data` uses back to `newtype`.
*   There are `case` and `let` expressions in the middle of categorical compositions, where they can thwart CCC simplifications.
    Inlining those `let` expressions may be exactly what's needed to enable the simplifier's other transformations to eliminate the `case` expressions.
*   AD with non-scalar domains.
*   Simple, general treatment of `ccc (\ _ -> U)` as `constFun (ccc u)`.
    Oops! Take care.
    If I have to $\eta$-expand `U`, I'll then get `apply . (constFun (ccc U) &&& id)`.
    Needs more thought.
*   Look into work replication.
    See 2016-11-30 notes.
*   Better CCC optimization.
*   Why aren't the syntactic `BoolCat`, `NumCat` etc methods inlining, while the `Category`, and `ProductCat` ones are?
*   Other CCCs:
    *   *All* CCCs (universally quantified)
    *   Automatic differentiation
*   Fancier data types via `HasRep` or `Control.Newtype`.
*   More rule-based optimization.
*   Better solution for numeric operations on `Float` and `Double`, which don't work, perhaps due to orphan instances.
    My temporary workaround is `Float`.

# Done

*   Other CCCs:
    *   A syntactic CCC for showing.
        *   Use to test rule-based optimization.
        *   I have a start in src/ConCat/Unused/.
        *   Keep primitives simple, say as a string naming the primitive.
        *   Try to do all optimization via GHC rules.
        *   Would be nice to pretty-print rather than `show`.
*   Inspect categorical code, and start optimizing.
*   Work around problem with numeric operations on `Float` and `Double`.
    I added a module `Float` with `Float` and `Double` types that `newtype`-wrap the standard versions.

