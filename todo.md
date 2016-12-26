# To do

*   Reboxing of `divideFloat#` and `divideDouble#`.
    The rules in `ConCat.Rebox` (commented out) don't work, perhaps because those operations can fail.
    Simplest solution may be to rebox those primitives programmatically in another simple `BuiltinRule`.
*   Fix the problem with finding numeric and show instances for `Float` & `Double`, and then simplify `Circuit` again to use 0 instead of `Eql(fromIntegerZ 0)`, `negate` instead of `negateZ`, etc.
*   Rewrite rule loop involving "`foo2`" and "`uncurry id`" in `AltCat`.
*   In `recast`, when handing `AxiomInstCo` and `Sym` variant, Check for HasRep instances.
*   In `Syn`, use the pretty-printing class.
*   Change the `ConstCat Syn` instance to pretty-print instead of `show`ing, so that the layout logic works.
*   Another idea about casts.
    Maybe I can operate not on the coercions but on their domain and range types as yielded by `coercionKind`.
    Then I wouldn't have to concoct sketchy coercions.
    *   When domain and range agree, yield `id`.
    *   If both are function types, use `(<~)` as now.
    *   If the domain type has a `HasRep` instance, pre-compose `repr`, recursively "solving" for the other factor.
    *   If the range type has a `HasRep` instance, post-compose `abst`, solving for other factor.
I think this algorithm is the essence of what I'm doing now.
*   In `LinearRow` and `LinearCol`, retry my old `scaleL` definition via `Keyed` and `Adjustable`, comparing for robustness and speed.
*   `SPECIALIZE` vector space and linear map operations for some common functors, particularly `Par1`, e.g., `scaleL` as used for numeric primitives.
*   In `Plugin`, factor out `return (mkCcc (Lam x ...))` (for lam) and maybe also `return (mkCcc ...)` (for top).
*   Maybe switch from `INLINE` to `INLINABLE`.
*   Now that I'm unfolding more effectively (even with value args), maybe I no longer need the `reveal` hack.
    My first test in `AD` failed, but I may need to tweak `unD'` *also*.
*   Eliminate the hack of first `ccc`ing to `(->)`, letting simplifications happen, and then `ccc`ing to another category, say without `Closed`.
    I think I'd have to improve my ability to do without `Closed`, including floating or substituting more `let` bindings.
*   I think I'll want to rename `ProductCat`, `CoproductCat`, and `ClosedCat` to "`Cartesian`", "`Cocartesian`", and "`Closed`".
    What about other `Category` subclasses?
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

*   Remove HERMIT dependency!
    I copied over `HERMIT.GHC.Typechecker`.
*   Undo the `NOINLINE` hack for numeric category operations, which is there for reboxing.
*   Find a way to localize the reboxing transformations (performing them only under `ccc`), so that they don't cause general slow-down.
    Then restore late inlining to `AltCat` ops.
*   Move my transformations earlier, before stage zero, and make `AltCat` operations inline at stage zero.
*   Experiment with running the plugin much later.
    Try second to last.
    Use `newtype`-wrapped `Int` as well as `Float` and `Double`, scheduled to inline just after the plugin, i.e., phase 0.
    Hm.
    Given the `deriving` specification, *can* I delay inlining?
*   In `Plugin`, try going directly from `AxiomInstCo` and `SymCo AxiomInstCo` to `reprC` and `abstC`. Failed.
*   Handle `newtype` better, and change some `data` uses back to `newtype`.
*   Fix `transCatOp` in `Plugin` to fail gracefully if the target category doesn't inhabit the needed `Category` subclass.
    Fall back to unfolding.
    Then fix the `ConstCat (->)` instance in `Category`, and replace `P.const` by `const` in `Circuit` and `Lambda`.
*   In `Plugin`, maybe float/subst when an expression is only used once.
    I think this one change would save a lot of work and lead to smaller CCC expressions.
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

