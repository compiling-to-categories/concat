# To do


*   Add a plugin flag for showing the Core resulting of the plugin's pass.
*   Define utility functions to do most of the work of various plugin transformations, including application, abstraction, pairing, etc.
*   Experiment with `-fexpose-all-unfoldings` as an alternative to explicit `INLINE` declarations.
    Also consider `INLINABLE`.
*   Move (some?) todo items to github repo.
*   Add `INLINE` pragmas for the method defaults in `ConCat.Category`.
    So far, I've added them for just a few `(***)`, `subC`, `recipC`, `divideC`.
    See personal notes for 2017-08-25.
*   Look for a better solution to the problem of GHC eagerly inlining methods.
    My current workaround is `ConCat.Category` vs `ConCat.AltCat`.
    Inconvenient for adding classes (like `ChoiceCat` in `ConCat.Choice`).
    Could I instead recognize the dictionary selectors?
*   Mystery with `RBin N3` vs expanded form.
    The former terminates, while the latter doesn't.
    See "`fft_fc_octet`" example in hardware/test/Examples.hs.
*   Failure with unboxed `let` bindings.
    See notes from 2017-07-15.
*   Principled replacement for the `delay` hack (defined in `ConCat.Misc`).
*   SMT depends on z3, which takes some work to install.
    Maybe disable SMT by default in concat-examples.cabal, with a flag to enable it.
*   I think the ghc-typelits-knownnat plugin works in GHCi.
    What's stopping concat-plugin from doing the same?
*   Automated testing.
*   Associated types for product, coproduct, exponential, `Bool`, `Int`, etc.
    The type of `ccc` will have to change, moving closer to the categorical notion of functor (and cartesian functor, closed cartesian functor, etc)
*   Users' guide / misc notes.
*   Document and begin fixing robustness issues.
*   Study performance, and begin improving:
    *   AD seems rather slow.
        Perhaps due to lots of inlining and simplification.
*   Clean up & simplify implementation (once automated testing is in place), particularly `ConCat.Plugin`.
*   Translate case to `DistribCat`.
*   Categories/back-ends:
    *   Verilog back-end, starting with the circuit graph category in `ConCat.Circuit` from concat and `Circat.Netlist` from circat.
        We'll need `Float` and `Double` literals, not currently supported by the KU netlist libraries.
    *   Linear maps with native target representations rather than inlining.
    *   GPU via CUDA or OpenCL, perhaps starting with the graph/circuit category (as with dot, Verilog, and GLSL)
    *   Interval analysis (`ConCat.Interval`): more operations.
    *   Polynomials
    *   Probabilistic computation
    *   Other Kleisli categories
    *   JavaScript generation
    *   Circuit graphs: rework with statically typed primitives.
        *   Cleaner optimization
        *   How to hash-cons?
    *   GLSL: optimizations to introduce SIMD
    *   Optimization, e.g., along the lines of z3cat.
    *   Automatic differentiation:
        *   Back-ends with explicit tensor representations.
            Experiment with associating composition.
        *   `ClosedCat` instance?
    *   A GUI category, along the lines of [*Tangible Functional Programming*](http://conal.net/papers/Eros/).
*   Improve treatment of coercions, replacing `CoerceCat` with composed uses of `RepCat`.
    (I've not managed to do so.)
*   `CoproductCat` instance in `ConCat.Circuit`.
*   Better use of GHC optimizations so that need less (ideally none) in `ConCat.Circuit`.
*   Recursion.
    Would help make a compelling case for compiling-to-categories vs deep DSLs.
*   Get rewrite rules to work better.
    Coercions and `let` bindings sometimes interfere.
*   Use [dump-core](https://hackage.haskell.org/package/dump-core) ([GitHub](https://github.com/yav/dump-core)) to view generated Core.
*   Representation/levity polymorphism, so that we can used unboxed primitives, rather than having to reverse GHC unboxing work.



# Misc to be reviewed

*   Compilation with AD is slow. Diagnose, and improve.
*   Maybe I should replace pin numbers by component numbers and output index (usually 0).
    I could perhaps identify components by a sequence of component indices within the ancestor chain, like stack frames.
*   Figure out how not to need orphan instances in `AD` and `Incremental`.
*   Better way to select orphan modules in `runTcMUnsafe` in `BuildDictionary`.
*   General `TerminalCat` default via `ConstCat` in `Category`.
    Revisit all `TerminalCat` instances.
*   Maybe I don't need `ConstCat (:>)` for anything but scalars, since the compiler will keep breaking down constant terms until it gets to a type for which the target category has a `ConstCat` instance.
*   Demand analysis at category.
*   Comment out `PseudoFun` annotations to see if anything breaks.
*   Use `typeR` from `Misc` to replace uses of `typeRep`.
    I don't think I'm still using `typeRep`.
*   In `Plugin`, refactor common functionality between "top" & "lam" transformations.
*   Name possibilities:
    *   Catskill (though [Catskell](https://wiki.haskell.org/Catskell))
*   Maybe have `buildDictionary` accumulate error messages rather than selecting among them.
*   Sort out the problem with solving `Coercible` constraints as needed for `CoerceCat (->)`.
    Came up with second derivatives.
    See 2017-01-01 notes, including note to Richard Eisenberg.
*   Larger tests, using shaped-types.
*   Remove old code from `Plugin`.
*   Add a test for derivatives without circuits, running the generated Haskell AD code.
*   `Circuit`: try making nodes for `abst`, `repr`, and `coerce`.
*   Restore the `Coercible` constraint in `ConCat.Circuit`, and figure out why the `CoerceCat` constraint isn't getting satisfied.
*   Does `ConvertB` work with constant propagation in `ConCat.Circuit`?
*   Why does the `Coercible` constraint suffice for `CoerceCat` in `LinearRow` but not in `LinearCol`?
*   Explore eliminating `abstReprCase` (and perhaps `abstReprCon`).
    Does unfolding suffice as an alternative?
    Not quite, since lambda-bound variables can appear as scrutinees.
    Maybe we could eliminate that possibility with another transformation.
*   After various optimizations, retry `ADFun` again for comparison.
*   Converting to the `Trivial` category leads to run-time error: "Impossible case alternative".
*   Rewrite rule loop involving "`foo2`" and "`uncurry id`" in `AltCat`.
*   In `LinearRow` and `LinearCol`, retry my old `scaleL` definition via `Keyed` and `Adjustable`, comparing for robustness and speed.
*   `SPECIALIZE` vector space and linear map operations for some common functors, particularly `Par1`, e.g., `scaleL` as used for numeric primitives.
*   In `Plugin`, factor out `return (mkCcc (Lam x ...))` (for lam) and maybe also `return (mkCcc ...)` (for top).
*   Maybe switch from `INLINE` to `INLINABLE`.
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

*Add more here as I encounter them.*

# Done

*   Split concat into a few packages/repos:
    *   Constrained categories ("concat")
    *   The compiler plugin
    *   Example categories and uses

    Make sure that it's easy & quick to build and run examples after the other packages change, without having to check in.
    For instance, use a stack.yaml with local package references.
*   Matches on `Int` literals lead to an error: "lam Case of boxer: bare unboxed var".
*   Fix the problem with finding numeric and show instances for `Float` & `Double`, and then simplify `Circuit` again to use 0 instead of `Eql(fromIntegerZ 0)`, `negate` instead of `negateZ`, etc.
*   Remove `ConCat.Float`.
*   Reboxing of `divideFloat#` and `divideDouble#`.
    The rules in `ConCat.Rebox` (commented out) don't work, perhaps because those operations can fail.
    Simplest solution may be to rebox those primitives programmatically in another simple `BuiltinRule`.
*   Re-organize `GAD` and `Incremental`.
    Leave only general support in `GAD`, and move specific to `AD` and `Incremental`.
*   Try `Coercion` (from `Data.Type.Coercion`) as an example of constrained categories.
    Note that `Coercion a b =~ Dict (Coercible a b)`.
    Similarly for `(:~:)` in `Data.Type.Equality`.
*   Track down problem with `double` example and `deriv`.
    Error message: "`unFunB` got unexpected bus `ConvertB (<function>)`".
    Happens when I use `newtype` instead of `data` for `D` in `AD` *and* drop `HasL` from `OkLM` in `LinearRow`.
    Fixed with a `reveal` added to `dfun` in `AD`.
*   Now that I'm unfolding more effectively (even with value args), maybe I no longer need the `reveal` hack.
    My first test in `AD` failed, but I may need to tweak `unD'` *also*.
    Update: I added `reveal` in `dfun` after `ccc` and before `unD`.
    Greatly improved simplification, and sped up compilation.
*   `Pretty` instances for `GHC.Generics` in `Orphans`.
*   Have `buildDictionary` yield an error message when it fails, replacing the `Maybe` return type with a sum.
    Then have `Plugin` display that message and terminate when appropriate.
*   In `ConCat.Category`, move `Trivial` and `(:**:)` to before Category, and move their class instances to just after each class definition, alongside `(->)`.
*   `Circuit`: perhaps add a `ReprB`, and don't worry about canceling `AbstB` and `ReprB`.
*   Another idea about casts.
    Maybe I can operate not on the coercions but on their domain and range types as yielded by `coercionKind`.
    Then I wouldn't have to concoct sketchy coercions.
    *   When domain and range agree, yield `id`.
    *   If both are function types, use `(<~)` as now.
    *   If the domain type has a `HasRep` instance, pre-compose `repr`, recursively "solving" for the other factor.
    *   If the range type has a `HasRep` instance, post-compose `abst`, solving for other factor.
    
    I think this algorithm is the essence of what I'm doing now.
*   Move bottom-hiding `unsafeCoerce` hack from `AltCat` to a more general definition in `Misc`.
    Then use in `AltCat` for `ccc`.
*   `Circuit`: `Eq` and `ConvertB`.
    I'll probably have to switch to heterogeneous equality, perhaps via `TestEquality` in `Data.Type.Equality`.
    I'm not using `Eq` for now, so I've commented out the instance.
    Oh! Now that `ConvertB` requires `Typeable`, I can implement `Eq` via `eqT`.
*   `Circuit`: Try to unify `AbstB` and `ConvertB`.
    Might require changing `abstC` and `reprC` to be like `abstC'` and `reprC'`, which would probably be fine.
*   Remove HERMIT dependency!
    I copied over `HERMIT.GHC.Typechecker`.
*   In `recast`, when handing `AxiomInstCo` and `Sym` variant, check for `HasRep` instances.
*   In `Syn`, use the pretty-printing class.
*   Undo the `NOINLINE` hack for numeric category operations, which is there for reboxing.
*   Find a way to localize the reboxing transformations (performing them only under `ccc`), so that they don't cause general slow-down.
    Then restore late inlining to `AltCat` ops.
*   Change the `ConstCat Syn` instance to pretty-print instead of `show`ing, so that the layout logic works.
*   Move my transformations earlier, before stage zero, and make `AltCat` operations inline at stage zero.
*   Experiment with running the plugin much later.
    Try second to last.
    Use `newtype`-wrapped `Int` as well as `Float` and `Double`, scheduled to inline just after the plugin, i.e., phase 0.
    Hm.
    Given the `deriving` specification, *can* I delay inlining?
*   Add functions like `sinFloat` to `monoInfo` in `Plugin`.
*   Better solution for numeric operations on `Float` and `Double`, which don't work, perhaps due to orphan instances.
    My temporary workaround is `Float`.
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

