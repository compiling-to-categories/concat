# To do

*   Why aren't the syntactic `BoolCat`, `NumCat` etc methods inlining, while the `Category`, and `ProductCat` ones are?
*   Other CCCs:
    *   *All* CCCs (universally quantified)
    *   Automatic differentiation
*   Fancier data types via `ConCat.HasRep` or `Control.Newtype`.
*   More rule-based optimization.
*   Better solution for numeric operations on `Float` and `Double`, which don't work, perhaps due to orphan instances.
    My temporary workaround is `ConCat.Float`.

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
    I added a module `ConCat.Float` with `Float` and `Double` types that `newtype`-wrap the standard versions.

