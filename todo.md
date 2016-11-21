# To do

*   Other CCCs:
    *   A syntactic CCC for showing.
        *   Use to test rule-based optimization.
        *   I have a start in src/ConCat/Unused/.
        *   Keep primitives simple, say as a string naming the primitive.
        *   Try to do all optimization via GHC rules.
        *   Would be nice to pretty-print rather than `show`.
    *   *All* CCCs (universally quantified)
    *   Automatic differentiation
*   Inspect categorical code, and start optimizing.
*   Fancier data types via `ConCat.HasRep` or `Control.Newtype`.
*   Numeric operations on `Float` and `Double` don't work, perhaps due to orphan instances.
    My temporary workaround is `ConCat.Float`.

