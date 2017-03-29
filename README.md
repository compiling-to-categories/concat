## Constrained categories

Experimenting (again) with constrained categories, as well as Haskell to hardware, automatic differentiation, interval analysis, and other interpretations. See the paper [*Compiling to categories*](http://conal.net/papers/compiling-to-categories).

To run:

    stack build :basic

## Some application ideas:

*   Interval analysis on general values rather than numbers
    Use a standard ordering for sums and products
*   Something about language recognition, such as regular languages
*   Various semirings, including shortest/longest paths
*   Probabilistic programming
*   Usage analysis.
*   Something that makes memoization more efficient, such as simple usage analysis.
    If a computation ignores part of a value, then don't evaluate and cache variations in that part.
*   Memoization at every stage. With what benefit?
*   AFRP
*   Functions with some special cases like constant, linear, polynomial, as well as the general case
