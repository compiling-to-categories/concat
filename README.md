## Constrained categories

Experimenting (again) with constrained categories, as well as Haskell to hardware, automatic differentiation, interval analysis, and other interpretations. See the paper [*Compiling to categories*](http://conal.net/papers/compiling-to-categories).

To run:

    stack build :basic

## Some applications

Working:

*   Circuit graphs
*   Automatic differentiation
*   GLSL for graphics
*   Interval analysis
*   Incremental computation

In progress:

*   Polynomials
*   Demand analysis for strictness.
*   Functions with some special cases like constant, linear, polynomial, as well as the general case

Others:
*   Something about language recognition, such as regular languages
*   Various semirings, including shortest/longest paths
*   Probabilistic programming
    If a computation ignores part of a value, then don't evaluate and cache variations in that part.
*   Memoization at every stage. With what benefit?
*   AFRP
