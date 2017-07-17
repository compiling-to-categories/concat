## Constrained categories

Experimenting (again) with constrained categories, as well as Haskell to hardware, automatic differentiation, interval analysis, and other interpretations. See the paper [*Compiling to categories*](http://conal.net/papers/compiling-to-categories).

To run miscellaneous examples:

    stack build :misc-examples

There are several more commented-out examples in examples/test/Examples.hs.
You can fiddle with comments to change the collection of examples compiled.
That module also serves as an example to copy and make your own examples.

For the graphics examples, instead run

    stack build :graphics-examples

There are more examples in graphics/test/Examples.hs.

## Some applications

Working:

*   Circuit graphs
*   Automatic differentiation
*   GLSL for graphics
*   Interval analysis
*   Incremental computation
*   SMT (satisfy modulo theories), with John Wiegley

In progress:

*   Polynomials
*   Demand analysis for strictness.
*   Functions with some special cases like constant, linear, polynomial, as well as the general case

Others:

*   Something about language recognition, such as regular languages
*   Various semirings, including shortest/longest paths
*   Probabilistic programming and other wrappings of monadic interfaces
*   Memoization at every stage. With what benefit?
*   AFRP
