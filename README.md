## Constrained categories

[![Build Status](https://travis-ci.org/conal/concat.svg?branch=master)](https://travis-ci.org/conal/concat)

Experimenting (again) with constrained categories, as well as Haskell to hardware, automatic differentiation, interval analysis, and other interpretations. See the paper [*Compiling to categories*](http://conal.net/papers/compiling-to-categories).

You will need to have [GraphViz](https://www.graphviz.org/) installed.

To run miscellaneous examples:

    stack build :misc-examples

There are several more commented-out examples in examples/test/Examples.hs.
You can fiddle with comments to change the collection of examples compiled.
That module also serves as an example to copy and make your own examples.

For the graphics examples, instead run

    stack build :graphics-examples

There are more examples in graphics/test/Examples.hs.

The SMT examples are disabled by default, because they rely on installing the [Z3 SMT solver](https://github.com/Z3Prover/z3) (with installation etc described [here](https://github.com/Z3Prover/z3/wiki)).
To enable some of those examples, install Z3, uncomment them in examples/test/Examples.hs, and run as follows:

    stack build :misc-examples --flag concat-examples:smt

# Troubleshooting

## I can't install netlist-to-verilog with cabal new-build or cabal install
https://github.com/ku-fpg/netlist is the repo that includes the offending package.
To get things started do
`git clone https://github.com/ku-fpg/netlist.git ../netlist-kit-kufp/`

## I get an error along the lines of "`Oops: toCcc' called`"

The plugin works via two kinds of rewrite rules: some specified via `RULES` pragmas, in the modules `ConCat.AltCat` and `ConCat.Rebox`, and a "builtin" rule, which is Haskell code that explicitly manipulates Core, in `ConCat.Plugin`. An run-time error of the form "`Oops: toCcc' called`" occurs if the plugin was not able to transform away all uses of the pseudo-function `toCcc'` (which has no implementation) via the rules.

Therefore:

*   Be sure to import the `ConCat.AltCat` and `ConCat.Rebox` modules, e.g.,

``` haskell
import ConCat.AltCat ()
import ConCat.Rebox ()
```

*   Remember to tell ghc to use the plugin with the option `-fplugin=ConCat.Plugin`.

*   Remember to turn on optimization, which enables the firing of the rules (e.g., `-O` or `-O2`).

*   Sometimes you also need to import `GHC.Generics` with a few constructors exposed (e.g., `U1`, `Par1`, `(:*:)`, and `Comp1`) so that Core casts can be successfully translated to categorical form (via `Coercible`).
    This requirement is especially unfortunate because the need to import has nothing to do with explicit use of those constructors in code that you write, and because following this advice leads to compiler warnings about unused imports.
    I hope to find an alternative method of translating coercions.

Example of ghc compilation:

```
ghc -O -fplugin=ConCat.Plugin YourModule.hs
```

Unfortunately, this library doesn't (yet) work when called from ghci.

## Plugin flags

You can get more info about plugin failures by providing some flags in the module being compiled with the plugin.
The current options:

``` haskell
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showResiduals #-}
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showCcc #-}
```

*   `trace`: Generate *lots* of output as (small) transformations happen.
*   `showResiduals`: A `residual` `toCcc'` call is one that the plugin did not manage to eliminate.
    Since the `toCcc'` pseudo-function has no implementation, residuals often result in a run-time error message.
*   `showCcc`: Show the Core for the whole module being compiled, at the end of the `toCcc` phase and before the final GHC passes.

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
