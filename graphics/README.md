This sub-project aims at reproducing [Pan](http://conal.net/Pan), [Vertigo](http://conal.net/papers/Vertigo), and [Eros](http://conal.net/papers/Eros/) via compiling-to-categories.
It will combine categories for GPU code generation, GUIs, and differentiable functions (for lighting).

    stack build :graphics-examples

Each generated shader is embedded in an HTML file in concat/graphics/out/shaders/.

There are several more commented-out examples in test/Examples.hs.
You can fiddle with comments to change the collection of examples compiled.
That module also serves as an example to copy and make your own examples.

