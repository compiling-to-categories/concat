This project aims at reproducing [Pan](http://conal.net/Pan), [Vertigo](http://conal.net/papers/Vertigo), and [Eros](http://conal.net/papers/Eros/) via compiling-to-categories.
It will combine categories for GPU code generation, GUIs, and differentiable functions (for lighting).

For now, you'll have to place this repository in the same directory as concat so that the relative paths in stack.yaml can find it.
Perhaps it should be moved back into the same repository instead while concat is being so actively developed.

To build and run:

    stack build :run

There are several more commented-out examples in test/Run.hs.
You can fiddle with comments to change the collection of examples compiled.
That module also serves as an example to copy and make your own examples.

