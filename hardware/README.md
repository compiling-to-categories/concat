This sub-project aims at translating native Haskell to the Verilog hardware description language (HDL) via compiling-to-categories.

    stack build :hardware-examples

Each generated circuit is written to a Verilog (\*.v) file in *concat/hardware/out/*.

There are several more commented-out examples in test/Examples.hs.
You can fiddle with comments to change the collection of examples compiled.
That module also serves as an example to copy and make your own examples.

