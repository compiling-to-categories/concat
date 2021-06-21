self: super:
let
  netlistSrc = super.fetchFromGitHub {
    owner = "ku-fpg";
    repo = "netlist";
    rev = "0f50a9cfd947885cac7fc392a5295cffe0b3ac31";
    sha256 = "tg0UMslWZin6EeUbOruC9jt1xsgYIuk9vGi7uBSOUCw=";
    fetchSubmodules = true;
  };
in {
  haskellPackages = super.haskellPackages.override (old: {
    overrides = super.lib.composeExtensions (old.overrides or (_: _: { }))
      (hself: hsuper:
        let
          defaultMod = drv:
            super.haskell.lib.disableLibraryProfiling
            (super.haskell.lib.dontHaddock drv);
          callCabal2nix = hself.callCabal2nix;
        in {
          # Prerequisites
          netlist =
            defaultMod (callCabal2nix "netlist" (netlistSrc + /netlist) { });
          verilog =
            defaultMod (callCabal2nix "netlist" (netlistSrc + /verilog) { });
          netlist-to-verilog = defaultMod
            (callCabal2nix "netlist" (netlistSrc + /netlist-to-verilog) { });
          netlist-to-vhdl = defaultMod
            (callCabal2nix "netlist" (netlistSrc + /netlist-to-vhdl) { });

          # ConCat packages
          concat-known = defaultMod (callCabal2nix "concat-known" ../known { });
          concat-satisfy =
            defaultMod (callCabal2nix "concat-satisfy" ../satisfy { });
          concat-inline =
            defaultMod (callCabal2nix "concat-inline" ../inline { });
          concat-classes =
            defaultMod (callCabal2nix "concat-classes" ../classes { });
          concat-plugin =
            defaultMod (callCabal2nix "concat-plugin" ../plugin { });
          concat-examples =
            defaultMod (callCabal2nix "concat-examples" ../examples { });
          concat-graphics =
            defaultMod (callCabal2nix "concat-graphics" ../graphics { });
          concat-hardware =
            defaultMod (callCabal2nix "concat-hardware" ../hardware { });
        });
  });
}
