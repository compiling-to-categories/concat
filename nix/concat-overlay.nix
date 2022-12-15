self: super: {
  haskellPackages = super.haskellPackages.extend (self.lib.composeExtensions
    (import ./nix/netlist-overlay.nix self super)
    (hself: hsuper: let
      defaultMod = drv:
        super.haskell.lib.disableLibraryProfiling
        (super.haskell.lib.dontHaddock drv);
      callCabal2nix = hself.callCabal2nix;
    in {
      concat-known = defaultMod (callCabal2nix "concat-known" ../known {});
      concat-satisfy =
        defaultMod (callCabal2nix "concat-satisfy" ../satisfy {});
      concat-inline =
        defaultMod (callCabal2nix "concat-inline" ../inline {});
      concat-classes =
        defaultMod (callCabal2nix "concat-classes" ../classes {});
      concat-plugin =
        defaultMod (callCabal2nix "concat-plugin" ../plugin {});
      concat-examples =
        defaultMod (callCabal2nix "concat-examples" ../examples {});
      concat-graphics =
        defaultMod (callCabal2nix "concat-graphics" ../graphics {});
      concat-hardware =
        defaultMod (callCabal2nix "concat-hardware" ../hardware {});
    }));
}
