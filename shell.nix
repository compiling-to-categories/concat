with import ./nix/pkgs.nix;
pkgs.haskellPackages.shellFor {
  buildInputs = [ cabal-install ghc ];
  packages = p:
    with pkgs.haskellPackages; [
      concat-classes
      concat-examples
      concat-graphics
      concat-hardware
      concat-inline
      concat-known
      concat-plugin
      concat-satisfy
    ];
}
