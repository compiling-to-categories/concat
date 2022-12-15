with import ./nix/pkgs.nix;
  pkgs.haskellPackages.shellFor {
    nativeBuildInputs = with pkgs; [
      cabal-install
      ghc
      graphviz
      (pkgs.haskell-language-server.override {
        supportedGhcVersions = ["8107" "902" "924"];
      })
    ];
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
