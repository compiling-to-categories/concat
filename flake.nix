{
  description = "concat";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-21.11";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachSystem flake-utils.lib.allSystems (system:
      let
        haskellLib = (import nixpkgs { inherit system; }).haskell.lib;

        excludedPackages = [ "concat-hardware" ];
        noHaddockPackages =
          [ "concat-examples" "concat-inline" "concat-plugin" ];
        # need display, graphviz for testing. disable test for now.
        noCheckPackages = [ "concat-graphics" "concat-plugin" ];

        parseCabalProject = import ./parse-cabal-project.nix;
        concatPackages = let parsed = parseCabalProject ./cabal.project;
        in builtins.filter
        ({ name, ... }: !(builtins.elem name excludedPackages)) parsed;
        concatPackageNames = builtins.map ({ name, ... }: name) concatPackages;

        haskellOverlay = self: super:
          builtins.listToAttrs (builtins.map ({ name, path }: {
            inherit name;
            value = let
              p = self.callCabal2nix name (./. + "/${path}") { };
              p1 = if builtins.elem name noHaddockPackages then
                haskellLib.dontHaddock p
              else
                p;
              p2 = if builtins.elem name noCheckPackages then
                haskellLib.dontCheck p1
              else
                p1;
            in p2;
          }) concatPackages);

        # see these issues and discussions:
        # - https://github.com/NixOS/nixpkgs/issues/16394
        # - https://github.com/NixOS/nixpkgs/issues/25887
        # - https://github.com/NixOS/nixpkgs/issues/26561
        # - https://discourse.nixos.org/t/nix-haskell-development-2020/6170
        fullOverlay = final: prev: {
          haskellPackages = prev.haskellPackages.override (old: {
            overrides =
              final.lib.composeExtensions (old.overrides or (_: _: { }))
              haskellOverlay;
          });
        };
      in {
        # This package set is only useful for CI build test.
        # In practice, users will create a development environment composed by overlays.
        packages = let
          packagesOnGHC = ghcVer:
            let
              overlayGHC = final: prev: {
                haskellPackages = prev.haskell.packages.${ghcVer};
              };

              newPkgs = import nixpkgs {
                overlays = [ overlayGHC fullOverlay ];
                inherit system;
              };

              individualPackages = builtins.listToAttrs (builtins.map
                ({ name, ... }: {
                  name = ghcVer + "_" + name;
                  value = builtins.getAttr name newPkgs.haskellPackages;
                }) concatPackages);

              allEnv = let
                hsenv = newPkgs.haskellPackages.ghcWithPackages (p:
                  let
                    deps =
                      builtins.map ({ name, ... }: p.${name}) concatPackages;
                  in deps);
              in newPkgs.buildEnv {
                name = "all-packages";
                paths = [ hsenv ];
              };
            in individualPackages // { "${ghcVer}_all" = allEnv; };

        in packagesOnGHC "ghc8107" // packagesOnGHC "ghc884"
        // packagesOnGHC "ghc901" // packagesOnGHC "ghc921"
        // packagesOnGHC "ghcHEAD";

        overlay = fullOverlay;

        devShells = let
          mkDevShell = ghcVer:
            let
              overlayGHC = final: prev: {
                haskellPackages = prev.haskell.packages.${ghcVer};
              };

              newPkgs = import nixpkgs {
                overlays = [ overlayGHC fullOverlay ];
                inherit system;
              };

            in newPkgs.haskellPackages.shellFor {
              packages = ps: builtins.map (name: ps.${name}) concatPackageNames;
              buildInputs = [ newPkgs.haskellPackages.cabal-install ] ++
                # haskell-language-server on GHC 9.2.1 is broken yet.
                newPkgs.lib.optional (ghcVer != "ghc921")
                [ newPkgs.haskell-language-server ];
              withHoogle = false;
            };
        in {
          "ghc8107" = mkDevShell "ghc8107";
          "ghc921" = mkDevShell "ghc921";
        };
      });
}
