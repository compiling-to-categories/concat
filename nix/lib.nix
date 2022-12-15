{
  bash-strict-mode,
  nixpkgs,
}: let
  # Reads the set of local packages from a cabal.project provided at the call
  # site.
  #
  # Ideally, parsing cabal.project should be done via official tools
  # Related discussion at NixOS/cabal2nix#286
  parseCabalProject = cabalProject: let
    content = builtins.readFile cabalProject;
    lines = nixpkgs.lib.splitString "\n" content;
    matches =
      builtins.map (builtins.match "^[[:space:]]*([.].*)/(.*)[.]cabal$") lines;
  in
    builtins.listToAttrs
    (builtins.concatMap
      (match:
        if builtins.isList match && builtins.length match == 2
        then [
          {
            name = builtins.elemAt match 1;
            value = builtins.elemAt match 0;
          }
        ]
        else [])
      matches);
in {
  inherit parseCabalProject;

  # A “Haskell overlay” is a function that takes the usual overlay arguments,
  # but also takes a GHC version and then Haskell-specific final and prev
  # arguments (suitable for passing to `haskell.packages.${ghc}.extend`).
  #
  # This function takes a (final: ghc: AttrSet of Haskell packages) and returns
  # a Haskell overlay.
  haskellOverlay = packages: final: prev: hfinal: hprev: packages final hfinal;

  # Produces a devShell for each supported GHC version.
  # `nativeBuildInputs` is a function from a Haskell package set for a
  # particular  GHC version to a list of packages to include as native build
  # inputs.
  mkDevShells = pkgs: ghcVersions: packages: nativeBuildInputs:
    builtins.listToAttrs
    (builtins.map
      (ghcVer: let
        hpkgs = pkgs.haskell.packages.${ghcVer};
      in {
        name = ghcVer;
        value =
          bash-strict-mode.lib.drv pkgs
          (hpkgs.shellFor {
            packages = _: builtins.attrValues (packages pkgs hpkgs);
            nativeBuildInputs = nativeBuildInputs hpkgs;
            withHoogle = false;
          });
      })
      ghcVersions);

  # Produces a set of packages for each supported GHC version.
  #
  # <ghcVer>_<package> = A package with only the one Cabal package
  # <ghcVer>_all = A package containing GHC will all Cabal packages installed
  mkPackages = pkgs: ghcVersions: packages:
    nixpkgs.lib.foldr
    (a: b: a // b)
    {}
    (builtins.map
      (ghcVer: let
        hpkgs = pkgs.haskell.packages.${ghcVer};

        ghcPackages = packages pkgs hpkgs;

        individualPackages =
          nixpkgs.lib.concatMapAttrs
          (name: value: {"${ghcVer}_${name}" = value;})
          ghcPackages;
      in
        individualPackages
        // {
          "${ghcVer}_all" = pkgs.buildEnv {
            name = "all-packages";
            paths = [
              (hpkgs.ghcWithPackages (_: builtins.attrValues ghcPackages))
            ];
          };
        })
      ghcVersions);

  # Creates an overlay with `haskellOverlay` installed in
  # `haskell.packages.<ghcVer>` for each supported GHC version.
  #
  # `haskellOverlay` should be a function:
  #
  #     final: prev: finalHaskPkgs: prevHaskPkgs: AttrSet
  overlayHaskellPackages = ghcVersions: haskellOverlay: final: prev: {
    haskell =
      prev.haskell
      // {
        packages =
          prev.haskell.packages
          // builtins.listToAttrs
          (builtins.map
            (ghcVer: {
              name = ghcVer;
              value =
                prev.haskell.packages.${ghcVer}.extend
                (haskellOverlay final prev);
            })
            ghcVersions);
      };
  };

  cabalProject2nix = cabalProject: pkgs: hpkgs: overrides:
    builtins.mapAttrs
    (name: path:
      bash-strict-mode.lib.shellchecked pkgs
      ((hpkgs.callCabal2nix name "${builtins.dirOf cabalProject}/${path}" {})
        .overrideAttrs
        overrides))
    (parseCabalProject cabalProject);
}
