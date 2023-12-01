{
  description = "Compiling to categories";

  nixConfig = {
    ## https://github.com/NixOS/rfcs/blob/master/rfcs/0045-deprecate-url-syntax.md
    extra-experimental-features = ["no-url-literals"];
    extra-trusted-public-keys = [
      "cache.garnix.io:CTFPyKSLcx5RMJKfLo5EEPUObbA78b0YQ2DTCJXqr9g="
    ];
    extra-trusted-substituters = ["https://cache.garnix.io"];
    ## Isolate the build.
    registries = false;
    sandbox = true;
  };

  outputs = inputs: let
    pname = "concat";

    defaultCompiler = "ghc948";
    supportedGhcVersions = [
      "ghc902"
      "ghc928"
      "ghc948"
    ];
    # Haddock for `concat-inline` currently fails with
    #
    # During interactive linking, GHCi couldn't find the following symbol:
    #  concatzminlinezm0zi1zi0zi0zmLozzNZZOi9JbQLBJ6XV1cRbO_ConCatziInlineziPlugin_plugin_closure
    noHaddockPackages = ["concat-inline"];

    cabalPackages = pkgs: hpkgs:
      inputs.nixpkgs.lib.concatMapAttrs
      (name: value: {
        "${name}" =
          if builtins.elem name noHaddockPackages
          then pkgs.haskell.lib.dontHaddock value
          else value;
      })
      (inputs.self.lib.cabalProject2nix ./cabal.project pkgs hpkgs (old: old));
  in
    {
      overlays = {
        default =
          inputs.self.lib.overlayHaskellPackages
          supportedGhcVersions
          inputs.self.overlays.haskell;

        haskell = inputs.self.lib.haskellOverlay cabalPackages;

        ## Only needed if you are using `concat-hardware`.
        netlist-default =
          inputs.self.lib.overlayHaskellPackages
          supportedGhcVersions
          inputs.self.overlays.netlist-haskell;

        netlist-haskell = import ./nix/netlist-overlay.nix;
      };

      homeConfigurations =
        builtins.listToAttrs
        (builtins.map
          (system: {
            name = "${system}-example";
            value = inputs.home-manager.lib.homeManagerConfiguration {
              pkgs = import inputs.nixpkgs {
                inherit system;
                overlays = [inputs.self.overlays.default];
              };

              modules = [
                ({pkgs, ...}: {
                  home.packages = [
                    (pkgs.haskellPackages.ghcWithPackages (hpkgs: [
                      hpkgs.concat-plugin
                    ]))
                  ];

                  ## These attributes are simply required by home-manager.
                  home = {
                    homeDirectory = /tmp/${pname}-example;
                    stateVersion = "23.105";
                    username = "${pname}-example-user";
                  };
                })
              ];
            };
          })
          inputs.flake-utils.lib.defaultSystems);

      ## TODO: Pull this into its own flake, for use across Haskell projects.
      lib = import ./nix/lib.nix {inherit (inputs) bash-strict-mode nixpkgs;};
    }
    // inputs.flake-utils.lib.eachSystem inputs.flake-utils.lib.allSystems (system: let
      pkgs = import inputs.nixpkgs {
        inherit system;
        ## NB: This uses `inputs.self.overlays.default` because packages need to
        ##     be able to find other packages in this flake as dependencies.
        overlays = [
          inputs.self.overlays.netlist-default
          inputs.self.overlays.default
        ];
      };
    in {
      packages =
        {default = inputs.self.packages.${system}."${defaultCompiler}_all";}
        // inputs.self.lib.mkPackages pkgs supportedGhcVersions cabalPackages;

      devShells =
        {default = inputs.self.devShells.${system}.${defaultCompiler};}
        // inputs.self.lib.mkDevShells pkgs supportedGhcVersions cabalPackages
        (hpkgs:
          [
            hpkgs.cabal-install
            pkgs.graphviz
          ]
          # Haskell Language Server doesn’t support all GHC versions.
          ++ pkgs.lib.optional
          (!(builtins.elem hpkgs.ghc.version ["8107" "924"]))
          hpkgs.haskell-language-server);

      checks = {
        nix-fmt =
          inputs.bash-strict-mode.lib.checkedDrv pkgs
          (pkgs.stdenv.mkDerivation {
            src = pkgs.lib.cleanSource ./.;

            name = "nix fmt";

            nativeBuildInputs = [inputs.self.formatter.${system}];

            buildPhase = ''
              runHook preBuild
              alejandra --check .
              runHook postBuild
            '';

            installPhase = ''
              runHook preInstall
              mkdir -p "$out"
              runHook preInstall
            '';
          });
      };

      ## TODO: Move these functions to the lib.
      apps = let
        ## Define a single entry for flake `apps` from the path in the Nix store
        ## for a Cabal package and executable defined in that package.
        cabalApp = package: executable: {
          program = "${inputs.self.packages.${system}."${defaultCompiler}_${package}"}/bin/${executable}";
          type = "app";
        };

        ## Given a path in the Nix store for a Cabal package and a list of
        ## executables defined in the Cabal package, creates an AttrSet of apps,
        ## one per listed executable.
        ##
        ## TODO: Somehow extract this, if possible, from `callCabal2nix` result.
        cabalApps = package: executables:
          builtins.listToAttrs
          (map (exe: {
              name = exe;
              value = cabalApp package exe;
            })
            executables);

        ## Given an AttrSet with the keys being paths in the Nix store for Cabal
        ## packages and the values being lists of executables defined in that
        ## Cabal package, creates an AttrSet of apps, one per listed executable.
        ##
        ## TODO: Somehow extract this, if possible, from `cabalProject2nix`
        ##       result.
        cabalProjectApps = pkgs.lib.concatMapAttrs cabalApps;
      in
        cabalProjectApps {
          concat-graphics = ["graphics-examples" "graphics-trace"];
          concat-hardware = ["hardware-examples" "hardware-trace"];
          concat-plugin = ["misc-examples" "misc-trace"];
        };

      # Nix code formatter, https://github.com/kamadorueda/alejandra#readme
      formatter = pkgs.alejandra;
    });

  inputs = {
    bash-strict-mode = {
      inputs.nixpkgs.follows = "nixpkgs";
      url = "github:sellout/bash-strict-mode";
    };

    flake-utils.url = "github:numtide/flake-utils";

    home-manager = {
      inputs.nixpkgs.follows = "nixpkgs";
      url = "github:nix-community/home-manager/release-23.11";
    };

    nixpkgs.url = "github:NixOS/nixpkgs/release-23.11";
  };
}
