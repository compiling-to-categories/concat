let
  bootstrapPkgs = import <nixpkgs> {};
  # We create this by using `nix-prefetch-git`, for instance:
  # nix-prefetch-git --rev foogitrev123 https://github.com/nixos/nixpkgs.git > ./nixpkgs-pin.json
  # The command `nix-prefetch-git` itself can be installed via Nix as well.
  json = builtins.readFile ./nixpkgs-pin.json;
  nixpkgs = builtins.fromJSON json;
  src = bootstrapPkgs.fetchFromGitHub {
    owner = "NixOS";
    repo = "nixpkgs";
    inherit (nixpkgs) rev sha256;
  };
in
  src
