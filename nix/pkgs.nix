let
  concatOverlay = import ./concat-overlay.nix;
  nixpkgsSrc = import ./pinned-nixpkgs.nix;
  pkgs = import nixpkgsSrc { overlays = [ concatOverlay ]; };
in pkgs
