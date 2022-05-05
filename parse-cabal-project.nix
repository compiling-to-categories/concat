# Ideally, parsing cabal.project should be done via official tools
# Related discussion here:
# https://github.com/NixOS/cabal2nix/issues/286

cabalProject:
let
  content = builtins.readFile cabalProject;
  lines = builtins.filter builtins.isString (builtins.split ''
    [
    ]'' content);
  matches =
    builtins.map (builtins.match "[[:space:]]*[.]/(.*)/(.*)[.]cabal$") lines;
  projects = builtins.concatMap (match:
    if builtins.isList match && builtins.length match == 2 then [{
      name = builtins.elemAt match 1;
      path = builtins.elemAt match 0;
    }] else
      [ ]) matches;
in projects
