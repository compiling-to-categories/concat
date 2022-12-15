final: prev: hfinal: hprev: let
  netlistSrc = final.fetchFromGitHub {
    owner = "ku-fpg";
    repo = "netlist";
    rev = "0f50a9cfd947885cac7fc392a5295cffe0b3ac31";
    sha256 = "tg0UMslWZin6EeUbOruC9jt1xsgYIuk9vGi7uBSOUCw=";
    fetchSubmodules = true;
  };
in {
  netlist = hfinal.callCabal2nix "netlist" (netlistSrc + /netlist) {};
  verilog = hfinal.callCabal2nix "netlist" (netlistSrc + /verilog) {};
  netlist-to-verilog =
    hfinal.callCabal2nix "netlist" (netlistSrc + /netlist-to-verilog) {};
  netlist-to-vhdl =
    hfinal.callCabal2nix "netlist" (netlistSrc + /netlist-to-vhdl) {};
}
