let
  pkgs = import <nixpkgs> {};
  haskellPackages = pkgs.haskellPackages;
  pkg = haskellPackages.callPackage ./. {};
in 
pkgs.lib.overrideDerivation pkg (attrs: {
  buildInputs = [ haskellPackages.cabalInstall pkgs.fish ] ++ attrs.buildInputs;
})
