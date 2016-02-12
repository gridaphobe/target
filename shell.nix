{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", profiling ? false }:

let

  inherit (nixpkgs) pkgs;

  liquidhaskell = import ../haskell { inherit (nixpkgs) fetchgitLocal; };
  liquid-fixpoint = import ../haskell/liquid-fixpoint { inherit (nixpkgs) fetchgitLocal; };
  prover = import ../haskell/prover { inherit (nixpkgs) fetchgitLocal; };

  f = import ./default.nix { inherit (pkgs) fetchgitLocal; };

  mkLocal = drv: { doCheck = false; doHaddock = false; configureFlags = ["-O0"]; };

  haskellPackages = (if compiler == "default"
                     then pkgs.haskellPackages
                     else pkgs.haskell.packages.${compiler}
                    ).override {
                      overrides = self: super: {
                        liquid-fixpoint = (self.callPackage liquid-fixpoint { inherit (pkgs) z3; }).overrideDerivation mkLocal;
                        prover = (self.callPackage prover {}).overrideDerivation mkLocal;
                        liquidhaskell = (self.callPackage liquidhaskell { inherit (pkgs) z3; }).overrideDerivation mkLocal;
                        aeson = super.aeson_0_10_0_0;

                        mkDerivation = drv: super.mkDerivation (drv // { enableLibraryProfiling = profiling; });
                      };
                    };

  drv = haskellPackages.callPackage f { inherit (pkgs) z3; };

in

  if pkgs.lib.inNixShell then drv.env else drv
