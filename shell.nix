{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7101" }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, array, base, containers, deepseq, directory
      , exceptions, filepath, ghc, ghc-paths, ghc-prim, hint
      , liquid-fixpoint, liquidhaskell, mtl, pretty, process, QuickCheck
      , stdenv, syb, tagged, tasty, tasty-hunit, template-haskell, text
      , text-format, th-lift, transformers, unordered-containers, vector
      , z3
      }:
      mkDerivation {
        pname = "target";
        version = "9.9.9.9";
        src = ./.;
        isLibrary = true;
        isExecutable = true;
        buildDepends = [
          base containers directory exceptions filepath ghc ghc-paths hint
          liquid-fixpoint liquidhaskell mtl pretty process QuickCheck syb
          tagged template-haskell text text-format th-lift transformers
          unordered-containers vector
        ];
        testDepends = [
          array base containers deepseq ghc ghc-prim liquid-fixpoint
          liquidhaskell mtl tagged tasty tasty-hunit template-haskell
          unordered-containers
        ];
        buildTools = [ z3 ];
        description = "Generate test-suites from refinement types";
        license = stdenv.lib.licenses.mit;
      };

  drv = pkgs.haskell.packages.${compiler}.callPackage f {};

in

  if pkgs.lib.inNixShell then drv.env else drv
