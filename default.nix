{ mkDerivation, array, base, containers, deepseq, directory
, exceptions, filepath, ghc, ghc-paths, ghc-prim, liquid-fixpoint
, liquidhaskell, mtl, pretty, process, stdenv, syb, tagged, tasty
, tasty-hunit, template-haskell, text, text-format, transformers
, unordered-containers, vector, th-lift
}:
mkDerivation {
  pname = "target";
  version = "0.1.1.1";
  src = (import <nixpkgs> {}).fetchgitLocal ./.;
  doCheck = true;
  buildDepends = [
    base containers directory exceptions filepath ghc ghc-paths
    liquid-fixpoint liquidhaskell mtl pretty process syb tagged
    template-haskell text text-format transformers unordered-containers
    vector th-lift
  ];
  testDepends = [
    array base containers deepseq ghc ghc-prim liquid-fixpoint
    liquidhaskell mtl tagged tasty tasty-hunit template-haskell
    unordered-containers
  ];
  description = "Generate test-suites from refinement types";
  license = stdenv.lib.licenses.mit;
}
