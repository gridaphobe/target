{ mkDerivation, array, base, containers, deepseq, directory
, exceptions, filepath, ghc, ghc-paths, ghc-prim, liquid-fixpoint
, liquidhaskell, mtl, pretty, process, stdenv, syb, tagged, tasty
, tasty-hunit, template-haskell, text, text-format, transformers
, unordered-containers, vector
}:
mkDerivation {
  pname = "target";
  version = "0.1.0.0";
  src = (import <nixpkgs> {}).haskellFilterSource ["bench" "examples" "test"] ./.;
  doCheck = false;
  buildDepends = [
    base containers directory exceptions filepath ghc ghc-paths
    liquid-fixpoint liquidhaskell mtl pretty process syb tagged
    template-haskell text text-format transformers unordered-containers
    vector
  ];
  testDepends = [
    array base containers deepseq ghc ghc-prim liquid-fixpoint
    liquidhaskell mtl tagged tasty tasty-hunit template-haskell
    unordered-containers
  ];
  description = "Generate test-suites from refinement types";
  license = stdenv.lib.licenses.mit;
}
