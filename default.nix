{ fetchgitLocal }:
{ mkDerivation, array, base, containers, deepseq, directory
, exceptions, filepath, ghc, ghc-paths, ghc-prim, hint
, liquid-fixpoint, liquidhaskell, mtl, pretty, process, QuickCheck
, stdenv, syb, tagged, tasty, tasty-hunit, template-haskell, text
, text-format, th-lift, transformers, unordered-containers, vector
, z3, tasty-ant-xml
}:
mkDerivation {
  pname = "target";
  version = "9.9.9.9";
  src = fetchgitLocal ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base containers directory exceptions filepath ghc ghc-paths
    liquid-fixpoint liquidhaskell mtl pretty process QuickCheck syb
    tagged template-haskell text text-format th-lift transformers
    unordered-containers vector
  ];
  executableHaskellDepends = [ base hint ];
  testHaskellDepends = [
    array base containers deepseq ghc ghc-prim liquid-fixpoint
    liquidhaskell mtl tagged tasty tasty-hunit template-haskell
    unordered-containers tasty-ant-xml
  ];
  testSystemDepends = [ z3 ];
  description = "Generate test-suites from refinement types";
  license = stdenv.lib.licenses.mit;
}
