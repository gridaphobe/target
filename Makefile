.PHONY: bench map-coverage

bench:
	rm -f bench/bench.log
	cabal configure -O2 --enable-benchmarks
	cabal build
	cabal exec ./dist/build/bench/bench 2>&1 | tee bench/bench.log

map-coverage:
	rm -f *.tix
	rm -rf _results
	mkdir -p _results
	cabal exec ghc -- --make -threaded -fforce-recomp -fhpc -iexamples:src -O2 bench/MapCoverage.hs -hide-package unbounded-delays
	cabal exec ./bench/MapCoverage 2>&1 | tee _results/MapCoverage.log
