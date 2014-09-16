.PHONY: bench map-coverage

bench:
	rm -f bench/bench.log
	cabal configure -O2 --enable-benchmarks
	cabal build
	cabal exec ./dist/build/bench/bench 2>&1 | tee bench/bench.log

map-coverage:
	rm -f MapCoverage.tix _results/MapCoverage-*.tix _results/Map-*.tsv _results/MapCoverage-*.log
	mkdir -p _results
	cabal exec ghc -- --make -threaded -fforce-recomp -fhpc -iexamples:src -O2 bench/MapCoverage.hs -hide-package unbounded-delays
	for t in 1 5 10 15 20 25 30; do \
	    cabal exec ./bench/MapCoverage -- $$t +RTS -N8 -RTS 2>&1 | tee _results/MapCoverage-$$t.log; \
	    mv MapCoverage.tix _results/MapCoverage-$$t.tix; \
	done


rbtree-coverage:
	rm -f RBTreeCoverage.tix _results/RBTreeCoverage-*.tix _results/RBTree-*.tsv _results/RBTreeCoverage-*.log
	mkdir -p _results
	cabal exec ghc -- --make -threaded -fforce-recomp -fhpc -iexamples:src -O2 bench/RBTreeCoverage.hs -hide-package unbounded-delays
	for t in 1 5 10 15 20 25 30; do \
	    cabal exec ./bench/RBTreeCoverage -- $$t +RTS -N4 -RTS 2>&1 | tee _results/RBTreeCoverage-$$t.log; \
	    mv RBTreeCoverage.tix _results/RBTreeCoverage-$$t.tix; \
	done

xmonad-coverage:
	rm -f StackSetCoverage.tix _results/StackSetCoverage-*.tix _results/Xmonad.StackSet-*.tsv _results/XMonad.StackSetCoverage-*.log
	mkdir -p _results
	cabal exec ghc -- --make -threaded -fforce-recomp -fhpc -iexamples:src -O2 bench/XMonad/StackSetCoverage.hs -hide-package unbounded-delays
	for t in 1 5 10 15 20 25 30; do \
	    cabal exec ./bench/XMonad/StackSetCoverage -- $$t +RTS -N4 -RTS 2>&1 | tee _results/XMonad.StackSetCoverage-$$t.log; \
	    mv StackSetCoverage.tix _results/StackSetCoverage-$$t.tix; \
	done
