all: l3c

l3c:
	runhaskell Setup.hs configure --user
	runhaskell Setup.hs build
	rm -rf bin/
	cp -r shellbins/ bin/
	chmod +x bin/*
clean:
	rm -rf bin/
	rm -rf dist/

test:
	cabal configure --enable-tests
	cabal build
	cabal test
	cat dist/test/c0c-0.0-c0c-test.log

benchmarks:
	cabal configure --enable-benchmarks
	cabal build
	cabal bench --benchmark-options="-o report.html"

