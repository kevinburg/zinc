all: l1c

l1c:
	runhaskell Setup.hs configure --user
	runhaskell Setup.hs build
	rm -rf bin/
	cp -r shellbins/ bin/
	chmod +x bin/*
clean:
	rm -rf bin/
	rm -rf dist/
