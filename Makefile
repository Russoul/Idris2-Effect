INTERACTIVE ?= --interactive

.PHONY: test copy-ttc-for-test

MAJOR=0
MINOR=1
PATCH=0

copy-ttc-for-test:
	rm -rf ./tests/effect/test001/depends/*
	mkdir -p ./tests/effect/test001/depends/effect-${MAJOR}.${MINOR}.${PATCH}
	cp -R ./build/ttc/* ./tests/effect/test001/depends/effect-${MAJOR}.${MINOR}.${PATCH}/

test: copy-ttc-for-test
	${MAKE} -C ./tests test

build:
	idris2 --build effect.ipkg

install:
	idris2 --install effect.ipkg

clean:
	$(RM) -rf build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
