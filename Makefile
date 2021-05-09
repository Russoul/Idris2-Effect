include config.mk

INTERACTIVE ?= --interactive

.PHONY: build install install-src clean test copy-ttc-for-test

IDRIS_MAJOR=0
IDRIS_MINOR=3
IDRIS_PATCH=0

export IDRIS2_VERSION := ${IDRIS_MAJOR}.${IDRIS_MINOR}.${IDRIS_PATCH}
IDRIS_NAME_VERSION := idris2-${IDRIS2_VERSION}

MAJOR=0
MINOR=1
PATCH=0

copy-ttc-for-test:
	rm -rf ./tests/effect/test001/depends/*
	mkdir -p ./tests/effect/test001/depends/effect-${MAJOR}.${MINOR}.${PATCH}
	cp -R ./build/ttc/* ./tests/effect/test001/depends/effect-${MAJOR}.${MINOR}.${PATCH}/
	rm -rf ./tests/effect/test002/depends/*
	mkdir -p ./tests/effect/test002/depends/effect-${MAJOR}.${MINOR}.${PATCH}
	cp -R ./build/ttc/* ./tests/effect/test002/depends/effect-${MAJOR}.${MINOR}.${PATCH}/

test: copy-ttc-for-test
	${MAKE} -C ./tests test

build:
	idris2 --build effect.ipkg

install:
	idris2 --install effect.ipkg

install-src:
	mkdir -p ${PREFIX}/${IDRIS_NAME_VERSION}-src
	cp -R src/* ${PREFIX}/${IDRIS_NAME_VERSION}-src/

clean:
	$(RM) -rf build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
