INTERACTIVE ?= --interactive

.PHONY: testbin test

testbin:
	idris2 --build tests.ipkg

test: testbin
	./build/exec/runtests effect $(INTERACTIVE) --only $(only)

clean:
	$(RM) -r build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
