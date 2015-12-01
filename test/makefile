HERM = hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize

doit:
	time $(HERM) DoTree.hss resume && ./TreeTest

reify-done:
	echo "" | make reify ; echo

no-reify-done:
	echo "" | make no-reify ; echo

dont-done:
	echo "" | make dont ; echo

foo-done:
	echo "" | make foo ; echo

reify:
	$(HERM) DoTree.hss

no-reify:
	$(HERM) DoTreeNoReify.hss

dont:
	$(HERM) Dont.hss

foo:
	$(HERM) Foo.hss

compile:
	cd ../..; make

