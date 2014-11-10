HERM = hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize

doit:
	time $(HERM) DoTree.hss resume && ./TreeTest

reify:
	echo "" | make reify-continue ; echo

no-reify:
	echo "" | make no-reify-continue ; echo

reify-continue:
	$(HERM) DoTree.hss

no-reify-continue:
	$(HERM) DoTreeNoReify.hss

dont:
	$(HERM) Dont.hss

foo:
	$(HERM) Foo.hss
