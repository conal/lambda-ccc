HERM = hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize

doit:
	time $(HERM) DoTree.hss resume && ./TreeTest

reify:
	echo "" | make reify-continue ; echo

no-reify:
	echo "" | make no-reify-continue ; echo

dont:
	echo "" | make dont-continue ; echo

foo:
	echo "" | make foo-continue ; echo

reify-continue:
	$(HERM) DoTree.hss

no-reify-continue:
	$(HERM) DoTreeNoReify.hss

dont-continue:
	$(HERM) Dont.hss

foo-continue:
	$(HERM) Foo.hss
