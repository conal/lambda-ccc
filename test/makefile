doit:
	time hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize DoTree.hss resume && ./TreeTest

reify:
	echo "" | make reify-continue ; echo

no-reify:
	echo "" | make no-reify-continue ; echo

reify-continue:
	hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize DoTree.hss

no-reify-continue:
	hermit TreeTest.hs -v0 -opt=LambdaCCC.Monomorphize DoTreeNoReify.hss

