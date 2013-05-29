install:
	cabal install --force-reinstalls

run:
	hermit test/Simple.hs -opt=LambdaCCC +Main
