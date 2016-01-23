default: go

go:	Examples
	./Examples

play:
	hermit Examples.hs -v0 -opt=LambdaCCC.Interactive Go.hss

# %.o: ../dist $*.hs
# 	ghc $*.hs

Examples: ../dist Examples.hs
	time ghc -fforce-recomp -fplugin=LambdaCCC.Plugin -O -dcore-lint Examples.hs
# 	ghc Examples.hs

# Why the -fforce-recomp? I guess GHC doesn't notice that the plugin has
# changed. Odd, since it does seem notice when cabal-installing.

compile:
	cd .. ; make

circat:
	cd ../../circat ; make
	make mono

extras:
	cd ../../hermit-extras ; make
	make mono

mono:
	cd ../../monomorph ; make
	make compile
