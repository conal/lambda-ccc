default: go

go:	Examples
	./Examples

play:
	hermit Examples.hs -v0 -opt=LambdaCCC.Interactive

# %.o: ../dist $*.hs
# 	ghc $*.hs

Examples: ../dist Examples.hs
	time ghc -fforce-recomp -fplugin=LambdaCCC.Plugin -O -dcore-lint Examples.hs
# 	ghc Examples.hs

# Why the -fforce-recomp? I guess GHC doesn't notice that the plugin has
# changed. Odd, since it does seem notice when cabal-installing.

compile:
	cd .. ; make

compile-circat:
	cd ~/Haskell/circat ; make
	make compile-mono

compile-extras:
	cd ~/Tabula/Haskell/hermit-extras ; make
	make compile-mono

compile-mono:
	cd ~/Haskell/monomorph ; make
	make compile
