default: go

go:	Examples
	./Examples

play:
	hermit Examples.hs -v0 -opt=LambdaCCC.Interactive Go.hss

# %.o: ../dist $*.hs
# 	ghc $*.hs

Examples: ../dist Examples.hs
	time ghc -fforce-recomp -fplugin=LambdaCCC.Plugin -O -dcore-lint Examples.hs

#  -fsimpl-tick-factor=1000

# For and :: RTRee N10 Bool -> Bool
#
# ghc: panic! (the 'impossible' happened)
#   (GHC version 7.10.3 for x86_64-apple-darwin):
# 	Simplifier ticks exhausted
#   When trying UnfoldingDone $dGenBuses_aaXT
#   To increase the limit, use -fsimpl-tick-factor=N (default 100)
#   If you need to do this, let GHC HQ know, and what factor you needed
#   To see detailed counts use -ddump-simpl-stats
#   Total ticks: 151525

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
