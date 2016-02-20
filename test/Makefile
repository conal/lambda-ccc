default: go

go:	Examples
	./Examples

play:
	hermit Examples.hs -v0 -opt=LambdaCCC.Interactive Play.hss

F:      ../dist F.hs Makefile
	ghc -O -fforce-recomp -fplugin=LambdaCCC.Plugin F

goF:    F
	./F

Z:      ../dist Z.hs Makefile
	ghc -O -fforce-recomp -fplugin=LambdaCCC.Plugin -package circat Z

goZ:    Z
	./Z

# ghc -O -fplugin=LambdaCCC.Plugin -fplugin-opt=LambdaCCC.Reify:verbose -dppr-case-as-let -dsuppress-idinfo -dcore-lint V

playF:
	hermit F.hs -v0 -opt=LambdaCCC.Interactive Play.hss

playZ:
	hermit Z.hs -v0 -opt=LambdaCCC.Interactive Play.hss -- -package circat

-- gf: ../dist G.hs F.hs G.iface F.iface Makefile

g:
	ghc G.hs

Examples: ../dist ../../shaped-types/dist Examples.hs Makefile
	time ghc -O -fforce-recomp -fplugin=LambdaCCC.Plugin Examples

# 	time ghc -O Examples.hs -fforce-recomp -fplugin=LambdaCCC.Plugin -dcore-lint

X: ../dist X.hs Makefile
	time ghc X.hs -fforce-recomp -fplugin=LambdaCCC.Plugin -O -dcore-lint

goX:	X
	./X

# 
# -ddump-simpl -ddump-simpl-stats -ddump-to-file 

SH = ../../shaped-types/dist/build/ShapedTypes

%.iface: $(SH)/%.hi
	ghc --show-iface $(SH)/$*.hi > $*.iface

ifaces: Pair.iface Vec.iface RPow.iface LPow.iface Scan.iface FFT.iface

%.hi %.o: ../dist %.hs
	ghc $*.hs

%.iface: %.hi
	ghc --show-iface $*.hi > $*.iface

shaped: compile
	cd ../../shaped-types ; make

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

unregister-all:
	@echo "Unregistering:"
	@ghc-pkg unregister lambda-ccc    --force || true
	@ghc-pkg unregister monomorph     --force || true
	@ghc-pkg unregister hermit-extras --force || true
	@ghc-pkg unregister circat        --force || true

recompile-all: unregister-all
	cd ../../circat	       ; cabal clean && cabal install
	cd ../../hermit-extras ; cabal clean && cabal install
	cd ../../monomorph     ; cabal clean && cabal install
	cd ..		       ; cabal clean && cabal install
