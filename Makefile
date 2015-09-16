install:
	cabal install -j1 --disable-documentation

run:
	hermit test/Simple.hs -opt=LambdaCCC +Main

demo:
	hermit test/Plus.hs -opt=LambdaCCC +Plus

tags: dist
	cd src ; find . -name '*.*hs' | grep -v Junk | grep -v Old | xargs hasktags -e

# Hack: depend on dist, which updates whenever we build. Is there a standard
# GNU make technique for running a rule whenever the target is called for?
