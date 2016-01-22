Convert lambda expressions to CCC combinators and then to circuits.

Additional info:

*   [Project notes](doc/notes.md).
*   The talk [From Haskell to Hardware via CCCs](https://github.com/conal/talk-2015-haskell-to-hardware).
*   Instructions in test/Tests.hs.

Dependencies:

*   GHC 7.10.3 or better
*   [KURE](https://github.com/ku-fpg/kure)
*   [HERMIT](https://github.com/ku-fpg/hermit)
*   [hermit-extras](http://github.com/conal/hermit-extras)
*   [circat](https://github.com/conal/circat), for circuit specification, display, and conversion to netlists.
*   [monomorph](https://github.com/conal/monomorph) for monomorphization (to be moved into lambda-ccc).

To try out:

*   `cabal install` circat and lambda-ccc (in that order)
*   In a shell, `cd` to lambda-ccc/test, and type `make`.
    If all works, you'll see something like the following output:

        bash-3.2$ ./test
        [starting HERMIT v0.5.0.1 on TreeTest.hs]
        % ghc TreeTest.hs -fforce-recomp -O2 -dcore-lint -fsimple-list-literals -fexpose-all-unfoldings -fplugin=LambdaCCC.Monomorphize -fplugin-opt=LambdaCCC.Monomorphize:-v0 -fplugin-opt=LambdaCCC.Monomorphize:DoTree.hss -fplugin-opt=LambdaCCC.Monomorphize:resume -fplugin-opt=LambdaCCC.Monomorphize:*: -v0

        real	0m6.098s
        user	0m5.968s
        sys	0m0.245s
        let f = \ ds -> abst (repr ds) in let f0 = \ ds -> let (a1,a'1) = repr (repr ds) in abst (repr (f a1) + repr (f a'1)) in let f1 = \ ds -> let (a1,a'1) = repr (repr ds) in abst (repr (f0 a1) + repr (f0 a'1)) in let f2 = \ eta -> let a = repr eta in abst (a * a) in let f3 = \ eta -> abst (let (a1,a'1) = repr (repr eta) in abst (f2 a1,f2 a'1)) in let f4 = \ eta -> abst (let (a1,a'1) = repr (repr eta) in abst (f3 a1,f3 a'1)) in \ x -> let (a1,a'1) = repr (let (a1,a'1) = repr (repr x) in abst (f4 a1,f4 a'1)) in repr (f1 a1) + repr (f1 a'1)
        Wrote out/sumSquare-t3.pdf
        Wrote out/sumSquare-t3.v.txt

The `.v.txt` file is Verilog code. Additionally the PDF will be displayed if the display code figures out how to on your system.

To play with examples, edit test/Example.hs, and re-run "make".
