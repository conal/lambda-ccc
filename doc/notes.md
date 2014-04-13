# Miscellaneous project notes

[*From Haskell to hardware via cartesian closed categories*]: http://conal.net/blog/posts/haskell-to-hardware-via-cccs/ "blog post"

[*Overloading lambda*]: http://conal.net/blog/posts/overloading-lambda "blog post"

[*Optimizing CCCs*]: http://conal.net/blog/posts/optimizing-cccs "blog post"

[*Circuits as a bicartesian closed category*]: http://conal.net/blog/posts/circuits-as-a-bicartesian-closed-category "blog post"

[HERMIT]: http://www.ittc.ku.edu/csdl/fpg/software/hermit.html "project description"

[KURE]: http://www.ittc.ku.edu/csdl/fpg/software/kure.html "project description"

[circat]: https://github.com/conal/circat "Github repo"

[type-encode]: https://github.com/conal/type-encode "Github repo"

[`LambdaCCC.Lambda`]: ../src/LambdaCCC/Lambda.hs

[`LambdaCCC.ToCCC`]: ../src/LambdaCCC/ToCCC.hs

[`LambdaCCC.Reify`]: ../src/LambdaCCC/Reify.hs

[*System F with Type Equality Coercions* (expanded version)]: https://research.microsoft.com/en-us/um/people/simonpj/papers/ext-f/tldi22-sulzmann-with-appendix.pdf "paper by Martin Sulzmann, Manuel Chakravarty, and Simon Peyton Jones"

## Overview

This project explores a means of compiling Haskell programs in non-traditional ways.
The original motivation (and Conal's main focus) is compilation of Haskell to massively parallel, reconfigurable hardware (FPGAs and the like).

The overall flow:

*   GHC compiles Haskell source code to Core.
*   A [HERMIT]-based plugin ([`LambdaCCC.Reify`]) transforms the Core into other Core that *reifies* the original, i.e., constructs a representation of that Core designed for convenient manipulation (interpretation, translation, etc) by Haskell programs.
    *   Unlike Core, this new representation is a *generalized* algebraic data type (GADT) (in [`LambdaCCC.Lambda`]), which means that programs manipulating it are easier to write (not having to insert type representations explicitly), with typing bugs caught early.
        (A type-correct Haskell program can construct type-incorrect Core.)
    *   *Issue:* How much expressiveness do we lose?
    *   *Issue:* What to call this GADT representation in our documents and conversations?
*   The expression GADT is converted (in [`LambdaCCC.ToCCC`]) to a vocabulary of bicartesian closed categories (biCCCs).
    To get a particular interpretation, simply type-specialize the result of this conversion to a particular biCCC.
    The biCCC vocabulary is much like `Category` (in [`Control.Category`](http://hackage.haskell.org/package/base/docs/Control-Category.html)), and `Arrow`, `ArrowChoice`, and `ArrowApply` (in [`Control.Arrow`](http://hackage.haskell.org/package/base/docs/Control-Arrow.html)).
*   One such biCCC is "circuit generators", as implemented in the [circat] project.
    That project also produces circuit drawings (via graphviz) and Verilog generation.

There are a few blog posts about the motivation and technical directions:

*   [*From Haskell to hardware via cartesian closed categories*]
*   [*Overloading lambda*]
*   [*Optimizing CCCs*]
*   [*Circuits as a bicartesian closed category*]


## To do

Procedural:

*   Make GitHub issues for each of these to-do items, and either link to them here or eliminate this list.

Documentation:

*   Haddock:
    *   Write module overviews
    *   Fill in missing documentation for exports.

Design & implementation:

*   Finish separation of lambda expressions from the underlying primitives.
    There's a good start already, as the expression `E` (in [`LambdaCCC.Lambda`]) and the [conversion to biCCCs][`LambdaCCC.ToCCC`] are parametrized over a type constructor of primitives.
    The [reification plugin][`LambdaCCC.Reify`], however, doesn't yet know about this parametrization and so can only handle the primitives designed for [circat].
    *[Issue conal/lambda-ccc#4]*
*   Handle record field accessors, including type class methods.
*   Do something sensible with unboxed types, even if just avoiding them.
    For instance, an `Int` literal `1` gets reified as `appP (reifyEP I#) (reifyEP 1)`.
    With types shown, this sub-expression `(reifyEP 1)` becomes `(reifyEP @ Int# 1)` which is not well-kinded.
    (Similarly for the other `reifyEP` call.)
    I think an easy fix would be having `reifyOf` in [`Lambda.Reify`] only if the argument type has kind `*`.
*   Coercions and casts
    *   Handle them in the representation and translation.
    *   Check handling of `newtype`s, which are represented via a coercion.
*   Type-encoding, in which algebraic data types (LDTs) are converted to binary sums and products.
    (Sorry for the odd acronym. I like "ADT" to mean "abstract data type".)
    See the [type-encode] project.
    Conversion is working well for *regular* LDTs.
    *   Extend to GADTs.
        My understanding of [*System F with Type Equality Coercions* (expanded version)] is that GADTs are represented as regular LDTs, plus some type-level proofs.
        I'm hopeful that handling them will be fairly straightforward, fitting those type-level proofs into the reified representation (still at the type level).
        We'll see.
    *   Tie into [circat], interpreting the `encode` and `decode` conversions.
    *   I think we'll want to synthesize `Encodable` dictionaries in the plugin, which is not yet easy in HERMIT.


## Contributors

*   Conal Elliott: concept, design, implementation
*   Andy Gill: many helpful conversations about the project; exploring additional applications
*   Andrew Farmer: consulting on KURE & HERMIT
*   Neil Sculthorpe: consulting on KURE & HERMIT
*   Nicolas Frisby: consulting on KURE & HERMIT
*   Tabula: support for Conal's work on the project
*   Steve Teig (Tabula's founder, president, CTO): originally suggested the Haskell-to-hardware project; numerous technical conversations.

Please let me know if I've forgotten to mention you!
