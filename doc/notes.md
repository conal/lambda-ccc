# Miscellaneous project notes

[*From Haskell to hardware via cartesian closed categories*]: http://conal.net/blog/posts/haskell-to-hardware-via-cccs/ "blog post"

[*Overloading lambda*]: http://conal.net/blog/posts/overloading-lambda "blog post"

[*Optimizing CCCs*]: http://conal.net/blog/posts/optimizing-cccs "blog post"

[*Circuits as a bicartesian closed category*]: http://conal.net/blog/posts/circuits-as-a-bicartesian-closed-category "blog post"

[HERMIT]: http://www.ittc.ku.edu/csdl/fpg/software/hermit.html "project description"

[KURE]: http://www.ittc.ku.edu/csdl/fpg/software/kure.html "project description"

[circat]: https://github.com/conal/circat "Github repo"

## Overview

This project explores a means of compiling Haskell programs in non-traditional ways.
The original motivation (and Conal's main focus) is compilation of Haskell to massively parallel, reconfigurable hardware (FPGAs and the like).

The overall flow:

*   GHC compiles Haskell source code to Core.
*   A [HERMIT]-based plugin (`LambdaCCC.Reify`) transforms the Core into other Core that *reifies* the original, i.e., constructs a representation of that Core designed for convenient manipulation (interpretation, translation, etc) by Haskell programs.
    *   Unlike Core, this new representation is a *generalized* algebraic data type (GADT) (in `LambdaCCC.Lambda`), which means that programs manipulating it are easier to write (not having to insert type representations explicitly), with typing bugs caught early.
        (A type-correct Haskell program can construct type-incorrect Core.)
    *   *Issue:* How much expressiveness do we lose?
    *   *Issue:* What to call this GADT representation in our documents and conversations?
*   The expression GADT is converted (in `LambdaCCC.ToCCC`) to a vocabulary of bicartesian closed categories (biCCCs).
    To get a particular interpretation, simply type-specialize the result of this conversion to a particular biCCC.
    The biCCC vocabulary is much like `Category` (in `Control.Category`), and `Arrow`, `ArrowChoice`, and `ArrowApply` (in `Control.Arrow`).
*   One such biCCC is "circuit generators", as implemented in the [circat] project.
    That project also produces circuit drawings (via graphviz) and Verilog generation.

There are a few blog posts about the motivation and technical directions:

*   [*From Haskell to hardware via cartesian closed categories*]
*   [*Overloading lambda*]
*   [*Optimizing CCCs*]
*   [*Circuits as a bicartesian closed category*]


## To do

Documentation:

*   Add more links to these notes, including `Control.Category` and friends.


## Contributors

*   Conal Elliott: concept, design, implementation
*   Andy Gill: many helpful conversations about the project; exploring additional applications
*   Andrew Farmer: consulting on KURE & HERMIT
*   Neil Sculthorpe: consulting on KURE & HERMIT
*   Nicolas Frisby: consulting on KURE & HERMIT
*   Tabula: supporting Conal's work on the project
*   Steve Teig (Tabula's founder, president, CTO): originally suggested the Haskell-to-hardware project; numerous in-depth conversations.

Please let me know if I've forgotten to mention you!
