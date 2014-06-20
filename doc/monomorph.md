# Notes on monomorphization

I think monomorphization makes a good first step in the pipeline.
Some motivation:

*   Supports monomorphic back-ends like circuits with fixed data representations, simplifying down to tuples of unboxed types (not need for pointers).
*   As I understand it, CCCs are models of the typed lambda calculus, but not polymorphic lambda calculi.
    I don't know where the boundaries are.
*   Hopefully it will be the one and only place where we need to inline.
    I want to handle inlining very carefully, since it leads to code blow-up.
    Take care so that we do no more inlining than needed and we do it efficiently.
    I hope that separating from other transformations will help us do it well.

