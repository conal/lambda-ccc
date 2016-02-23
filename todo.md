*   Terser simplification
*   Reification rules from dictionaries, e.g., `reify (fft :: ...)`, rather than the just the methods (`$fFFTPairPair_$cfft`), to save time later.


----

*   Multi-clock systems:
    semantic model and implementation.
*   Rethink allocation to use sets of spacetime slots.

*   Efficient incremental update.
    Use in histogram and counting sort.
*   Algorithms:
    *   Sorting:
        *   Radix sort
        *   Larger bitonic sort
        *   Batcher's odd-even merge sort
    *   Regular expression matching and other forms of parsing.
        Possible tools:
        *   Languages as star [semirings](https://en.wikipedia.org/wiki/Semiring).
            Among other references, see [*A Very General Method of Computing Shortest Paths*].
        *   Derivatives of regular languages and beyond.
            (See [this StackExchange discussion](https://cstheory.stackexchange.com/questions/3280/generalizations-of-brzozowskis-method-of-derivatives-of-regular-expressions-to) for some pointers.)
*   Computation with buffering
*   Fast compilation
*   Linear algebra via tries.
    `forkT` and `joinT`.
*   Automatic differentiation for machine learning
*   Variable bit width `Int`s
*   Streams as first-class values
*   Automatically set up data transfers around a circuit, including repetition as in matrix multiplication.
*   Learn how to declare RAMs.
    Stylus does not automatically choose to use RAMs from `reg` declarations.
