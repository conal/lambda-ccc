# Notes on monomorphization

[type-encode]: https://github.com/conal/type-encode "Haskell library"

[let-float from case alternative]: https://github.com/ku-fpg/hermit/issues/113 "HERMIT issue"

[over-eager `letNonRecSubstR`?]: https://github.com/ku-fpg/hermit/issues/114 "HERMIT issue"

[Eliminate impossible case alternatives?]: https://github.com/ku-fpg/hermit/issues/110 "HERMIT issue"

## Motivation

*   Supports monomorphic back-ends like circuits with fixed data representations, simplifying down to tuples of unboxed types (not need for pointers).
*   As I understand it, CCCs are models of the typed lambda calculus, but not polymorphic lambda calculi.
    I don't know where the boundaries are.
*   Hopefully it will be the one and only place where we need to inline.
    I want to handle inlining very carefully, since it leads to code blow-up.
    Take care so that we do no more inlining than needed and we do it efficiently.
    I hope that separating from other transformations will help us do it well.

## Context

My current overall plan (as of June 20, 2014) is to apply a few transformation passes:

*   Monomorphize.
*   Standardize types:
    *   Eliminate all but a few "standard types" supported by CCCs:
        `()` and binary sums, binary products, and functions over standard types.
        Probably also `Void`, `Bool`, and maybe something like `Int#`.
    *   For some types, use the `Encodable` class in `LambdaCCC.Encodable`, which has `encode` and `decode` methods for converting to and from a standard encoding.
        In particular, use these encodings for monomorphic specializations of GADTs, including length-typed vectors and depth-typed perfect leaf trees.
    *   For other types, use a simple encoding as balanced binary sums of binary products.
        See [type-encode].

## Implementation

How might we implement monomorphization on Core?

*   Start with a monomorphic expression (probably a type specialization of a polymorphic function such as `sum` or `scanl`).
*   For every application of a named polymorphic value (usually a function) to type, dictionary, and coercion arguments, make a specialized version of that definition.
*   Memoize the specialization for reuse.
    *   Especially useful for trees, so that the number of specialized versions is linear in the depth, i.e., logarithmic in the number of elements.
    *   For `fmap` or `foldMap` on top-down trees, each monomorphic specialization will call the next smaller one twice.
        Not really, since I'm using a uniform pair functor (and will generalize to an arbitrary `Functor`, `Foldable`, `Traversable`, `Applicative`, `Monad`).
        Instead of two calls, there will be just one, together with a `fmap` or `foldMap` over uniform pairs.
        That `fmap` or `foldMap` will get type specialized just once.
    *   For vectors, each specialization will call the next smaller once.
*   I can cache these definitions into HERMIT's definition stash for reuse.
*   I don't think I need to specialize on dictionaries, since the dictionary can be passed into the monomorphic function.
    On the other hand, it's probably a very good idea so that we can simplify.
    I'd like not to have to use the dictionary itself in the stash key.
    How can I know that the dictionary is fully determined by the type arguments?
    Seeing `f ty dict`, how do I know that this `dict` was inserted by the type-checker based on `f ty`?

Sketch of a simple prototype:

*   Repeatedly:
    *   Reach into an expression to find a name applied to type, dictionary, and coercion arguments.
        Unfold, simplify, and `let-intro`, using the expression itself to generate a name.
    *   Hoist the `let` up as far as it can go, using `let-intro` from the top.
*   Remember when we introduce a name by storing the generated variable in definition stash.
    The RHS of that def doesn't matter.
    Before unfolding etc, check the stash, i.e., memoize.
*   Prune away impossible alternatives in `case` expressions by looking for coercion parameters with uninhabited kinds in constructor patterns (for GADTs).
    I don't know how to do this step, and I don't know how to generate finite code without it.
    See the HERMIT's issue [Eliminate impossible case alternatives?].

## Try it!

In lambda-ccc/test,

```haskell
bash-3.2$ hermit Mono.hs -v0 -opt=LambdaCCC.Monomorphize DoMono.hss
[starting HERMIT v0.5.0.0 on Mono.hs]
% ghc Mono.hs -fforce-recomp -O2 -dcore-lint -fsimple-list-literals -fexpose-all-unfoldings -fplugin=LambdaCCC.Monomorphize -fplugin-opt=LambdaCCC.Monomorphize:-v0 -fplugin-opt=LambdaCCC.Monomorphize:DoMono.hss -fplugin-opt=LambdaCCC.Monomorphize:*: -v0
sum4 :: Tree (S (S Z)) Int -> Int
sum4 = sum (Tree (S (S Z))) Int ($fFoldableTree (S (S Z))) $fNumInt
hermit<1> one-td monomorphize >>> try (any-bu bindUnLetIntroR) >>> try (any-bu let-float') >>> try simplifyAllRhs >>> try unshadow
<1> memo save: sum_@_(Tree_(S_(S_Z)))_@_Int_($fFoldableTree_@_(S_(S_Z)))_$fNumInt
g :: Tree (S (S Z)) Int -> Sum Int
g =
  foldMap
    (Tree (S (S Z)))
    ($fFoldableTree (S (S Z)))
    Int
    (Sum Int)
    ($fMonoidSum Int $fNumInt)
    (product1 Int |> (~# :: (Int -> Int) ~R (Int -> Sum Int)))
sum4 :: Tree (S (S Z)) Int -> Int
sum4 =
  g |> (~# :: (Tree (S (S Z)) Int -> Sum Int) ~R (Tree
                                                (S (S Z)) Int -> Int))
hermit<2> one-td monomorphize >>> try (any-bu bindUnLetIntroR) >>> try (any-bu let-float') >>> try simplifyAllRhs >>> try unshadow
<1> memo save: foldMap_@_(Tree_(S_(S_Z)))_($fFoldableTree_@_(S_(S_Z)))_@_Int_@_(Sum_Int)_($fMonoidSum_@_Int_$fNumInt)
x :: (Int -> Sum Int) -> Tree (S (S Z)) Int -> Sum Int
x = \ f ds ->
  case ds of wild (Sum Int)
    L (~# :: S (S Z) ~N Z) a1 -> f a1
    B n1 (~# :: S (S Z) ~N S n1) uv ->
      $fFoldablePair_$cfoldMap
        (Tree n1 Int)
        (Sum Int)
        ($fMonoidSum Int $fNumInt)
        ($fFoldableTree_$cfoldMap n1
           Int (Sum Int) ($fMonoidSum Int $fNumInt) f)
        uv
g :: Tree (S (S Z)) Int -> Sum Int
g = x (product1 Int |> (~# :: (Int -> Int) ~R (Int -> Sum Int)))
sum4 :: Tree (S (S Z)) Int -> Int
sum4 =
  g |> (~# :: (Tree (S (S Z)) Int -> Sum Int) ~R (Tree
                                                (S (S Z)) Int -> Int))
hermit<3> ...
```

## Misc issues

*   HERMIT issue [let-float from case alternative]:
    *   The `letFloatExprR` transformation doesn't cover floating out of case alternatives.
    *   I added a `letFloatCaseAltR` in `LambdaCCC.Monomorphize`.
*   HERMIT issue [over-eager `letNonRecSubstR`?].
    For now, I'm avoiding `letNonRecSubstR`, which means I can't use `simplifyR` or `bashR`.
    Instead, I'm using `bashUsingE` and a version of the standard `bash` rewriters that omits `letNonRecSubstR`.
*   I worry that the repeated use of `one-td` in `one-td monomorphize` is going to be inherently inefficient, leading to a lot of wasted re-traversal.
    I've had a terrible time with progressively slow transformation, and I want to learn how to produce more efficient HERMIT plugins while keeping a modular programming style, especially during experimentation.
