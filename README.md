# Simply typed lambda calculus
An implementation of the simply typed λ-calculus in Haskell, along with an illustration that simply-typed terms are strongly normalizing.

## What's included
- A way to construct terms in the simlpy typed λ-calculus. This includes `variables`, typed `abstractions`, and `applications`
- Helper functions for constructing `Church numerals` and corresponding terms for operations such as addition & multiplication
- Implementations for `α-conversion`, `β-reduction`, normalization, and type checking
- A way to construct higher-order numeric functions (functionals)

The above are combined into a method for calculating the upper bound for the number of reductions for a given term. This is used to show the upper bound decreases with each reduction step and hence illustrates well-typed terms are strongly normalizing.

## Local setup
You'll need `ghci` and its dependencies. The easiest way to install these is with [GHCup](https://www.haskell.org/ghcup/install/).

## Running locally
Start an interactive shell and load the supplied module.
```bash
ghci simply-typed-lambda-calculus.hs
```
From here you're able to construct terms and apply them to the supplied operations mentioned above.
 
## Example usage
To construct a church numeral use the `numeral` function. For a refresher on Church encoding click [here](https://en.wikipedia.org/wiki/Church_encoding#Church_numerals).
```
ghci> numeral 1
\f: o -> o . \x: o . f x
```
This looks correct.

Let's try adding two together with `add`
```
ghci> (numeral 1) `add` (numeral 1)
(\m: (o -> o) -> o -> o . \n: (o -> o) -> o -> o . \f: o -> o . \x: o . m f (n f x)) (\f: o -> o . \x: o . f x) (\f: o -> o . \x: o . f x)
```

Wow ok, let's try normalizing it to get something vaguely recognisable.

```
ghci> normalize it
13 -- (\m: (o -> o) -> o -> o . \n: (o -> o) -> o -> o . \f: o -> o . \x: o . m f (n f x)) (\f: o -> o . \x: o . f x) (\f: o -> o . \x: o . f x)
11 -- (\a: (o -> o) -> o -> o . \b: o -> o . \c: o . (\f: o -> o . \x: o . f x) b (a b c)) (\f: o -> o . \x: o . f x)
9 -- \d: o -> o . \b: o . (\b: o -> o . \c: o . b c) d ((\f: o -> o . \x: o . f x) d b)
8 -- \d: o -> o . \b: o . (\a: o . d a) ((\f: o -> o . \x: o . f x) d b)
4 -- \d: o -> o . \b: o . d ((\f: o -> o . \x: o . f x) d b)
3 -- \d: o -> o . \b: o . d ((\a: o . d a) b)
2 -- \d: o -> o . \b: o . d (d b)
```

This prints each reduction step along with the upper bound for the remaining reduction steps. Looking at the final form we see the church encoding for 2, which is correct.

For some more involved examples and examples of features working in isolation, such as `α-conversion`, take a look at `Spec.pdf`
