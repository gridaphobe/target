# Target
Target is a library for testing Haskell functions based on refinement type
specifications.

## Getting Started
First things first, get Target from Hackage

```
$ cabal install target
```

You'll also need a recent version of [Z3](http://z3.codeplex.com/)
or [CVC4](http://cvc4.cs.nyu.edu/web/).

## Testing with Target
To get acquainted with refinement types and Target, let's examine
a small grading library called `Scores`.

### First Steps

We'll need to import two modules from Target.
[`Test.Target`](http://hackage.haskell.org/package/target/docs/Test-Target.html)
exports the main testing API, and
[`Test.Target.Targetable`](http://hackage.haskell.org/package/target/docs/Test-Target-Targetable.html)
exports the
[`Targetable`](http://hackage.haskell.org/package/target/docs/Test-Target-Targetable.html#t:Targetable)
type-class, which represents types for which we can
generate constrained values. We'll need the latter module for one of
the later examples when we define our own datatype.

```haskell
module Scores where

import Test.Target
import Test.Target.Targetable
```

### Refinement Types
A refinement type decorates the basic Haskell types
with logical predicates drawn from an efficiently decidable
theory. For example,

```haskell
{-@ type Nat   = {v:Int | 0 <= v} @-}
{-@ type Pos   = {v:Int | 0 <  v} @-}
{-@ type Rng N = {v:Int | 0 <= v && v < N} @-}
```

are refinement types describing the set of integers that are
non-negative, strictly positive, and in the interval `[0, N)`
respectively. We will also build up function and collection
types over base refinement types like the above.

### Base Types
Let's write a function `rescale` that takes a source range `[0,r1)`,
a target range `[0,r2)`, and a score `n` from the source range,
and returns the linearly scaled score in the target range.

For example, `rescale 5 100 2` should return `40`.
Here's a first attempt at `rescale`

```haskell
{-@ rescale :: r1:Nat -> r2:Nat -> s:Rng r1 -> Rng r2 @-}
rescale r1 r2 s = s * (r2 `div` r1)
```

Let's load our code into GHCi and test it!

```haskell
ghci> :set -XTemplateHaskell
ghci> :l Scores.hs
ghci> target rescale 'rescale "Scores.hs"
```

The main function Target exports is
[`target`](http://hackage.haskell.org/package/target/docs/Test-Target.html#v:target)

```haskell
target :: Testable f => f -> TH.Name -> FilePath -> IO ()
```

which drives the entire testing process. It also provides
[`targetWith`](http://hackage.haskell.org/package/target/docs/Test-Target.html#v:targetWith)
to customize some of the options, and
[`targetResult`](http://hackage.haskell.org/package/target/docs/Test-Target.html#v:targetResult)
which returns the test outcome instead of printing it.

(Since the refinement type specifications are given in special
comments, we use Template Haskell to give target the exact name
of the function we want to test. Unfortunately we can't extract
the path to the module from the Template Haskell name, so we
have to provide it separately..)

Unfortunately, target quickly responds with

```haskell
Found counter-example: (1, 0, 0)
```

Indeed, `rescale 1 0 0` results in `0` which is not in the target
`Rng 0`, as the latter is empty! We could fix this in various ways,
e.g. by requiring the ranges are non-empty:

```haskell
{-@ rescale :: r1:Pos -> r2:Pos -> s:Rng r1 -> Rng r2 @-}
```

Now, Target accepts the function and reports

```haskell
ghci> target rescale 'rescale "Scores.hs"
OK. Passed all tests.
```

Using the refinement type *specification* for `rescale`,
Target systematically tests the *implementation* by generating
all valid inputs up to a given depth bound (defaulting to 5)
that respect the pre-conditions, running the function, and
checking that the output satisfies the post-condition.

### Containers
Suppose we have normalized all scores to be out of `100`

```haskell
{-@ type Score = Rng 100 @-}
```

Now we'll write a function to compute a *weighted* average
of a list of scores.

```haskell
{-@ average :: [(Int, Score)] -> Score @-}
average []  = 0
average wxs = total `div` n
  where
    total   = sum [w * x | (w, x) <- wxs ]
    n       = sum [w     | (w, _) <- wxs ]
```

It can be tricky to *verify* this function as it requires non-linear reasoning
about an unbounded collection. However, we can gain a great degree of confidence by
systematically testing it using the type specification; indeed, Target responds:

```haskell
ghci> target average 'average "Scores.hs"
Found counter-example: [(0,0)]
```

Clearly, an unfortunate choice of weights can trigger a divide-by-zero; we can fix
this by requiring the weights be non-zero:

```haskell
{-@ average :: [({v:Int | v /= 0}, Score)] -> Score @-}
```

but now Target responds with

```haskell
ghci> target average 'average "Scores.hs"
Found counter-example: [(-3,3),(3,0)]
```

which also triggers the divide-by-zero! Let's play it safe and require positive weights,

```haskell
{-@ average :: [(Pos, Score)] -> Score @-}
```

at which point Target reports that all tests pass.

### Ordered Containers
The very nature of our business requires that at the end of the day,
we order students by their scores. We can represent ordered lists by
requiring the elements of the tail `t` to be greater than the head `h`:

```haskell
{-@ data OrdList a
      = ONil
      | OCons {h :: a, t :: OrdList {v:a | h <= v}}
  @-}
```

Target can only test functions that operate on `Targetable` types, so we'll
also need to make `OrdList` `Targetable`. We could write our own instance, but
they turn out to be quite mechanical, so instead we'll use `GHC.Generics` to
derive an instance automatically.

```haskell
data OrdList a = ONil | OCons a (OrdList a)
  deriving Generic

instance Targetable a => Targetable (OrdList a)
```

We can now write a function to insert a score into an ordered list:

```haskell
{-@ insert :: (Ord a) => a -> OrdList a -> OrdList a @-}
```

Target automatically generates all ordered lists (up to a given depth)
and executes `insert` to check for any errors.

### Structured Containers
Everyone has a few bad days. Let us write a function that takes the
`best k` scores for a particular student. That is, the output
must satisfy a *structural* constraint -- that its size
equals `k`. We can encode the size of a list with a logical
measure function:

```haskell
{-@ measure len :: [a] -> Int
    len []      = 0
    len (x:xs)  = 1 + len xs
  @-}
```

Now, we can stipulate that the output indeed has `k` scores:

```haskell
{-@ best :: k:Nat -> [Score] -> {v:[Score] | k = len v} @-}
best k xs = take k $ reverse $ sort xs
```

Now, Target quickly finds a counterexample:

```haskell
ghci> target best 'best "Scores.hs"
Found counter-example: (2,[])
```

Of course -- we need to have at least `k` scores to start with!

```haskell
{-@ best :: k:Nat -> {v:[Score] | k <= len v}
         -> {v:[Score] | k = len v}
  @-}
```

and now, Target is assuaged and reports no counterexamples.

Note that we don't have to write a custom `Targetable` instance
to generate lists of a specific length, the standard one suffices!

### Higher-order Functions
Perhaps instead of taking the `k` best grades, we would like
to pad each individual grade, and, furthermore, we want to
be able to experiment with different padding functions. Let's
rewrite `average` to take a functional argument, and
stipulate that it can only increase a `Score`.

```haskell
{-@ padAverage :: (s:Score -> {v:Score | s <= v}) -> [(Pos, Score)] -> Score @-}
padAverage f []  = f 0
padAverage f wxs = total `div` n
  where
    total   = sum [w * f x | (w, x) <- wxs ]
    n       = sum [w       | (w, _) <- wxs ]
```

Target automatically checks that `padAverage` is
a safe generalization of `average`. Randomized
testing tools can also generate functions, but those
functions are unlikely to satisfy non-trivial constraints,
thereby burdening the user with custom generators.

### Moving On
You can specify a lot of interesting properties with refinement
types and we've only scratched the surface here. Check out the
[LiquidHaskell blog](http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/categories/basic/)
for more examples; Target uses the same specification language as
LiquidHaskell so the examples should all be testable.
