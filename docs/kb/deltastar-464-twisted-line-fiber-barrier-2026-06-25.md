# Issue #464: Twisted-Line Bounded-Fiber Barrier

Date: 2026-06-25

## Claim Tested

The twisted monomial-graph annihilator line has period

```text
ζ(t) = sum_{x in S} ψ(t * φ(x)).
```

`TwistedLineCollisionParseval` already proves the exact identity

```text
sum_t |ζ(t)|^2 = q * #{(x,y) in S x S : φ(x) = φ(y)}.
```

A plausible next attack was: in actual monomial-graph directions the phase map often has bounded
fibers, so perhaps the twisted line can beat the original BGK/Paley wall and force the missing floor.

## Formal Result

The new frontier brick

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_TwistedLineFiberEnergyBarrier.lean
```

proves the precise bounded-fiber consequence and its monomial-graph specialization.

If every restricted fiber through a point of `S` has size at most `L`,

```text
#{y in S : φ(y) = φ(x)} <= L   for every x in S,
```

then

```text
#{(x,y) in S x S : φ(x) = φ(y)} <= |S| * L
```

and therefore

```text
sum_t |ζ(t)|^2 <= q * |S| * L,
average_t |ζ(t)|^2 <= |S| * L.
```

This strictly improves the crude `q * |S|^2` energy bound when the folds are bounded.

The same file also proves the concrete geometric cap for monomial phases

```text
φ(x) = a*x + b*x^j.
```

When `j >= 2` and `b != 0`, every level set is contained in the roots of a nonzero polynomial of
degree at most `j`, hence every restricted fiber has size at most `j`.  Therefore Lean verifies

```text
sum_t |ζ(t)|^2 <= q * |S| * j,
average_t |ζ(t)|^2 <= |S| * j.
```

This confirms that bounded-fold monomial directions are genuinely better than the crude collision
ceiling, but only at the energy level.

## Why This Still Fails To Prove The Floor

The output is still an L2/counting theorem.  It says the average squared line period is at most
`|S| * L`.  It does not say every line period is at most `sqrt(|S| * L)`, nor does it control the
single worst frequency/offset that drives the delta-star floor.

Even with `L = O(1)`, the formal conclusion is compatible with one exceptional line parameter having
mass near the full energy budget.  Turning this into a floor proof would require an additional
anti-concentration or uniform cancellation theorem for the twisted periods.  That missing theorem is
exactly the original L2-to-L∞ obstruction, not a consequence of bounded fibers alone.

## What It Rules Out

This closes the tempting shortcut:

```text
bounded monomial-graph folds
  -> small collision energy
  -> uniform period bound
  -> delta-star floor
```

The first arrow is now Lean-verified.  The second arrow is false without new input.  Bounded fibers
improve the average, but they do not provide the domination theorem needed to consume
`WorstCaseIncidenceBounded` or bypass the BGK/Paley wall.

## Residual Target

A surviving route must add genuinely uniform information, for example:

```text
bounded fibers + non-degenerate phase geometry + cancellation mechanism
  -> sup_t |ζ(t)| <= C * sqrt(|S| log(q/|S|)).
```

The bounded-fiber lemma can be a bookkeeping input to such a theorem, but it is not the theorem.
