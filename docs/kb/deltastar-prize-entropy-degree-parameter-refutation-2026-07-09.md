# Prize entropy pin: degree and actual-rate refutations

Date: 2026-07-09

## Historical definition

`PrizePinConjecture` in `PrizeEntropyDeltaStar.lean` is false as stated.  Its parameter
`k` is the polynomial degree bound used by `evalCode g n k`, so the code has dimension
`k + 1`.  The entropy expression instead receives `k / n` as its rate.

`PrizeEntropyPinRefuted.lean` gives a machine-checked counterexample at

```text
p = 12289, n = 8, g = 4043, k = 0, epsilon* = 14/12289.
```

The existing unconditional theorem `KKH26DimOne.deltaStar_pin_F12289` proves

```text
mcaDeltaStar (evalCode 4043 8 0) (14/12289) = 3/4.
```

But the historical conjecture supplies rate `0/8 = 0`, and

```text
prizeDeltaStar 0 B = 1
```

for every budget `B`, because binary entropy vanishes at zero.  Thus the claimed equality
would identify `3/4` with `1`.

## The actual-rate repair also fails

The same Lean module proves the stronger exact inequality

```text
3/4 < prizeDeltaStar (1/8) 14.
```

Here `1/8` is the actual dimension-one code rate and `14` is the simplified list budget
`12289 * (14/12289)`.  The certificate uses

```text
binEntropy(1/8) < 2/5,
7/2 < logb 2 14,
```

so `binEntropy(1/8) / logb 2 14 < 1/8`.  The logarithm bound follows from the exact integer
inequality `2^7 < 14^2`; no floating-point oracle enters the proof.

Consequently, merely replacing `k/n` by `(k+1)/n` does not produce a valid generic finite
exact-pin formula.

## The logarithm-base repair also fails

There is a second mismatch in the historical expression: Mathlib's `Real.binEntropy` uses
natural logarithms, while its denominator is `Real.logb 2 B`.  The Lean module now also tests
the obvious base-consistent candidate

```text
prizeDeltaStarBits rho B = 1 - rho - (binEntropy rho / log 2) / logb 2 B.
```

At the same dimension-one pin it proves the inequality in the opposite direction:

```text
prizeDeltaStarBits (1/8) 14 < 3/4.
```

The exact certificate reduces to

```text
log 14 < 8 * binEntropy(1/8),
14 < 2^24 / 7^7.
```

Thus correcting both the rate parameter and the entropy units still misses this finite
operational threshold.  This is a counterexample to that specific repair, not a claim that
every possible entropy-based asymptotic law is false.

## Scope

These results refute the historical Lean definition, its naive actual-rate repair, and the
obvious base-consistent actual-rate repair as generic finite exact-pin statements.  They do
not close or refute any of the four production prize instances, and they do not rule out a
suitably qualified asymptotic entropy law.  The production worst-case list upper bound remains
open.

## Related finite pins

`DeltaStarPinsF17N8.lean` adds two independent unconditional operational pins on the
eight-point smooth domain over `F_17`:

```text
degree <= 2, epsilon* in [2/17, 4/17): delta* = 1/4;
degree <= 1, epsilon* in [3/17, 8/17): delta* = 3/8.
```

They combine the five-thirds ratio-pigeonhole good side with explicit pencil bad sides.
They are finite exact pins, not proofs of the entropy formula.

## Validation

`scripts/pg-iterate.sh` typechecks the updated module.  Its `#print axioms` audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
