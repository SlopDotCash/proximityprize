# Issue #464: Burgess Shift-Holder Exponent Gate

Date: 2026-06-25

Status: abstract exponent bookkeeping; not a prize proof.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_BurgessShiftHolderExponentGate.lean`

## Point

The classical Burgess shift-Holder shape for a length-`H` character sum is modeled as

```text
H^(1 - 1/r) * p^((r + 1) / (4r^2)).
```

After substituting `p = H^beta`, the pure `H`-exponent is

```text
1 - 1/r + beta * (r + 1) / (4r^2).
```

This gate records the arithmetic wall, independently of any analytic theorem:

```lean
burgessHExponent_lt_one_iff :
  burgessHExponent beta r < 1 <-> beta < 4 * r / (r + 1)
```

The nontriviality threshold `4r/(r+1)` is always strictly below `4`.

## Result

At the #464 beta-four wall:

```lean
burgessHExponent_beta_four_eq :
  burgessHExponent 4 r = 1 + 1 / r^2
```

So every finite Burgess parameter is strictly worse than the trivial `H` exponent:

```lean
one_lt_burgessHExponent_beta_four :
  1 < burgessHExponent 4 r
```

and therefore cannot supply even an `H^{<1}` bound, much less the prize-scale
`H^(1/2)` bound.

## Consequence For #464

Finite Burgess shift-Holder amplification remains a wall certificate rather than an escape hatch at
`p = H^4`.  Any proof route that relies only on this exponent shape must introduce a genuinely new
ingredient that survives at or beyond the beta-four threshold.
