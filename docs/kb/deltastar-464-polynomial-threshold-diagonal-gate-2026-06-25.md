# Issue #464: polynomial threshold exponents for diagonal transfer

Date: 2026-06-25.

Status: finite transfer guardrail, not a prize proof.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PolynomialThresholdDiagonalGate.lean`

## Inputs checked

- Live issue #464 asks for a finite diagonal at the smooth-domain prize scale, not an eventual
  fixed-order theorem.
- `docs/kb/deltastar-464-fixed-parameter-limit-transfer-gate-2026-06-25.md` gives the general
  threshold-below-scale transfer contract.
- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md` repeatedly flags exponent bookkeeping at `p approx n^4`
  as decisive: exponent-5 Linnik is too large for the off-BGK least-prime lane, and hidden high
  polynomial thresholds in vertical/equidistribution results are likewise unusable at the diagonal.

## Result

`_FixedParameterLimitTransferGate.lean` isolates the general noncommuting-limits problem:

```text
for every fixed n, Good(n,p) holds for all p >= P0(n)
```

does not imply

```text
Good(n, scale(n))
```

unless `P0(n) <= scale(n)` is proved uniformly.

The new gate specializes that contract to polynomial thresholds. With the shifted base
`n+2`, define:

```text
P0(n)    = (n+2)^theta
scale(n) = (n+2)^beta
```

The Lean theorem is:

```lean
thresholdBelowScale_polynomial_iff :
  ThresholdBelowScale (polynomialScale theta) (polynomialScale beta) <-> theta <= beta
```

and the consumer form is:

```lean
prizeDiagonalGood_of_polynomial_eventual_le
```

So an effective vertical/equidistribution theorem with polynomial threshold exponent `theta`
reaches the prize diagonal of exponent `beta` only when `theta <= beta`.

The explicit failure theorem is:

```lean
exists_polynomial_eventual_not_diagonal_of_exponent_gt :
  beta < theta ->
    exists Good,
      EventualWithThreshold Good (polynomialScale theta) /\
      Not (PrizeDiagonalGood Good (polynomialScale beta))
```

The witness is the threshold property itself: `Good n p := (n+2)^theta <= p`.

## Why this matters

Many plausible imports from vertical Sato-Tate, Katz equidistribution, or effective
algebraic-geometry literature have the right qualitative form but hide a threshold:

```text
p >= P0(n)
```

If the best available `P0(n)` is, for example, `n^10`, then it is irrelevant to a prize diagonal
near `n^4`. The theorem may be true for each fixed `n` eventually, but the eventual range begins
after the field sizes the prize asks about.

This is not the same as the off-BGK least-prime exponent gate. There the question is whether a
prime exists below a target scale. Here the question is whether an already-quoted fixed-parameter
theorem has an effective onset below the target scale.

## Countermodel

The file also reuses the fixed-parameter countermodel:

```text
afterPolynomialScaleGood beta n p := (n+2)^beta < p
```

For each fixed `n`, this is eventually true in `p`; on the diagonal `p = (n+2)^beta`, it is false.
This proves that qualitative eventual truth alone cannot close the diagonal target.

## Consequence for #464

Any vertical theorem proposed for the #464 floor must expose its threshold exponent. The usable
checklist is:

1. identify the effective threshold `P0(n)`;
2. upper-bound it by a polynomial `(n+2)^theta`;
3. compare `theta` to the prize field exponent `beta`;
4. only if `theta <= beta` can the theorem even enter the prize diagonal.

If `theta > beta`, the theorem may still be mathematically strong in the fixed-`n` limit, but it
does not prove the smooth-domain RS floor at the prize scale.
