# DeltaStar #464: fixed-parameter limit transfer gate

Date: 2026-06-25

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FixedParameterLimitTransferGate.lean`
- Status: abstract finite gate; no arithmetic theorem claimed.

## Inputs checked

- Live issue #464 still asks for the finite prize diagonal: explicit smooth-domain RS at
  `p ≈ n^β`, not a two-stage limit with `p -> ∞` after fixing `n`.
- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md` lists effective vertical Sato-Tate / Katz monodromy
  as a possible language for the wall, but it explicitly requires a finite, effective, worst-case
  conclusion at the growing conductor.
- Existing frontier gates already cover related obstructions: vacuous thin-regime Katz discrepancy,
  tail-to-sup atom size, and growing-conductor Jacobi/Katz failure.  This gate isolates the separate
  noncommuting-limits issue.

## Result

This gate isolates the exact missing uniformity when a vertical Sato-Tate / Katz / Untrau input is
quoted in its fixed-parameter form.

Qualitative theorem shape:

```text
for every fixed n, exists P0(n), for every p >= P0(n), Good(n,p)
```

Prize-facing theorem shape:

```text
for every n, Good(n, scale(n))
```

The Lean contract is:

```text
EventualWithThreshold Good P0
ThresholdBelowScale P0 scale        -- forall n, P0(n) <= scale(n)
---------------------------------------------------------------
PrizeDiagonalGood Good scale
```

It is also sharp.  The file proves the universal transfer principle is equivalent to
`ThresholdBelowScale P0 scale`; testing on `Good n p := P0 n <= p` makes necessity immediate.

## Countermodel

For any diagonal scale `scale`, define:

```text
afterScaleGood n p := scale(n) < p
```

Then:

- for each fixed `n`, `afterScaleGood n p` is eventually true with threshold `scale(n)+1`;
- at the prize diagonal `p = scale(n)`, it is false;
- therefore pointwise eventual truth alone cannot imply the diagonal statement.

This is the noncommuting-limits obstruction in its smallest form: a `q -> infinity` theorem at fixed
subgroup order does not touch `q = scale(n)` unless the effective threshold is known to lie below
the prize scale.

## Routing For #464

This complements, rather than duplicates:

- `_AssaultV2_EffectiveSatoTate.lean`: the honest Katz/Weil-II discrepancy is vacuous in the thin
  prize regime (`f / sqrt(q) >= 1`);
- `_VerticalTailSupConsumer.lean`: a distributional tail bound consumes to a pointwise sup only below
  one-atom mass;
- `_JacobiKatzEquidist.lean`: growing-order Jacobi/Katz conductor growth overwhelms fixed-order
  equidistribution rates;
- `_wfHK2_katz_sarnak_extreme_value.lean`: symmetry/extreme-value heuristics return the open BGK
  target rather than proving it.

The present gate records the separate fixed-parameter/diagonal mismatch.  It says what would have to
be supplied by an effective vertical Sato-Tate theorem before it can enter the #464 prize cone:
explicit thresholds `P0(n)` with `P0(n) <= scale(n)` at the prize scale, plus the independent
tail-to-sup atom-scale contract.

## Consequence for #464

A theorem of the form "for each fixed subgroup order, the family becomes equidistributed as the
field grows" is not usable until it comes with a quantitative threshold below the prize field size.
For the prize diagonal this means an explicit `P0(n)` satisfying `P0(n) <= n^β` (or below the chosen
split prime-field representative near that scale).  Without that inequality, the fixed-parameter
theorem may become true only after the prize point has already passed.
