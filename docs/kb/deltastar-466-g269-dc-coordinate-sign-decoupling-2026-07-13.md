# δ* / #466 — G269: the DC coordinate does not control the adjacent-rank CORE covariance sign

**Date:** 2026-07-13
**Lane:** direct Opus 4.8 CORE (cron)
**Branch:** `research/proximity-prize` (never `main`, per #499)
**Status:** LANDED no-go. CORE remains OPEN / ON-BGK.

## Object

The current frontier CORE surrogate (the object G220, G228–G267 operate on):

```
W_G(x) = #{(y,z) ∈ G² : 2y − z = x},              G = order-n multiplicative subgroup of 𝔽_p^*  (n a 2-power)
R_r(x) = (dp_r ⋆ dp_{r-1})(x)                       adjacent-rank subset-sum correlation
A_r(n,p) = p · Σ_x W_G(x) R_r(x) − (Σ_x W_G(x))(Σ_x R_r(x))          (exact integer; the CORE covariance)
```

## Exact per-coordinate decomposition

With `SW := Σ_x W_G(x) = n²`, `SR := Σ_x R_r(x)`, define the exact integer per-coordinate centered
contribution

```
P(x) := (p·W_G(x) − SW)·(p·R_r(x) − SR).
```

A one-line expansion gives the identity

```
Σ_x P(x) = p²·Σ_x W_G(x)R_r(x) − p·SW·SR = p·A_r(n,p),
```

so `P(x)` is the exact centered contribution of coordinate `x` and `Σ_x P(x) = p·A_r`. Split it into
the **DC-diagonal** term `P(0)` (the `x = 0` self-collision coordinate) and the **off-DC** remainder
`Poff := Σ_{x≠0} P(x)`. Then `P(0) + Poff = p·A_r` exactly.

## The tempting one-sided handle this closes

A natural simplification of the binding analytic target — square-root cancellation on the off-DC arcs
— is that the covariance sign is a **removable DC artifact**: that `sign A_r = sign P(0)`, i.e. the
`x = 0` self-collision coordinate controls the sign, so after subtracting the diagonal the object is
sign-definite or trivial. **This is false, in both directions.**

## What is certified

Exact float-free witnesses (`n = 16`, `r = 5`; `W_G(0) = 0` at both, so the DC term is purely
`R_5`-driven):

```
(n,p) = (16, 97):    A₅ = −6 285 008,    P(0) = +101 818 368,   Poff = −711 464 144
(n,p) = (16, 433):   A₅ = +3 425 440,    P(0) = −215 519 232,   Poff = +1 698 734 752
```

- **`(16,97)`**: covariance negative, DC coordinate positive → `A₅ < 0 < P(0)`.
- **`(16,433)`**: covariance positive, DC coordinate negative → `P(0) < 0 < A₅`.

Either alone refutes `sign A_r = sign P(0)`; together they show the DC sign is uninformative in both
directions. On both witnesses the **off-DC** block matches the covariance sign while the DC block
opposes it, and the exact decomposition `P(0) + Poff = p·A₅` holds.

Third certified cell — a genuine three-way sign configuration (`n = 16`, `p = 257`):

```
A₅ = −1 051 408,   P(0) = −1 035 505 664,   Poff = +765 293 808,   P(0) + Poff = 257·A₅.
```

Here DC and covariance agree in sign (both negative) but the off-DC block is positive: the sign arises
from a cancellation between the DC and off-DC blocks, not from either alone.

## Census (statistical, record = probe)

Over 160 genuine cells sampled at both orders (`n = 8` at ranks `r ∈ {3,4}`, `n = 16` at ranks
`r ∈ {5,6}`; `80 + 80 = 160`):

- `sign(A_r) = sign(P(0)[DC])` in only **120/160** cells;
- `sign(A_r) = sign(Poff)` in **158/160** cells;
- the DC term dominates the magnitude (`|P(0)| > |Poff|`) in only **6/160** cells.

The covariance sign lives on the off-DC arcs; the DC coordinate is a frequently sign-opposed,
magnitude-negligible term.

## Formal payload

- `Frontier/_G269DCCoordinateSignDecoupling.lean` — axiom-clean integer certificate. `structure
  DCWitness` (prime + exact `A₅`, `P(0)`, `Poff`), and theorems `wCovNegDCPos_decomp`,
  `wCovPosDCNeg_decomp`, `wThreeWay_decomp` (exact decomposition identity `P(0) + Poff = p·A₅`),
  `wCovNegDCPos_A5_neg`, `wCovNegDCPos_P0_pos`, `wCovPosDCNeg_A5_pos`, `wCovPosDCNeg_P0_neg`,
  `wThreeWay_signs`, `no_dc_sign_lock` (both-direction decoupling), `offdc_carries_sign`. All `by
  decide`; every theorem depends on ZERO axioms (not even `propext`), no `sorryAx`, no `native_decide`.
- `scripts/probes/g269_dc_coordinate_sign_decoupling.py` — pure-int computation of record: recomputes
  the witnesses and the exact identity `P(0) + Poff = p·A_r` float-free, asserts the both-direction
  decoupling and the three-way cell, and reproduces the 45/80 vs 79/80 census split (SystemExit(1) on
  any failure), and reproduces the 120/160 vs 158/160 census split over both orders. PASS.

## Scope (honest)

As with G214/G216/G217/G220/G266, the **computation of record** is the reproducible float-free probe;
the Lean file certifies the arithmetic and the exact decomposition identity on the recorded cells plus
the sign-decoupling witnesses, not an in-Lean subset-sum re-derivation of `A_r`. The `120/160` vs
`158/160` split is a statistical statement, recorded in the probe, not dressed as a theorem.

This closes the "DC-artifact" simplification of the adjacent-rank sponsor covariance: the sign is not
controlled by the `x = 0` self-collision coordinate, so any bound must engage the off-DC arcs
directly. It is orthogonal to G266/G267 (the quadrant/thinness census of `A_r`'s value) and to the
antipodal-count floor route (G268): those study whether `A_r` is positive; G269 studies which
coordinates carry the sign, and localizes it away from the removable diagonal onto exactly the open
square-root-cancellation surface. It does **not** bound `A₅` at production primes. The surviving CORE
object is unchanged. CORE remains OPEN / ON-BGK.
