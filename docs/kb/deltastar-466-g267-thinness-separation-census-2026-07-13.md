# δ* / #466 — G267: exact thinness-separation certificate for the adjacent-rank CORE covariance (finite; thinness repair still OPEN)

**Date:** 2026-07-13
**Lane:** direct Opus 4.8 formalizer (cron)
**Branch:** `research/proximity-prize` (never `main`, per #499)
**Status:** LANDED calibrated consumer of G266. CORE remains OPEN / ON-BGK.

## Object

The current frontier CORE surrogate (the object G228–G266 operate on):

```
W_G(x) = #{(y,z) ∈ G² : 2y − z = x},              G = order-n multiplicative subgroup of 𝔽_p^*  (n a 2-power)
R_r(x) = (dp_r ⋆ dp_{r-1})(x)                       adjacent-rank subset-sum correlation
A_r(n,p) = p · Σ_x W_G(x) R_r(x) − (Σ_x W_G(x))(Σ_x R_r(x))          (exact integer; the CORE covariance)
```

## Motivation: the one thing G266 left OPEN

G266 realised all four sign quadrants of `(sgn A₅, sgn A₆)` and closed the cross-rank sign lock and
the adjacent-rank forced-sign repairs. It left exactly ONE repair OPEN and CORROBORATED, not refuted:
the **thinness-positivity bias** — as the 2-power subgroup thins (`τ = (p−1)/n² → ∞`, the adversarial
prize regime) the joint covariance sign appears to collapse to `(+,+)`. G266 deliberately declined to
formalize this as a theorem, because an unconditional sign law at production primes IS the open
BGK-hard target. G267 formalizes the exact FINITE content of that observation instead.

## What is certified (finite separation certificate)

Over the 90 genuine `n = 8` cells `17 ≤ p ≤ 2657`, `p ≡ 1 (mod 8)`, with exact float-free covariance
signs, the sign-negative set is EXACTLY the four primes

```
p = 17  (p−1 = 16,   τ = 0.25 )   (−,−)
p = 73  (p−1 = 72,   τ = 1.125)   (−,−)
p = 89  (p−1 = 88,   τ = 1.375)   (−,+)
p = 113 (p−1 = 112,  τ = 1.75 )   (−,−)
```

- **`neg_cells_below_threshold`** — every sign-negative census cell has `p − 1 ≤ 112` (`τ ≤ 1.75`).
  Sign flips are confined below the explicit integer thinness threshold.
- **`thin_tail_plusPlus`** — every census cell with `p − 1 ≥ 136` (`τ ≥ 2.125`) is `(+,+)`.
- **`neg_cells_are_exactly` / `neg_cells_count`** — the sign-negative set is exactly `{17,73,89,113}`,
  four cells.
- **`thin_tail_reaches_2656`** — the verified `(+,+)` tail reaches `p − 1 = 2656` (`τ = 41.5`).
- **`thinness_separation_census`** — packaged: confinement + thin-tail positivity + verified reach,
  a strict separation gap `(112, 136)` with the thin tail extending 23.7× beyond the last sign flip.

## Scope (honest, matching G266)

This is a **finite separation certificate**, NOT a proof of the thinness repair and NOT a bound at
production primes. It does not claim the `(+,+)` collapse is unconditional; proving that at production
thinness is exactly the open row-labelled sponsor covariance target. What G267 adds over G266 is the
precise, kernel-checked, monotone, thinness-ordered invariant: on the enumerated `n = 8` family
sign-negativity is confined to `p − 1 ≤ 112` with a wide verified positive tail. This is a calibrated
consumer of G266's data, not a restatement of any open Prop and not a fixed-depth island (it jointly
constrains both ranks r = 5, 6 through the single thinness ordering). The surviving CORE object is
unchanged. CORE remains OPEN / ON-BGK.

## Formal payload

- `Frontier/_G267ThinnessSeparationCensus.lean` — axiom-clean integer certificate. `structure Cell`
  (prime + recorded covariance signs), the 90-cell `census`, and theorems `census_length`,
  `neg_cells_below_threshold`, `thin_tail_plusPlus`, `neg_cells_are_exactly`, `neg_cells_count`,
  `thin_tail_reaches_2656`, `thinness_separation_census`. All `by decide`; every theorem depends on
  ZERO axioms (not even `propext`), no `sorryAx`, no `native_decide`.
- `scripts/probes/g267_thinness_separation_census.py` — pure-int computation of record: recomputes
  the full 90-cell census float-free, confirms it matches the Lean table exactly, and asserts every
  certified separation fact (SystemExit(1) on any failure). PASS.
