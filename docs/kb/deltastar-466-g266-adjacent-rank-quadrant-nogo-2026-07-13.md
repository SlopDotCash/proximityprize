# δ* / #466 — G266: adjacent-rank CORE covariance realises all four quadrants (no cross-rank sign lock, no adjacent-rank forced sign; thinness-positivity bias OPEN)

**Date:** 2026-07-13
**Lane:** direct Opus 4.8 CORE (cron)
**Branch:** `research/proximity-prize` (never `main`, per #499)
**Status:** LANDED no-go. CORE remains OPEN / ON-BGK.

## Object

The current frontier CORE surrogate (the object G228–G265 operate on):

```
W_G(x) = #{(y,z) ∈ G² : 2y − z = x},              G = order-n multiplicative subgroup of 𝔽_p^*  (n a 2-power)
R_r(x) = (dp_r ⋆ dp_{r-1})(x)
       = #{(A,B) : A ⊆ G, |A|=r, B ⊆ G, |B|=r-1, (Σ A) − (Σ B) = x}
A_r(n,p) = p · Σ_x W_G(x) R_r(x) − (Σ_x W_G(x))(Σ_x R_r(x))          (exact integer; the CORE covariance)
```

This is the **adjacent-rank correlation** row, distinct from G220's **single-subset-sum** row
`R_r(x) = #{A ⊆ G : |A|=r, Σ A = x}`. G220 closed the physical-space route for the single-subset-sum
object (sign unforced, dominant diagonal flips). Three repairs survived G220 specifically for the
adjacent-rank object and its thinness dependence.

## What was closed

Exact float-free census over genuine cells `n ∈ {8,16,32}`, `p` prime with `n | (p−1)`:

- **CLOSED — No cross-rank sign lock.** The quadrant `(sign A₅, sign A₆) = (−,+)` occurs at the
  genuine cell `(n,p) = (8, 89)`: `A₅ = −256 < 0`, `A₆ = +40 > 0`. So `A₆ > 0 ⟹ A₅ > 0` is FALSE; a
  rank-6 bound does not transport to rank 5 by sign.
- **CLOSED — No adjacent-rank forced sign at either rank.** `A₅` and `A₆` are each negative on
  `(8,113)` (`−−`) and positive on `(8,2969)` (`++`).
- **NOT CLOSED — thinness-positivity bias is OPEN (honest correction).** An earlier draft claimed a
  `no_thinness_forced_sign` theorem; that was WRONG. The thinness repair predicts eventual fixed `(+)`
  sign for *sufficiently thin* cells, and the data CORROBORATE it: for `n=8` every genuine negative
  cell has `τ = (p−1)/n² ≤ 1.8`, while all scanned cells with `τ > 1.8` up to `τ = 56.5` are `(+,+)`.
  The `(+,+)` bias with thinness is real and is left OPEN as a candidate one-sided handle.

Census (n∈{8,16,32}, p<2000, ≤25 cells each = 67 cells): `{++:38, +−:4, −+:1, −−:24}` — all four
quadrants realised, including the unique `−+` at `(8,89)`.

## Why non-overlapping with G220

G220's certificate used the single-subset-sum row and mentioned all four quadrants occur for THAT
object. It did **not** certify the adjacent-rank correlation object (the actual G228–G265 frontier
surrogate), nor rule out a cross-rank sign lock specific to it. G266 supplies the exact `(−,+)`
adjacent-rank witness `(8,89)` and a `(−,−)` witness `(8,113)`, closing the cross-rank and
adjacent-rank-forced-sign repairs while leaving the thinness-positivity bias OPEN.

## Formal payload

- `Frontier/_G266AdjacentRankQuadrantNoGo.lean` — axiom-clean integer certificate.
  Witnesses `wMinusPlus = (8,89): A₅=−256, A₆=+40`, `wMinusMinus = (8,113): A₅=−13128, A₆=−7240`,
  `wThinPlusPlus = (8,2969): A₅=+4357008, A₆=+1894816`. Theorems: `wMinusPlus_A5_neg`,
  `wMinusPlus_A6_pos`, `wMinusMinus_A5_neg`, `wMinusMinus_A6_neg`, `wThinPlusPlus_A5_pos`,
  `wThinPlusPlus_A6_pos`, `no_cross_rank_sign_lock`, `adjacent_rank_sign_not_forced`. All `by decide`;
  every theorem depends on ZERO axioms, no `sorryAx`, no `native_decide`. There is deliberately NO
  thinness theorem (the bias is open, not refuted).
- `scripts/probes/g266_adjacent_rank_quadrant_nogo.py` — pure-int computation of record: recomputes
  both witnesses float-free and runs the four-quadrant census. PASS.

## Scope (honest)

Computation of record is the float-free probe (G214/G216/G217/G220 convention); the Lean file
certifies the recorded constants' arithmetic and signs, not an in-Lean subset-sum re-derivation. The
census fractions and the thinness bias are statistical statements of record, not Lean theorems. This
does not bound `A₅` or `A₆` at production primes. The surviving object is the direct row-labelled
sponsor covariance, uniform in the fixed quotient character, stable under the rank-specific weights.
The open thinness-positivity bias is the one forward-pointing residue of this lane. CORE remains OPEN
/ ON-BGK.
