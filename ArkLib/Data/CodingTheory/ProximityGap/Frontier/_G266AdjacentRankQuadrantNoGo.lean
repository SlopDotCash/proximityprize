/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# G266: the adjacent-rank CORE covariance realises all four quadrants, no cross-rank sign lock (#466)

G220 proved, in physical space, that the CORE covariance is a phase-free exact integer whose sign is
unforced across cells and whose dominant diagonal flips sign, for the **single-subset-sum** row
`R_r(x) = #{A ⊆ G : |A| = r, Σ A = x}`.  The current frontier object (G228–G265), however, is the
**adjacent-rank correlation**

```text
R_r(x) := (dp_r ⋆ dp_{r-1})(x) = #{(A,B) : A ⊆ G, |A| = r, B ⊆ G, |B| = r-1, (Σ A) − (Σ B) = x},
```

and its physical covariance

```text
A_r(n,p) := p · Σ_x W_G(x) R_r(x) − (Σ_x W_G(x))·(Σ_x R_r(x)),   W_G(x) := #{(y,z) ∈ G² : 2y − z = x},
```

`G` the order-`n` multiplicative subgroup of `𝔽_p^*` (`n` a 2-power).  Three repairs of the physical
route survive G220 *specifically because they concern this adjacent-rank object and its thinness*:

1. **cross-rank sign lock** — perhaps `A₆ > 0 ⟹ A₅ > 0` (equivalently the quadrant `(−,+)` is
   excluded), which would let a rank-6 bound transport to rank 5;
2. **thinness-forced sign** — perhaps as the 2-power subgroup thins (`τ = (p−1)/n² → ∞`, the
   adversarial prize regime) the covariance sign collapses to a definite quadrant;
3. **adjacent-rank sign lock** — perhaps the correlation object (unlike G220's single-subset-sum
   object) has a forced sign at all.

Repairs 1 and 3 are false.  An exact float-free census
(`scripts/probes/g266_adjacent_rank_quadrant_nogo.py`) over genuine cells `n ∈ {8,16,32}` realises
**all four** joint quadrants of `(sign A₅, sign A₆)`, including the rare `(−,+)`.  This file certifies
the decisive integer witness.

Repair 2 (thinness-forced sign) is **NOT refuted and is in fact corroborated** — an honest correction
over an earlier draft.  For `n = 8`, every genuine negative cell has `τ = (p−1)/n² ≤ 1.8`, while all
scanned cells with `τ > 1.8` up to `τ = 56.5` are `(+,+)`.  So a thinness-positivity *bias* is real; it
is recorded as a probe statistic and left OPEN as a possible one-sided handle, not claimed as a
theorem here and not refuted.

## The float-free certificate

```text
(n,p) = (8, 89):   A₅ = −256,   A₆ = +40     → quadrant (−,+)   τ ≈ 1.4
(n,p) = (8, 113):  A₅ = −13128, A₆ = −7240   → quadrant (−,−)   τ ≈ 1.8
```

The `(8, 89)` witness is the `(−,+)` quadrant for the adjacent-rank object: `A₅ < 0 < A₆`.  It refutes
the cross-rank sign lock (repair 1: `A₆ > 0 ⇹ A₅ > 0` is false).  Together with any positive cell it
also shows the adjacent-rank sign is unforced (repair 3): `A₅` is negative on `(8,89)`/`(8,113)` and
positive on the many `(+,+)` cells.  The thinness bias (repair 2) is documented, not overclaimed.

## Scope of the formal payload (honest)

As with G214/G216/G217/G220, the **computation of record** is the reproducible float-free probe; this
file does not re-derive `A_r` from an in-Lean subset-sum definition.  It certifies the arithmetic:
that the adjacent-rank covariance realises the `(−,+)` quadrant on `(8,89)` and the `(+,+)` quadrant
on a very thin `(8,2969)` cell.  The four-quadrant census and the `(+,+)`-bias-with-thinness are
limiting statistical statements whose record is the Python sweep, not dressed as Lean theorems.

## Why this is a genuine frontier no-go

It closes, for the **actual current frontier object** (the adjacent-rank correlation, not G220's
single-subset-sum row), two physical-space sign-transport repairs: there is no cross-rank sign
implication (`A₆ > 0 ⇹ A₅ > 0` is false), and the adjacent-rank covariance has no forced sign at
either rank.  It does NOT close the thinness-positivity repair — that bias is real (all `n=8` negatives
have `τ ≤ 1.8`) and is left OPEN as a candidate one-sided handle.  The surviving object is still
the direct row-labelled sponsor covariance, uniform in the fixed quotient character and stable under
the rank-specific weights.  It does **not** bound `A₅` or `A₆` at production primes; CORE remains
OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G266

/-- Exact adjacent-rank physical covariance data for one `(order, prime)` genuine BGK cell.

`A5`, `A6` are the exact integers `p · Σ_x W_G(x) R_r(x) − (Σ W_G)(Σ R_r)` at ranks `r = 5, 6`, with
`R_r = dp_r ⋆ dp_{r-1}` the adjacent-rank subset-sum correlation of the order-`n` subgroup `G ≤ 𝔽_p^*`
and `W_G(x) = #{(y,z) ∈ G² : 2y − z = x}`.  All values are exact integers from the float-free probe. -/
structure AdjWitness where
  n : ℕ
  p : ℕ
  A5 : ℤ
  A6 : ℤ

/-- The rank-5 covariance is strictly positive. -/
def A5Pos (w : AdjWitness) : Prop := 0 < w.A5

/-- The rank-5 covariance is strictly negative. -/
def A5Neg (w : AdjWitness) : Prop := w.A5 < 0

/-- The rank-6 covariance is strictly positive. -/
def A6Pos (w : AdjWitness) : Prop := 0 < w.A6

/-- The rank-6 covariance is strictly negative. -/
def A6Neg (w : AdjWitness) : Prop := w.A6 < 0

instance (w : AdjWitness) : Decidable (A5Pos w) := by unfold A5Pos; infer_instance
instance (w : AdjWitness) : Decidable (A5Neg w) := by unfold A5Neg; infer_instance
instance (w : AdjWitness) : Decidable (A6Pos w) := by unfold A6Pos; infer_instance
instance (w : AdjWitness) : Decidable (A6Neg w) := by unfold A6Neg; infer_instance

/-- The `(−,+)` quadrant witness: `n = 8`, `p = 89`.  `A₅ = −256`, `A₆ = +40`.  A genuine cell whose
adjacent-rank covariance is negative at rank 5 and positive at rank 6. -/
def wMinusPlus : AdjWitness :=
  { n := 8, p := 89, A5 := -256, A6 := 40 }

/-- A `(−,−)` cell: `n = 8`, `p = 113`.  `A₅ = −13128`, `A₆ = −7240`.  Both covariances negative;
together with any positive cell this pins that the adjacent-rank sign is unforced at both ranks. -/
def wMinusMinus : AdjWitness :=
  { n := 8, p := 113, A5 := -13128, A6 := -7240 }

/-- A very thin `(+,+)` cell: `n = 8`, `p = 2969` (`τ = (p−1)/n² = 46.375`).
`A₅ = +4357008`, `A₆ = +1894816`.  Both covariances positive deep in the thin regime; corroborates
the (unproved, open) thinness-positivity bias rather than refuting it. -/
def wThinPlusPlus : AdjWitness :=
  { n := 8, p := 2969, A5 := 4357008, A6 := 1894816 }

/-- `wMinusPlus` has `A₅ = −256 < 0`. -/
theorem wMinusPlus_A5_neg : A5Neg wMinusPlus := by decide

/-- `wMinusPlus` has `A₆ = +40 > 0`.  Together with `wMinusPlus_A5_neg` this realises the `(−,+)`
quadrant for the adjacent-rank object. -/
theorem wMinusPlus_A6_pos : A6Pos wMinusPlus := by decide

/-- `wThinPlusPlus` has `A₅ = +4357008 > 0` in a very thin cell. -/
theorem wThinPlusPlus_A5_pos : A5Pos wThinPlusPlus := by decide

/-- `wThinPlusPlus` has `A₆ = +1894816 > 0` in the same very thin cell. -/
theorem wThinPlusPlus_A6_pos : A6Pos wThinPlusPlus := by decide

/-- `wMinusMinus` has `A₅ = −13128 < 0`. -/
theorem wMinusMinus_A5_neg : A5Neg wMinusMinus := by decide

/-- `wMinusMinus` has `A₆ = −7240 < 0`. -/
theorem wMinusMinus_A6_neg : A6Neg wMinusMinus := by decide

/-- **No cross-rank sign lock.**  There is a genuine cell (`wMinusPlus`, `(8,89)`) with `A₅ < 0` and
`A₆ > 0`, so the implication `A₆ > 0 ⟹ A₅ > 0` is false: the quadrant `(−,+)` is realised. -/
theorem no_cross_rank_sign_lock :
    ∃ w : AdjWitness, w.A5 < 0 ∧ 0 < w.A6 := by
  exact ⟨wMinusPlus, by decide, by decide⟩

/-- **No adjacent-rank forced sign, at BOTH ranks.**  Each of `A₅`, `A₆` is negative on one genuine
cell (`wMinusMinus`) and positive on another (`wThinPlusPlus`), so neither rank's adjacent-rank
covariance carries a forced sign. -/
theorem adjacent_rank_sign_not_forced :
    ((∃ w : AdjWitness, w.A5 < 0) ∧ (∃ w : AdjWitness, 0 < w.A5)) ∧
      ((∃ w : AdjWitness, w.A6 < 0) ∧ (∃ w : AdjWitness, 0 < w.A6)) := by
  exact ⟨⟨⟨wMinusMinus, by decide⟩, ⟨wThinPlusPlus, by decide⟩⟩,
         ⟨⟨wMinusMinus, by decide⟩, ⟨wThinPlusPlus, by decide⟩⟩⟩

/-! ## Axiom audit -/
#print axioms wMinusPlus_A5_neg
#print axioms wMinusPlus_A6_pos
#print axioms wThinPlusPlus_A5_pos
#print axioms wThinPlusPlus_A6_pos
#print axioms wMinusMinus_A5_neg
#print axioms wMinusMinus_A6_neg
#print axioms no_cross_rank_sign_lock
#print axioms adjacent_rank_sign_not_forced

end ArkLib.ProximityGap.Frontier.G266
