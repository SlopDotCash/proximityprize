/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawScaleDoorScaleBridge

/-!
# Door-IV Shaw-gap drift contrapositive (#444)

This file adds the explicit drift/no-go form of the Shaw scale bridge.  The already-proven identity

`M / √n = Sh(q,n,M) * √(log(q/n))`

says that the genuine prize-floor ratio is the Shaw value multiplied by the exact synthesis gap.  The
contrapositive pressure is: if the gap factors drift past every rescaled target and the Shaw values do
not vanish, then the genuine prize-floor ratios must drift too.  Thus a constant prize-floor bound with
a positive Shaw floor has already controlled the open door-(iv) `√log` gap.

This is pure algebra over `_ShawScaleDoorScaleBridge`; it proves no CORE cancellation, no completion,
no moment estimate, and no anti-concentration theorem.
-/

namespace ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive

open _root_.ProximityGap.Frontier.ShawValueCapstone
open ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy
open ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge

/-- **Unbounded gap plus a nonvanishing Shaw floor forces unbounded prize-floor ratios.**
If the exact synthesis gap factors `√(log(qᵢ/nᵢ))` drift past every rescaled target and every Shaw
value is bounded below by one fixed positive `c`, then the genuine prize-floor ratios `Mᵢ/√nᵢ` also
drift past every target.  This is the explicit contrapositive pressure behind
`gap_family_le_prizeFloorBound_div_shawFloor`: a constant prize-floor bound cannot coexist with a
positive Shaw floor unless the door-(iv) `√log` gap has already been controlled.

No cancellation or CORE estimate is proved here; the theorem is pure algebra over the exact identity
`M/√n = Sh·√log`, stated in the explicit drift form used by the campaign's negative capstones. -/
theorem prizeFloorRatio_unbounded_of_gap_unbounded_and_shawFloor {ι : Type*}
    {q n M : ι → ℝ} {c : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hc : 0 < c)
    (hfloor : ∀ i, c ≤ shawValue (q i) (n i) (M i))
    (hgapDrift : ∀ B : ℝ, ∃ i : ι, B / c < Real.sqrt (Real.log (q i / n i))) :
    ∀ B : ℝ, ∃ i : ι, B < M i / prizeScale (n i) := by
  intro B
  rcases hgapDrift B with ⟨i, hgap⟩
  refine ⟨i, ?_⟩
  have hB_eq : B = c * (B / c) := by
    field_simp [ne_of_gt hc]
  have hB_lt_cgap : B < c * Real.sqrt (Real.log (q i / n i)) := by
    rw [hB_eq]
    exact mul_lt_mul_of_pos_left hgap hc
  have hcg_le_shg : c * Real.sqrt (Real.log (q i / n i))
      ≤ shawValue (q i) (n i) (M i) * Real.sqrt (Real.log (q i / n i)) :=
    mul_le_mul_of_nonneg_right (hfloor i) (Real.sqrt_nonneg _)
  have hbridge := prizeFloorRatio_eq_shawValue_mul_gap (q i) (n i) (M i) (hn i) (hnq i)
  exact lt_of_lt_of_le hB_lt_cgap (by simpa [hbridge] using hcg_le_shg)

/-- **Bounded prize-floor ratios plus an unbounded gap force Shaw values to vanish along a
subsequence.**  This is the complementary drift/no-go form of the Shaw-scale bridge.  If the genuine
prize-floor ratios `Mᵢ/√nᵢ` stay below one nonnegative constant `B`, while the exact synthesis gaps
`√(log(qᵢ/nᵢ))` drift past every target, then the Shaw values become arbitrarily small: for every
positive `ε` there is an index with `Shᵢ < ε`.

Thus a bounded prize-floor family over an unbounded `√log` regime cannot also have a nonvanishing
Shaw-value floor.  This is pure normalization algebra over `Sh = (M/√n)/√log`; it proves no CORE
cancellation and makes no anti-concentration claim. -/
theorem shawValue_arbitrarily_small_of_gap_unbounded_and_prizeFloorBound {ι : Type*}
    {q n M : ι → ℝ} {B : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hB : 0 ≤ B)
    (hPrize : ∀ i, M i / prizeScale (n i) ≤ B)
    (hgapDrift : ∀ T : ℝ, ∃ i : ι, T < Real.sqrt (Real.log (q i / n i))) :
    ∀ ε : ℝ, 0 < ε → ∃ i : ι, shawValue (q i) (n i) (M i) < ε := by
  intro ε hε
  rcases hgapDrift (B / ε) with ⟨i, hgap⟩
  refine ⟨i, ?_⟩
  have hgap_nonneg_target : 0 ≤ B / ε := div_nonneg hB hε.le
  have hgap_pos : 0 < Real.sqrt (Real.log (q i / n i)) :=
    lt_of_le_of_lt hgap_nonneg_target hgap
  have hlog_nonneg : 0 ≤ Real.log (q i / n i) := by
    apply Real.log_nonneg
    have hdiv : n i / n i ≤ q i / n i :=
      div_le_div_of_nonneg_right (le_of_lt (hnq i)) (le_of_lt (hn i))
    simpa [div_self (ne_of_gt (hn i))] using hdiv
  have hL : 0 < Real.log (q i / n i) := by
    have hsqpos : 0 < (Real.sqrt (Real.log (q i / n i))) ^ 2 := sq_pos_of_pos hgap_pos
    simpa [Real.sq_sqrt hlog_nonneg] using hsqpos
  have hSh_le := shawValue_le_prizeFloorBound_div_gap (q i) (n i) (M i) B
    (hn i) (hnq i) hL (hPrize i)
  have hB_lt_eps_gap : B < ε * Real.sqrt (Real.log (q i / n i)) := by
    have hmul := mul_lt_mul_of_pos_left hgap hε
    have hleft : ε * (B / ε) = B := by
      field_simp [ne_of_gt hε]
    simpa [hleft] using hmul
  have hB_div_gap_lt : B / Real.sqrt (Real.log (q i / n i)) < ε := by
    exact (div_lt_iff₀ hgap_pos).2 hB_lt_eps_gap
  exact lt_of_le_of_lt hSh_le hB_div_gap_lt

/-- **No positive uniform Shaw floor over an unbounded synthesis-gap regime with bounded prize
ratios.**  This is the existential no-go consumer of
`shawValue_arbitrarily_small_of_gap_unbounded_and_prizeFloorBound`: if `Mᵢ/√nᵢ` is bounded while the
exact door-(iv) gap factors `√(log(qᵢ/nᵢ))` drift without bound, then no fixed `c>0` can sit below every
Shaw value.  Equivalently, a bounded prize-floor theorem in an unbounded `√log` regime must have
`Shᵢ → 0` along a subsequence unless it also controls the door-(iv) gap.  Pure normalization algebra;
no CORE cancellation, completion, or anti-concentration estimate is asserted. -/
theorem not_exists_positive_shawFloor_of_gap_unbounded_and_prizeFloorBound {ι : Type*}
    {q n M : ι → ℝ} {B : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hB : 0 ≤ B)
    (hPrize : ∀ i, M i / prizeScale (n i) ≤ B)
    (hgapDrift : ∀ T : ℝ, ∃ i : ι, T < Real.sqrt (Real.log (q i / n i))) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ i : ι, c ≤ shawValue (q i) (n i) (M i) := by
  rintro ⟨c, hc, hfloor⟩
  rcases shawValue_arbitrarily_small_of_gap_unbounded_and_prizeFloorBound
      hn hnq hB hPrize hgapDrift c hc with ⟨i, hi⟩
  exact (not_lt_of_ge (hfloor i)) hi

/-- **Positive Shaw floor plus unbounded synthesis gap forbids bounded prize ratios.**
This is the boundedness no-go consumer of
`prizeFloorRatio_unbounded_of_gap_unbounded_and_shawFloor`: if every Shaw value is bounded below by
one fixed `c>0` and the exact gap factors drift past every rescaled target, then the genuine ratios
`Mᵢ/√nᵢ` cannot be uniformly bounded.  Pure scale algebra; no CORE cancellation theorem. -/
theorem not_prizeFloorRatio_bddAbove_of_gap_unbounded_and_shawFloor {ι : Type*}
    {q n M : ι → ℝ} {c : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hc : 0 < c)
    (hfloor : ∀ i, c ≤ shawValue (q i) (n i) (M i))
    (hgapDrift : ∀ B : ℝ, ∃ i : ι, B / c < Real.sqrt (Real.log (q i / n i))) :
    ¬ ∃ B : ℝ, ∀ i : ι, M i / prizeScale (n i) ≤ B := by
  intro hBdd
  rcases hBdd with ⟨B, hB⟩
  rcases prizeFloorRatio_unbounded_of_gap_unbounded_and_shawFloor
      hn hnq hc hfloor hgapDrift B with ⟨i, hi⟩
  exact (not_lt_of_ge (hB i)) hi

end ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive

#print axioms ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive.prizeFloorRatio_unbounded_of_gap_unbounded_and_shawFloor
#print axioms ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive.shawValue_arbitrarily_small_of_gap_unbounded_and_prizeFloorBound
#print axioms ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive.not_exists_positive_shawFloor_of_gap_unbounded_and_prizeFloorBound
#print axioms ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive.not_prizeFloorRatio_bddAbove_of_gap_unbounded_and_shawFloor
