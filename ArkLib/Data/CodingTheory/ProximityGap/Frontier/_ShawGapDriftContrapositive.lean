/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

end ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive

#print axioms ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive.prizeFloorRatio_unbounded_of_gap_unbounded_and_shawFloor
