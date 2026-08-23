/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersection

/-!
# CS25 #82, deliverable 2 (b): the ball-intersection bound

The joint cover count in **Hamming-weight form**, and the triangle structure that forces its decay.

* `rHD_le_iff_hammingDist_le` — the floor bridge: `δᵣ(w,c) ≤ δ ↔ Δ₀(w,c) ≤ ⌊δ·n⌋`.
* `jointCoverCount_eq_hamming` — `I(c,c') = #{w : Δ₀(w,c) ≤ r ∧ Δ₀(w,c') ≤ r}` with `r = ⌊δ·n⌋`.
* `jointCoverCount_support_le` — the triangle constraint `Δ₀(c,c') ≤ Δ₀(w,c) + Δ₀(w,c')`, so any `w` in
  the intersection has `Δ₀(c,c') ≤ 2r`; the intersection is empty once codewords are far apart.
-/

open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Floor bridge.** `δᵣ(w,c) ≤ δ` (in `ℝ≥0∞`) iff the integer Hamming distance is `≤ ⌊δ·n⌋`. -/
theorem rHD_le_iff_hammingDist_le (w c : ι → F) (δ : ℝ≥0) :
    (relHammingDist w c : ENNReal) ≤ (δ : ENNReal)
      ↔ hammingDist w c ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Nat.le_floor_iff (by positivity)]
  rw [ENNReal.coe_NNRat_coe_NNReal, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, relHammingDist]
  push_cast
  rw [div_le_iff₀ hn]

/-- **Joint cover count in Hamming-weight form.** `I(c,c') = #{w : Δ₀(w,c) ≤ r ∧ Δ₀(w,c') ≤ r}`
with `r = ⌊δ·n⌋`. -/
theorem jointCoverCount_eq_hamming (δ : ℝ≥0) (c c' : ι → F) :
    jointCoverCount δ c c'
      = (univ.filter (fun w : ι → F =>
          hammingDist w c ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊
            ∧ hammingDist w c' ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊)).card := by
  unfold jointCoverCount
  congr 1
  ext w
  simp only [mem_filter, rHD_le_iff_hammingDist_le]

/-- **Disjointness cutoff.** If two centers are more than `2⌊δn⌋` apart, their `δ`-balls don't meet:
`I(c,c') = 0`.  (Triangle inequality; this restricts the weight-distribution sum to `d ≤ 2⌊δn⌋`.) -/
theorem jointCoverCount_eq_zero_of_lt (δ : ℝ≥0) (c c' : ι → F)
    (h : 2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ < hammingDist c c') :
    jointCoverCount δ c c' = 0 := by
  rw [jointCoverCount_eq_hamming, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro w - ⟨hwc, hwc'⟩
  have htri := hammingDist_triangle c w c'
  rw [hammingDist_comm c w] at htri
  omega

end ArkLib.CS25
