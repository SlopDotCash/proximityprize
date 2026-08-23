/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentHighDist
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# CS25 high-distance second moment for Reed-Solomon carriers (#82)

This module specializes the high-distance CS25 second-moment collapse to the finite carrier of a
Reed-Solomon code.  The Reed-Solomon MDS distance formula supplies the only nonzero-codeword
distance hypothesis needed by `ArkLib.CS25.sum_closeCount_sq_high_dist`, yielding the exact second
moment and the covered-set lower bound for radii below half the minimum distance.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] [DecidableEq F] in
/-- The finite Reed-Solomon carrier is closed under subtraction. -/
theorem rs_finCarrier_sub_mem (domain : ι ↪ F) (k : ℕ) :
    ∀ a ∈ ReedSolomon.finCarrier domain k, ∀ b ∈ ReedSolomon.finCarrier domain k,
      a - b ∈ ReedSolomon.finCarrier domain k := by
  intro a ha b hb
  have ha' : a ∈ ReedSolomon.code domain k := by
    simpa [ReedSolomon.finCarrier] using ha
  have hb' : b ∈ ReedSolomon.code domain k := by
    simpa [ReedSolomon.finCarrier] using hb
  simpa [ReedSolomon.finCarrier] using
    (Submodule.sub_mem (ReedSolomon.code domain k) ha' hb')

omit [DecidableEq ι] [DecidableEq F] in
/-- The finite Reed-Solomon carrier is closed under addition. -/
theorem rs_finCarrier_add_mem (domain : ι ↪ F) (k : ℕ) :
    ∀ a ∈ ReedSolomon.finCarrier domain k, ∀ b ∈ ReedSolomon.finCarrier domain k,
      a + b ∈ ReedSolomon.finCarrier domain k := by
  intro a ha b hb
  have ha' : a ∈ ReedSolomon.code domain k := by
    simpa [ReedSolomon.finCarrier] using ha
  have hb' : b ∈ ReedSolomon.code domain k := by
    simpa [ReedSolomon.finCarrier] using hb
  simpa [ReedSolomon.finCarrier] using
    (Submodule.add_mem (ReedSolomon.code domain k) ha' hb')

omit [DecidableEq ι] [DecidableEq F] in
/-- The zero word belongs to the finite Reed-Solomon carrier. -/
theorem rs_finCarrier_zero_mem (domain : ι ↪ F) (k : ℕ) :
    (0 : ι → F) ∈ ReedSolomon.finCarrier domain k := by
  simp [ReedSolomon.finCarrier]

omit [DecidableEq ι] in
/-- Reed-Solomon nonzero codewords are farther than `2r` whenever `2r < n - k + 1`. -/
theorem rs_finCarrier_high_dist (domain : ι ↪ F) (k r : ℕ) [NeZero k]
    (hk : k ≤ Fintype.card ι)
    (h2r : 2 * r < Fintype.card ι - k + 1) :
    ∀ v ∈ ReedSolomon.finCarrier domain k, v ≠ 0 →
      2 * r < hammingDist (0 : ι → F) v := by
  intro v hv hv0
  have hmin : Code.minDist ((ReedSolomon.code domain k) : Set (ι → F))
      ≤ hammingDist (0 : ι → F) v := by
    unfold Code.minDist
    apply Nat.sInf_le
    exact ⟨0, by simp, v, by simpa [ReedSolomon.finCarrier] using hv, hv0.symm, rfl⟩
  rw [ReedSolomon.minDist_eq' hk] at hmin
  exact lt_of_lt_of_le h2r hmin

/-- **Exact CS25 second moment for high-distance Reed-Solomon carriers.**  If
`2r < n - k + 1`, the centered ball-intersection sum collapses to the origin term:

`∑_w closeCount(RS_k, r, w)^2 = |RS_k| · |B(0,r)|`. -/
theorem rs_finCarrier_sum_closeCount_sq_high_dist
    (domain : ι ↪ F) (k r : ℕ) [NeZero k]
    (hk : k ≤ Fintype.card ι)
    (h2r : 2 * r < Fintype.card ι - k + 1) :
    (∑ w : ι → F, (closeCount (ReedSolomon.finCarrier domain k) r w) ^ 2)
      = (ReedSolomon.finCarrier domain k).card * ballInterCount r (0 : ι → F) := by
  exact sum_closeCount_sq_high_dist (ReedSolomon.finCarrier domain k) r
    (rs_finCarrier_sub_mem domain k)
    (rs_finCarrier_add_mem domain k)
    (rs_finCarrier_zero_mem domain k)
    (rs_finCarrier_high_dist domain k r hk h2r)

/-- **Covered-set lower bound for high-distance Reed-Solomon carriers.**  In the same
`2r < n - k + 1` regime, the number of received words within radius `r` of the RS carrier is at
least the first-moment count `|RS_k| · |B(0,r)|`. -/
theorem rs_finCarrier_card_close_ge_card_mul_vol
    (domain : ι ↪ F) (k r : ℕ) [NeZero k]
    (hk : k ≤ Fintype.card ι)
    (h2r : 2 * r < Fintype.card ι - k + 1)
    (hpos : 0 < (ReedSolomon.finCarrier domain k).card *
      (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    (ReedSolomon.finCarrier domain k).card *
      (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
        ≤ (Finset.univ.filter
          (fun w : ι → F => closeCount (ReedSolomon.finCarrier domain k) r w ≠ 0)).card := by
  exact card_close_ge_card_mul_vol (ReedSolomon.finCarrier domain k) r
    (rs_finCarrier_sub_mem domain k)
    (rs_finCarrier_add_mem domain k)
    (rs_finCarrier_zero_mem domain k)
    (rs_finCarrier_high_dist domain k r hk h2r)
    hpos

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_finCarrier_sub_mem
#print axioms ArkLib.CS25.rs_finCarrier_add_mem
#print axioms ArkLib.CS25.rs_finCarrier_zero_mem
#print axioms ArkLib.CS25.rs_finCarrier_high_dist
#print axioms ArkLib.CS25.rs_finCarrier_sum_closeCount_sq_high_dist
#print axioms ArkLib.CS25.rs_finCarrier_card_close_ge_card_mul_vol
