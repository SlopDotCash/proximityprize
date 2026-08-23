/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentReduction

/-!
# Sphere-packing (Hamming) bound

For a code `𝒞` whose minimum distance exceeds `2r` (every pair of distinct codewords is `> 2r`
apart), the radius-`r` Hamming balls around the codewords are pairwise disjoint (triangle
inequality), so they pack into the ambient space:

  `|𝒞| · |B(0,r)| ≤ qⁿ`.

This is the classical Hamming / sphere-packing bound, here phrased over `ι → F` using the
center-independence of ball volume (`ball_card_center_indep`).  It is the proximity-gap counterpart
of the second-moment ball machinery: disjointness for `dist > 2r` is the same triangle fact that
makes far codewords contribute nothing to the CS25 second moment.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Sphere-packing (Hamming) bound.**  If every pair of distinct codewords of `𝒞` is more than
`2r` apart, the radius-`r` balls are disjoint and pack into `ι → F`:
`|𝒞| · |B(0,r)| ≤ |ι → F| = qⁿ`. -/
theorem card_mul_ballVol_le (𝒞 : Finset (ι → F)) (r : ℕ)
    (hd : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → 2 * r < hammingDist c c') :
    𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ Fintype.card (ι → F) := by
  classical
  have hdisj : (𝒞 : Set (ι → F)).PairwiseDisjoint
      (fun c => Finset.univ.filter (fun w : ι → F => hammingDist w c ≤ r)) := by
    intro c hc c' hc' hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro x hxc hxc'
    rw [Finset.mem_filter] at hxc hxc'
    have hcc := hd c hc c' hc' hne
    have htri : hammingDist c c' ≤ hammingDist c x + hammingDist x c' := hammingDist_triangle c x c'
    rw [hammingDist_comm c x] at htri
    omega
  calc 𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      = ∑ c ∈ 𝒞, (Finset.univ.filter (fun w : ι → F => hammingDist w c ≤ r)).card := by
        rw [Finset.sum_congr rfl (fun c _ => ball_card_center_indep c r), Finset.sum_const,
          smul_eq_mul, mul_comm]
    _ = (𝒞.biUnion
          (fun c => Finset.univ.filter (fun w : ι → F => hammingDist w c ≤ r))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ Fintype.card (ι → F) := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ _)

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.card_mul_ballVol_le
