/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TwoAdicGradedTower

/-!
# Moment-annihilation corollaries of the depth-ℓ 2-adic graded tower (#444)

This file packages the forward-use form of `_TwoAdicGradedTower`: once the first `ℓ`
binomial moments vanish (or, more generally, their graded Taylor vector already lies in
`I^ℓ`), the signed cyclotomic wraparound sum lies in `I^ℓ`.

This is only the algebraic low-rung tower substrate. It does **not** prove the integer parity
criterion, any char-`p` transfer, BGK, CORE, or a capacity/growth-law claim. It is a reusable
consumer lemma for Sidon-depth / moment-vanishing formalizations: the open analytic content is
finding enough prize-regime cancellations to feed these hypotheses.
-/

namespace ProximityGap.Frontier.TwoAdicMomentAnnihilation

open Finset
open ProximityGap.Frontier.TwoAdicGradedTower

variable {ι R : Type*} [CommRing R]

/-- **Forward graded-vector consumer.** If the depth-`ℓ` graded Taylor vector already lies in
`I^ℓ`, then the signed wraparound sum lies in `I^ℓ`. This is the direction of the full tower
biconditional used by Sidon-depth or moment-vanishing callers. -/
theorem signedSum_mem_idealPow_of_gradedTower_mem (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ : ℕ)
    (s : Finset ι) (c : ι → R) (a : ι → ℕ)
    (hgraded : (∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j) ∈ I ^ ℓ) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i)) ∈ I ^ ℓ := by
  exact (signedSum_mem_idealPow_iff_gradedTower I t ht ℓ s c a).2 hgraded

/-- **Depth-`ℓ` moment annihilation.** If every binomial moment
`σ_j = Σ_i c_i * C(a_i,j)` vanishes for `j < ℓ`, then the signed wraparound sum
`Σ_i c_i(1+t)^{a_i}` is in `I^ℓ`. For `t = ζ − 1` and `I = (t)`, this is the clean
formal bridge from low-depth moment vanishing to `λ^ℓ` divisibility. -/
theorem signedSum_mem_idealPow_of_moments_zero (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ : ℕ)
    (s : Finset ι) (c : ι → R) (a : ι → ℕ)
    (hzero : ∀ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) = 0) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i)) ∈ I ^ ℓ := by
  apply signedSum_mem_idealPow_of_gradedTower_mem I t ht ℓ s c a
  have hgraded_zero :
      (∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j) = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [hzero j hj, zero_mul]
  rw [hgraded_zero]
  exact (I ^ ℓ).zero_mem

end ProximityGap.Frontier.TwoAdicMomentAnnihilation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.TwoAdicMomentAnnihilation.signedSum_mem_idealPow_of_gradedTower_mem
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.TwoAdicMomentAnnihilation.signedSum_mem_idealPow_of_moments_zero
