/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMultiPieceDeficitQuantitative

/-!
# Door (iv): the coherence deficit is SANDWICHED by total pairwise misalignment

`_DoorIVCoherenceDeficitQuantitative` / `_DoorIVMultiPieceDeficitQuantitative` give LOWER bounds on the
multi-piece coherence deficit `1 − ρ_multi` from a SINGLE non-collinear pair.  This file proves the
matching TWO-SIDED law, characterizing `1 − ρ_multi` (up to a factor `2`) by the TOTAL pairwise
misalignment of the whole family.

Define the **total pairwise misalignment**
`S(A) = Σ_{j<k} (‖A j‖·‖A k‖ − ⟪A j, A k⟫_ℝ)` and the total piece mass `M = Σ ‖A i‖`.  The engine is the
exact double-sum identity (Cauchy–Schwarz off-diagonal accounting): `2·S(A) = M² − ‖Σ A‖²`, i.e. the
"norm-square defect" `M² − ‖Σ A‖²` is exactly twice the total pairwise misalignment.  Since
`M² − ‖Σ A‖² = (M − ‖Σ A‖)(M + ‖Σ A‖)` and `M ≤ M + ‖Σ A‖ ≤ 2M`, dividing by `M·(M+‖Σ A‖)` gives:

> `S(A)/M²  ≤  1 − ρ_multi  ≤  2·S(A)/M²`   (both constants `1`, `2` are tight).

Consequence for door (iv): the multi-piece coherence deficit is EQUIVALENT, up to a factor `2`, to the
total pairwise angular misalignment of the pieces.  In particular the matching UPPER bound
`1 − ρ_multi ≤ 2·S/M²` is the new content: **small total pairwise misalignment FORCES `ρ_multi`
near `1`.**  A multi-piece refinement of the worst-frequency monomial sum therefore cannot manufacture
a coherence saving out of many nearly-collinear pieces — the saving is controlled, two-sidedly, by the
genuine total angular spread.  This is the citable two-sided capstone of the door-(iv) coherence
obstruction; it does NOT prove CORE.  No Gauss-period cancellation / moment / completion /
anti-concentration is claimed or used.  CORE `M(μ_n)` stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich

open scoped BigOperators InnerProductSpace
open ProximityGap.Frontier.DoorIVMultiPieceDeficitQuantitative

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Total pairwise misalignment of a finite family (`Σ_{j<k} (‖A j‖‖A k‖ − ⟪A j,A k⟫_ℝ)`), written as
half the full off-diagonal double sum for clean double-counting. -/
noncomputable def totalPairwiseMisalign {ι : Type*} (s : Finset ι) (A : ι → F) : ℝ :=
  (∑ j ∈ s, ∑ k ∈ s, (‖A j‖ * ‖A k‖ - ⟪A j, A k⟫_ℝ)) / 2

/-- **Double-sum mass identity.** `(Σ ‖A i‖)² = Σ_j Σ_k ‖A j‖·‖A k‖`. -/
theorem sq_sum_norm_eq_double {ι : Type*} (s : Finset ι) (A : ι → F) :
    (∑ i ∈ s, ‖A i‖) ^ 2 = ∑ j ∈ s, ∑ k ∈ s, ‖A j‖ * ‖A k‖ := by
  rw [sq, Finset.sum_mul_sum]

/-- **Double-sum norm-square identity.** `‖Σ A i‖² = Σ_j Σ_k ⟪A j, A k⟫_ℝ` in a real inner product
space. -/
theorem norm_sum_sq_eq_double {ι : Type*} (s : Finset ι) (A : ι → F) :
    ‖∑ i ∈ s, A i‖ ^ 2 = ∑ j ∈ s, ∑ k ∈ s, ⟪A j, A k⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [inner_sum]

/-- **The key identity:** twice the total pairwise misalignment equals the norm-square defect.
`2·S(A) = (Σ ‖A i‖)² − ‖Σ A i‖²`. -/
theorem two_mul_totalPairwiseMisalign {ι : Type*} (s : Finset ι) (A : ι → F) :
    2 * totalPairwiseMisalign s A = (∑ i ∈ s, ‖A i‖) ^ 2 - ‖∑ i ∈ s, A i‖ ^ 2 := by
  unfold totalPairwiseMisalign
  rw [sq_sum_norm_eq_double, norm_sum_sq_eq_double]
  rw [← Finset.sum_sub_distrib]
  have : ∀ j ∈ s, (∑ k ∈ s, ‖A j‖ * ‖A k‖) - (∑ k ∈ s, ⟪A j, A k⟫_ℝ)
      = ∑ k ∈ s, (‖A j‖ * ‖A k‖ - ⟪A j, A k⟫_ℝ) := by
    intro j _; rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl this]
  ring

/-- `S(A) ≥ 0` (each pairwise term is ≥ 0 by Cauchy–Schwarz; equivalently `‖Σ A‖ ≤ Σ ‖A i‖`). -/
theorem totalPairwiseMisalign_nonneg {ι : Type*} (s : Finset ι) (A : ι → F) :
    0 ≤ totalPairwiseMisalign s A := by
  have h2 := two_mul_totalPairwiseMisalign s A
  have htri : ‖∑ i ∈ s, A i‖ ≤ ∑ i ∈ s, ‖A i‖ := norm_sum_le _ _
  have hmnn : 0 ≤ ∑ i ∈ s, ‖A i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hsq : ‖∑ i ∈ s, A i‖ ^ 2 ≤ (∑ i ∈ s, ‖A i‖) ^ 2 := by
    apply sq_le_sq' <;> [linarith [norm_nonneg (∑ i ∈ s, A i)]; exact htri]
  linarith [h2]

/-- **LOWER bound:** `S(A)/M² ≤ 1 − ρ_multi`. -/
theorem totalMisalign_div_sq_le_one_sub_coherence {ι : Type*} (s : Finset ι) (A : ι → F)
    (hden : 0 < ∑ i ∈ s, ‖A i‖) :
    totalPairwiseMisalign s A / (∑ i ∈ s, ‖A i‖) ^ 2 ≤ 1 - multiPieceNormCoherence s A := by
  set M := ∑ i ∈ s, ‖A i‖ with hM
  set s0 := ‖∑ i ∈ s, A i‖ with hs0
  have htri : s0 ≤ M := by rw [hs0, hM]; exact norm_sum_le _ _
  have hs0nn : 0 ≤ s0 := by rw [hs0]; exact norm_nonneg _
  have h2 : 2 * totalPairwiseMisalign s A = M ^ 2 - s0 ^ 2 := two_mul_totalPairwiseMisalign s A
  have hdefect : 1 - multiPieceNormCoherence s A = (M - s0) / M := by
    unfold multiPieceNormCoherence
    rw [sub_div, div_self (ne_of_gt hden)]
  rw [hdefect]
  -- S/M² = (M²−s0²)/(2M²) = (M−s0)(M+s0)/(2M²) ≤ (M−s0)/M  since (M+s0)/(2M) ≤ 1
  have hS : totalPairwiseMisalign s A = (M ^ 2 - s0 ^ 2) / 2 := by linarith [h2]
  rw [hS]
  have hMpos : (0:ℝ) < M ^ 2 := by positivity
  rw [div_le_div_iff₀ hMpos hden]
  -- (M²−s0²)/2 · M ≤ (M−s0) · M²  ⟺  0 ≤ (M/2)·(M−s0)²
  have hMs0 : 0 ≤ M - s0 := by linarith
  nlinarith [mul_nonneg (le_of_lt hden) (sq_nonneg (M - s0)), hMs0, hs0nn, htri]

/-- **UPPER bound (the new content):** `1 − ρ_multi ≤ 2·S(A)/M²`.  Small total pairwise misalignment
forces `ρ_multi` near `1`. -/
theorem one_sub_coherence_le_two_mul_totalMisalign_div_sq {ι : Type*} (s : Finset ι) (A : ι → F)
    (hden : 0 < ∑ i ∈ s, ‖A i‖) :
    1 - multiPieceNormCoherence s A ≤ 2 * totalPairwiseMisalign s A / (∑ i ∈ s, ‖A i‖) ^ 2 := by
  set M := ∑ i ∈ s, ‖A i‖ with hM
  set s0 := ‖∑ i ∈ s, A i‖ with hs0
  have htri : s0 ≤ M := by rw [hs0, hM]; exact norm_sum_le _ _
  have hs0nn : 0 ≤ s0 := by rw [hs0]; exact norm_nonneg _
  have h2 : 2 * totalPairwiseMisalign s A = M ^ 2 - s0 ^ 2 := two_mul_totalPairwiseMisalign s A
  have hdefect : 1 - multiPieceNormCoherence s A = (M - s0) / M := by
    unfold multiPieceNormCoherence
    rw [sub_div, div_self (ne_of_gt hden)]
  rw [hdefect, h2]
  -- (M−s0)/M ≤ (M²−s0²)/M² = (M−s0)(M+s0)/M²  since (M+s0)/M ≥ 1
  have hMpos : (0:ℝ) < M ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hMpos]
  -- (M−s0) · M² ≤ (M²−s0²) · M  ⟺  0 ≤ M·(M−s0)·s0
  have hMs0 : 0 ≤ M - s0 := by linarith
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt hden) hMs0) hs0nn, hMs0, hs0nn, htri]

/-- **The two-sided sandwich (citable capstone).** The multi-piece coherence deficit is pinned, up to
a factor `2`, by the total pairwise misalignment `S(A)`:
`S(A)/M²  ≤  1 − ρ_multi  ≤  2·S(A)/M²`. -/
theorem coherence_deficit_pairwise_sandwich {ι : Type*} (s : Finset ι) (A : ι → F)
    (hden : 0 < ∑ i ∈ s, ‖A i‖) :
    totalPairwiseMisalign s A / (∑ i ∈ s, ‖A i‖) ^ 2 ≤ 1 - multiPieceNormCoherence s A
      ∧ 1 - multiPieceNormCoherence s A ≤ 2 * totalPairwiseMisalign s A / (∑ i ∈ s, ‖A i‖) ^ 2 :=
  ⟨totalMisalign_div_sq_le_one_sub_coherence s A hden,
   one_sub_coherence_le_two_mul_totalMisalign_div_sq s A hden⟩

end ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich

#print axioms ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich.sq_sum_norm_eq_double
#print axioms ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich.norm_sum_sq_eq_double
#print axioms ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich.two_mul_totalPairwiseMisalign
#print axioms ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich.totalPairwiseMisalign_nonneg
#print axioms ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich.totalMisalign_div_sq_le_one_sub_coherence
#print axioms ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich.one_sub_coherence_le_two_mul_totalMisalign_div_sq
#print axioms ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich.coherence_deficit_pairwise_sandwich
