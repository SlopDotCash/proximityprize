/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProductionBoundaryFailure
import ArkLib.Data.CodingTheory.ProximityGap.Round8CosetWall
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget

/-! # Full affine-line MCA error at the Reed–Solomon boundary

An integer bad-scalar count attains its field-size ceiling once the number of
minimal detecting supports exceeds the square of one less than the field size.
-/

open scoped NNReal ENNReal
open Polynomial Code
namespace ProximityGap.BoundaryFullMass

open Ownership SpikeFloor

variable {F : Type} {n : ℕ}

section
variable [Field F] [Fintype F] [NeZero n]

private theorem full_count {N q M : ℕ} (hq : 0 < q) (hM : M ≤ q)
    (hdense : (q - 1) ^ 2 < N) (hmoment : N * q ≤ M * (q + N - 1)) : M = q := by
  by_contra h
  have hpred : M ≤ q - 1 := by omega
  have hmul := hmoment.trans (Nat.mul_le_mul_right _ hpred)
  have hp : q = (q - 1) + 1 := by omega
  have heq : q + N - 1 = (q - 1) + N := by omega
  rw [heq] at hmul
  nlinarith [congrArg (N * ·) hp]

/-- A single polynomial line has every field element bad at the boundary. -/
theorem exists_all_bad (D : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hdense : (Fintype.card F - 1) ^ 2 < n.choose (k + 1)) :
    ∃ Q : F[X], ∀ γ : F, mcaEvent (F := F) (rsCode D k : Set (Fin n → F)) δ
      (fun i => Q.eval (D i)) (fun i => (D i) ^ k) γ := by
  classical
  obtain ⟨Q, hQ⟩ := boundary_production_failure D hk hlo hhi
  let bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    (rsCode D k : Set (Fin n → F)) δ (fun i => Q.eval (D i)) (fun i => (D i) ^ k) γ)
  have hcard : bad.card = Fintype.card F := full_count Fintype.card_pos bad.card_le_univ hdense hQ
  have hset := Finset.eq_univ_of_card bad hcard
  refine ⟨Q, fun γ => ?_⟩
  have hmem : γ ∈ bad := hset ▸ Finset.mem_univ γ
  exact (Finset.mem_filter.mp hmem).2

/-- The canonical affine - line error is exactly one throughout the boundary band. -/
theorem mcaError_eq_one [SampleableType F] (D : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hdense : (Fintype.card F - 1) ^ 2 < n.choose (k + 1)) :
    CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F)
      (ReedSolomon.code D k) (δ : ℝ) = 1 := by
  classical
  rw [← BoundarySecurityBudget.rsCode_eq_code, ← epsMCA_eq_mcaError]
  obtain ⟨Q, hQ⟩ := exists_all_bad D hk hlo hhi hdense
  exact epsMCA_eq_one_of_forall_mcaEvent _ δ
    (finMapTwoWords (fun i => Q.eval (D i)) (fun i => (D i) ^ k)) hQ

end

variable [Fintype F] [Nonempty F]

/-- An easily checked bit - size condition implies the dense - support hypothesis. -/
theorem dense_of_bits {k b : ℕ} (hkn : k + 1 ≤ n) (hq : Fintype.card F ≤ 2 ^ b)
    (hb : 2 * b ≤ min (k + 1) (n - (k + 1))) : (Fintype.card F - 1) ^ 2 < n.choose (k + 1) := by
  have hc : 2 ^ min (k + 1) (n - (k + 1)) ≤ n.choose (k + 1) := by
    rcases le_total (k + 1) (n - (k + 1)) with h | h
    · rw [min_eq_left h]
      exact ArkLib.ProximityGap.Round8CosetWall.two_pow_le_choose_count n _ (by omega)
    · rw [min_eq_right h, ← Nat.choose_symm hkn]
      exact ArkLib.ProximityGap.Round8CosetWall.two_pow_le_choose_count n _ (by omega)
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hlt : Fintype.card F - 1 < 2 ^ b := by omega
  calc
    (Fintype.card F - 1) ^ 2 < (2 ^ b) ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
    _ = 2 ^ (2 * b) := by rw [← pow_mul, Nat.mul_comm b 2]
    _ ≤ 2 ^ min (k + 1) (n - (k + 1)) := Nat.pow_le_pow_right (by decide) hb
    _ ≤ _ := hc

#print axioms exists_all_bad
#print axioms mcaError_eq_one
#print axioms dense_of_bits
end ProximityGap.BoundaryFullMass
