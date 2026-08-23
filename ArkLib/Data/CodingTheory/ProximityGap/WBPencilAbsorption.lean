/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# The Welch–Berlekamp absorption lemma (#371, H-RC stage i)

The first brick of the WB-pencil programme: a received word is within distance `w`
of the Reed–Solomon code **iff** the Welch–Berlekamp relation is solvable —
a nonzero `ℓ` of degree ≤ w and an `R` of degree ≤ w+k−1 with

  `ℓ(xᵢ)·yᵢ = R(xᵢ)` at EVERY domain point.

Forward: take `ℓ = ∏_{i ∈ E}(X − xᵢ)` over the disagreement set and `R = ℓ·P`; the
error positions are absorbed by the vanishing of `ℓ`.  Backward: off the ≤ w roots
of `ℓ`, division recovers a degree-< k explanation... the backward direction needs
the root/agreement count and is the consumer's (`WBPencilBound`) business; this file
proves the forward (absorption) direction, which is what the pencil bound consumes:
**every bad scalar yields a WB solution**, linearly in `(ℓ, R)` along the γ-line.
-/

open Finset Polynomial

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The Welch–Berlekamp relation for a received word `y` at slack `w`. -/
def WBSolvable (dom : Fin n ↪ F) (k w : ℕ) (y : Fin n → F) : Prop :=
  ∃ ℓ R : F[X], ℓ ≠ 0 ∧ ℓ.natDegree ≤ w ∧ R.natDegree ≤ w + k - 1 ∧
    ∀ i : Fin n, ℓ.eval (dom i) * y i = R.eval (dom i)

/-- **The absorption lemma**: a word agreeing with a degree-`< k` polynomial on all
but at most `w` positions satisfies the WB relation.  (`1 ≤ k` keeps the degree
budget `w + k − 1` honest.) -/
theorem wbSolvable_of_close (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    {y : Fin n → F} {P : F[X]} (hP : P.natDegree < k)
    {E : Finset (Fin n)} (hE : E.card ≤ w)
    (hagree : ∀ i, i ∉ E → P.eval (dom i) = y i) :
    WBSolvable dom k w y := by
  classical
  set ℓ : F[X] := ∏ i ∈ E, (X - C (dom i)) with hℓ
  have hℓ0 : ℓ ≠ 0 := by
    rw [hℓ]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (dom i)
  have hℓdeg : ℓ.natDegree ≤ w := by
    calc ℓ.natDegree = ∑ i ∈ E, (X - C (dom i)).natDegree :=
          natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (dom i)
      _ = ∑ _i ∈ E, 1 := Finset.sum_congr rfl fun i _ => natDegree_X_sub_C (dom i)
      _ = E.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ w := hE
  refine ⟨ℓ, ℓ * P, hℓ0, hℓdeg, ?_, ?_⟩
  · calc (ℓ * P).natDegree ≤ ℓ.natDegree + P.natDegree := natDegree_mul_le
      _ ≤ w + (k - 1) := Nat.add_le_add hℓdeg (by omega)
      _ = w + k - 1 := by omega
  · intro i
    by_cases hi : i ∈ E
    · -- the error position is absorbed: ℓ vanishes there
      have hz : ℓ.eval (dom i) = 0 := by
        rw [hℓ, eval_prod]
        exact Finset.prod_eq_zero hi (by simp)
      rw [eval_mul, hz, zero_mul, zero_mul]
    · rw [eval_mul, hagree i hi]

/-- The line form the pencil consumes: every explainable scalar (in the
`FarCosetExplosion` sense, with agreement ≥ n − w) yields a WB solution for the
line `u₀ + γ·u₁`. -/
theorem wbSolvable_of_explainable (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hw : w ≤ n) {u₀ u₁ : Fin n → F} {γ : F}
    (h : ∃ S : Finset (Fin n), n - w ≤ S.card ∧
      ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        ∀ i ∈ S, c i = u₀ i + γ * u₁ i) :
    WBSolvable dom k w (fun i => u₀ i + γ * u₁ i) := by
  classical
  obtain ⟨S, hS, c, hc, hcag⟩ := h
  obtain ⟨P, hPdeg, rfl⟩ := hc
  have hPdeg' : P.natDegree < k := by
    by_cases hP0 : P = 0
    · subst hP0
      simpa using hk
    · have := Polynomial.natDegree_lt_iff_degree_lt (n := k) (hP0) |>.mpr hPdeg
      exact this
  refine wbSolvable_of_close dom hk hPdeg' (E := Finset.univ \ S) ?_ ?_
  · have := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin n)) S
    have hcap : (Finset.univ ∩ S).card = S.card := by
      rw [Finset.univ_inter]
    have huniv : (Finset.univ : Finset (Fin n)).card = n := by
      rw [Finset.card_univ, Fintype.card_fin]
    omega
  · intro i hi
    have hiS : i ∈ S := by
      by_contra hns
      exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hns⟩)
    exact hcag i hiS

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.wbSolvable_of_close
#print axioms ProximityGap.WBPencil.wbSolvable_of_explainable
