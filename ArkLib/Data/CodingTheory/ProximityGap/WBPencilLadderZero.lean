/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilRationalReduction

/-!
# Theorem WB-3a: genuine rational pairs have NO bad scalars below the ladder reach

The first proven regime of the WB-2 residual: for a **genuinely rational** stack —
`u_j = R_j/ℓ_j` on the domain with `deg ℓ_j ≤ w`, `deg R_j ≤ w+k−1`, denominators
nonvanishing on the domain and coprime, and `ℓ₀ ∤ R₀` — at any radius with witness
floor `≥ n − w` and `3w + k ≤ n` (the ladder reach):

**no scalar is even line-explainable**, a fortiori none is MCA-bad.

Mechanism: an explaining codeword `P` forces, by degree counting
(`agreement ≥ n − w > 2w + k − 1 ≥ deg`), the polynomial identity
`P·ℓ₀·ℓ₁ = ℓ₁·R₀ + γ·ℓ₀·R₁`; then `ℓ₀ ∣ ℓ₁·R₀`, and coprimality gives `ℓ₀ ∣ R₀` —
contradicting genuineness.  Together with WB-1/WB-2 this proves the below-ladder
two-sided picture for the rational family and confirms the probe data
(`probe_rational_pair_extremality.py`: zero bad scalars).
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THEOREM WB-3a.**  A genuinely rational stack below the ladder reach has no
line-explainable scalar at witness floor `n − w`: the per-γ explanation forces a
polynomial identity that contradicts `ℓ₀ ∤ R₀`. -/
theorem rational_pair_no_explainable (dom : Fin n ↪ F) {k w : ℕ}
    (hlad : 3 * w + k ≤ n) (hk : 1 ≤ k)
    {ℓ₀ ℓ₁ R₀ R₁ : F[X]}
    (hℓ₀d : ℓ₀.natDegree ≤ w) (hℓ₁d : ℓ₁.natDegree ≤ w)
    (hR₀d : R₀.natDegree ≤ w + k - 1) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen : ¬ ℓ₀ ∣ R₀) (γ : F) :
    ¬ ∃ S : Finset (Fin n), n - w ≤ S.card ∧
      ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        ∀ i ∈ S, c i = R₀.eval (dom i) / ℓ₀.eval (dom i)
          + γ * (R₁.eval (dom i) / ℓ₁.eval (dom i)) := by
  rintro ⟨S, hScard, c, hc, hag⟩
  obtain ⟨P, hPdeg, rfl⟩ := hc
  -- the difference polynomial
  set Q : F[X] := P * ℓ₀ * ℓ₁ - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) with hQ
  -- Q vanishes on the witness image
  have hQvan : ∀ i ∈ S, Q.eval (dom i) = 0 := by
    intro i hi
    have h : P.eval (dom i) = R₀.eval (dom i) / ℓ₀.eval (dom i)
        + γ * (R₁.eval (dom i) / ℓ₁.eval (dom i)) := hag i hi
    have h0 := hℓ₀v i
    have h1 := hℓ₁v i
    rw [hQ]
    simp only [eval_sub, eval_add, eval_mul, eval_C]
    rw [h]
    field_simp
    ring
  -- degree: Q ≤ 2w + k − 1 < n − w ≤ |S|
  have hPdeg' : P.natDegree ≤ k - 1 := by
    by_cases hP0 : P = 0
    · subst hP0
      simp
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
      omega
  have hQdeg : Q.natDegree ≤ 2 * w + k - 1 := by
    rw [hQ]
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · calc (P * ℓ₀ * ℓ₁).natDegree
          ≤ (P * ℓ₀).natDegree + ℓ₁.natDegree := natDegree_mul_le
        _ ≤ (P.natDegree + ℓ₀.natDegree) + ℓ₁.natDegree :=
            Nat.add_le_add_right natDegree_mul_le _
        _ ≤ ((k - 1) + w) + w := by
            exact Nat.add_le_add (Nat.add_le_add hPdeg' hℓ₀d) hℓ₁d
        _ ≤ 2 * w + k - 1 := by omega
    · refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · calc (ℓ₁ * R₀).natDegree ≤ ℓ₁.natDegree + R₀.natDegree := natDegree_mul_le
          _ ≤ w + (w + k - 1) := Nat.add_le_add hℓ₁d hR₀d
          _ ≤ 2 * w + k - 1 := by omega
      · calc (C γ * (ℓ₀ * R₁)).natDegree
            ≤ (C γ).natDegree + (ℓ₀ * R₁).natDegree := natDegree_mul_le
          _ ≤ 0 + (ℓ₀.natDegree + R₁.natDegree) :=
              Nat.add_le_add (le_of_eq (natDegree_C _)) natDegree_mul_le
          _ ≤ 0 + (w + (w + k - 1)) :=
              Nat.add_le_add_left (Nat.add_le_add hℓ₀d hR₁d) 0
          _ ≤ 2 * w + k - 1 := by omega
  -- forcing: Q = 0
  have hQ0 : Q = 0 := by
    by_contra hQne
    have hroots : (S.image dom).card ≤ Q.roots.toFinset.card := by
      refine Finset.card_le_card ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, mem_roots hQne]
      exact hQvan i hi
    have himg : (S.image dom).card = S.card :=
      Finset.card_image_of_injective _ dom.injective
    have h1 := Q.roots.toFinset_card_le
    have h2 := Q.card_roots'
    omega
  -- the identity and the divisibility contradiction
  have hid : ℓ₁ * R₀ = ℓ₀ * (P * ℓ₁ - C γ * R₁) := by
    have h := sub_eq_zero.mp hQ0
    calc ℓ₁ * R₀ = P * ℓ₀ * ℓ₁ - C γ * (ℓ₀ * R₁) := by
          rw [h]
          ring
      _ = ℓ₀ * (P * ℓ₁ - C γ * R₁) := by ring
  have hdvd : ℓ₀ ∣ ℓ₁ * R₀ := Dvd.intro _ hid.symm
  exact hgen (hcop.dvd_of_dvd_mul_left hdvd)

open Classical in
/-- The MCA form: a genuinely rational stack below the ladder reach has **no bad
scalar at all** at any radius `δ ≤ w/n`. -/
theorem rational_pair_no_mcaEvent (dom : Fin n ↪ F) {k w : ℕ}
    (hlad : 3 * w + k ≤ n) (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {ℓ₀ ℓ₁ R₀ R₁ : F[X]}
    (hℓ₀d : ℓ₀.natDegree ≤ w) (hℓ₁d : ℓ₁.natDegree ≤ w)
    (hR₀d : R₀.natDegree ≤ w + k - 1) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen : ¬ ℓ₀ ∣ R₀) (γ : F) :
    ¬ mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ := by
  intro h
  obtain ⟨S, hsz, ⟨c, hc, hag⟩, -⟩ := h
  refine rational_pair_no_explainable dom hlad hk hℓ₀d hℓ₁d hR₀d hR₁d hℓ₀v hℓ₁v
    hcop hgen γ ⟨S, ?_, c, hc, fun i hi => ?_⟩
  · -- the size cast (the established pattern)
    have hw : w ≤ n := by omega
    have h1 : ((n - w : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      have hnw : ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by
        rw [Nat.cast_tsub]
      have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
        rw [Fintype.card_fin]
      calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := hnw
        _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
            exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
        _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
            rw [tsub_mul, one_mul, hcardn]
        _ ≤ (S.card : ℝ≥0) := hsz
    exact_mod_cast h1
  · have := hag i hi
    simpa [smul_eq_mul] using this

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.rational_pair_no_explainable
#print axioms ProximityGap.WBPencil.rational_pair_no_mcaEvent
