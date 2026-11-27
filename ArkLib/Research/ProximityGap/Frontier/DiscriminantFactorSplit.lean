/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HeightOneNormalization
import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.ResultantDegree
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Squarefree.Basic

/-! # Binary discriminant degree bounds, factor split, and unramifiedness off the discriminant

This module implements Worker Packet L1a for the purely algebraic logarithmic section-height
engine:
1. Weighted degree bounds for `Polynomial.discr`, yielding `deg_Z (F.discr) ≤ G` and
   `deg_X (F.discr) ≤ A` for `F : K[X][X][X]`.
2. Transformation laws of `Polynomial.discr` under scalar multiplication, `taylor`, and `reflect`.
3. Squarefree 3-way factor split `V(Z) * U(X) * H(X, Z)` of any nonzero `Δ : K[X][X]`, with
   `H` free of horizontal and vertical factors.
4. For every prime `p : K[X][X]` and branch `w : HeightOneSpectrum (localNormalization E hp)`:
   - universal ramification and inertia bounds `e ≤ b`, `f ≤ b` (giving tameness and residue
     separability whenever `char K = 0 ∨ b < char K`), and
   - unramifiedness (`e = 1`) whenever `¬ p ∣ F.discr` (including when `p ∣ F.leadingCoeff`),
     via a projective coordinate inversion `T = 1 / (Y - a)` and `differentIdeal = ⊤`.
-/

set_option autoImplicit false
set_option linter.style.longFile 1900
noncomputable section

open Polynomial Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.DiscriminantFactorSplit

/-! ## Section 1: Weighted degree bounds for `Polynomial.discr` -/

section WeightedDiscr

private lemma sylvester_reindex_eq {R : Type*} [CommRing R] (f g : R[X]) {m n m' n' : ℕ}
    (hm : m = m') (hn : n = n') :
    f.sylvester g m' n' =
      (f.sylvester g m n).reindex (finCongr (by rw [hm, hn])) (finCongr (by rw [hm, hn])) := by
  subst hm; subst hn; rfl

/-- Mapping coefficients preserves `sylvesterDeriv` when `natDegree` is preserved. -/
lemma sylvesterDeriv_map_of_natDegree_eq {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : R[X]) (hdeg : (F.map φ).natDegree = F.natDegree) :
    (F.map φ).sylvesterDeriv =
      (φ.mapMatrix F.sylvesterDeriv).reindex (finCongr (by rw [hdeg])) (finCongr (by rw [hdeg])) := by
  by_cases hn : F.natDegree = 0
  · have hn' : (F.map φ).natDegree = 0 := hdeg.trans hn
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [sylvesterDeriv, hn, hn']
  · ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [sylvesterDeriv, hn, ↓reduceDIte, Matrix.reindex_apply, Matrix.submatrix_apply,
      finCongr_symm, finCongr_apply, Fin.cast_mk, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.updateRow_apply, Fin.mk.injEq, hdeg]
    split_ifs with h1 h2 h3
    · simp
    · simp
    · simp
    · have hsyl := sylvester_reindex_eq (F.map φ).derivative (F.map φ)
        (m := F.natDegree - 1) (n := F.natDegree)
        (m' := (F.map φ).natDegree - 1) (n' := (F.map φ).natDegree)
        (by rw [hdeg]) hdeg.symm
      have hmap := Polynomial.sylvester_map_map F.derivative F (F.natDegree - 1) F.natDegree φ
      rw [← Polynomial.derivative_map] at hmap
      rw [hsyl, hmap]
      simp [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply]

/-- Mapping coefficients preserves `Polynomial.discr` when `natDegree` is preserved. -/
lemma discr_map_of_natDegree_eq {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : R[X]) (hdeg : (F.map φ).natDegree = F.natDegree) :
    (F.map φ).discr = φ F.discr := by
  unfold Polynomial.discr
  rw [sylvesterDeriv_map_of_natDegree_eq φ F hdeg, Matrix.det_reindex_self, hdeg,
    ← RingHom.map_det, map_mul, map_pow, map_neg, map_one]

/-- Weighted degree bound for `Polynomial.discr`: if `F : R[X][X]` has `b = F.natDegree ≥ 2`,
`b * w ≤ W`, and `(F.coeff j).natDegree + w * j ≤ W` for every nonzero coefficient, then
`F.discr.natDegree ≤ (2 * b - 2) * W - b * (b - 1) * w`. -/
theorem natDegree_discr_le_weighted {R : Type*} [CommRing R] (F : R[X][X]) (w W : ℕ)
    (hb : 2 ≤ F.natDegree) (hW : F.natDegree * w ≤ W)
    (hF : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree + w * j ≤ W) :
    F.discr.natDegree ≤ (2 * F.natDegree - 2) * W - F.natDegree * (F.natDegree - 1) * w := by
  classical
  set b := F.natDegree with hb_def
  have hb0 : b ≠ 0 := by omega
  have hwW : w ≤ W := by
    calc w = 1 * w := (one_mul w).symm
      _ ≤ b * w := Nat.mul_le_mul_right w (by omega)
      _ ≤ W := hW
  let M := F.sylvesterDeriv
  have hM_eq : M = (F.derivative.sylvester F (b - 1) b).updateRow ⟨2 * b - 2, by omega⟩
      (fun j ↦ if ↑j = b - 2 then 1 else (if ↑j = 2 * b - 2 then (b : R[X]) else 0)) := by
    change F.sylvesterDeriv = _
    unfold sylvesterDeriv
    rw [dite_eq_right hb0]
  let row : Fin (b - 1 + b) → ℕ :=
    fun i => if i.val = 2 * b - 2 then W + w * (b - 2) else w * i.val
  let col : Fin (b - 1 + b) → ℕ :=
    Fin.addCases (fun j : Fin (b - 1) => W + w * j.val) (fun j : Fin b => (W - w) + w * j.val)
  have hentry (i j : Fin (b - 1 + b)) (hne : M i j ≠ 0) : (M i j).natDegree + row i ≤ col j := by
    rw [hM_eq, Matrix.updateRow_apply] at hne ⊢
    by_cases hi : i = ⟨2 * b - 2, by omega⟩
    · subst hi
      simp only [↓reduceIte, row] at hne ⊢
      split_ifs at hne ⊢ with h1 h2
      · rw [natDegree_one, zero_add]
        have hjlt : j.val < b - 1 := by omega
        have hjeq : j = Fin.castAdd b ⟨j.val, hjlt⟩ := Fin.ext rfl
        rw [hjeq]
        simp only [col, Fin.addCases_left, h1, le_refl]
      · have hdegb : ((b : R[X]).natDegree) = 0 := natDegree_natCast b
        rw [hdegb, zero_add]
        have hjge : b - 1 ≤ j.val := by omega
        have hjlt : j.val - (b - 1) < b := by omega
        have hjeq : j = Fin.natAdd (b - 1) ⟨j.val - (b - 1), hjlt⟩ := by
          ext; dsimp; omega
        rw [hjeq]
        simp only [col, Fin.addCases_right]
        have hsub : j.val - (b - 1) = b - 1 := by omega
        rw [hsub]
        have hmul : w * (b - 1) = w + w * (b - 2) := by
          have : b - 1 = 1 + (b - 2) := by omega
          rw [this, Nat.mul_add, Nat.mul_one]
        omega
      · exact absurd rfl hne
    · have hival : i.val ≠ 2 * b - 2 := fun h => hi (Fin.ext h)
      simp only [hi, ↓reduceIte, row, hival] at hne ⊢
      cases j using Fin.addCases with
      | left j₁ =>
        simp only [sylvester, Matrix.of_apply, Fin.addCases_left] at hne ⊢
        split_ifs at hne ⊢ with h
        · have hh := hF _ hne
          have hsub : w * (i.val - j₁.val) + w * j₁.val = w * i.val := by
            rw [← Nat.mul_add, Nat.sub_add_cancel h.1]
          simp only [col, Fin.addCases_left]
          omega
        · exact absurd rfl hne
      | right j₁ =>
        simp only [sylvester, Matrix.of_apply, Fin.addCases_right] at hne ⊢
        split_ifs at hne ⊢ with h
        · have hne' : F.coeff (i.val - j₁.val + 1) ≠ 0 := by
            intro hz
            exact hne (by simp [coeff_derivative, hz])
          have hh := hF _ hne'
          have hcd : (F.derivative.coeff (i.val - j₁.val)).natDegree ≤
              (F.coeff (i.val - j₁.val + 1)).natDegree := coeff_derivative_natDegree_le F _
          have hmul : w * (i.val - j₁.val + 1) + w * j₁.val = w * i.val + w := by
            rw [Nat.mul_add, Nat.mul_one, add_right_comm, ← Nat.mul_add, Nat.sub_add_cancel h.1]
          simp only [col, Fin.addCases_right]
          omega
        · exact absurd rfl hne
  let S := (∑ j : Fin (b - 1), j.val) + ∑ j : Fin b, j.val
  have hcol_sum : ∑ j, col j = (b - 1) * W + b * (W - w) + w * S := by
    simp only [col, S, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, ← Finset.mul_sum]
    ring
  have hidx_sum : ∑ i : Fin (b - 1 + b), i.val = (b - 1) * b + S := by
    simp only [S, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hrow_sum : (∑ i, row i) + w * (2 * b - 2) = w * ((b - 1) * b + S) + (W + w * (b - 2)) := by
    let last : Fin (b - 1 + b) := ⟨2 * b - 2, by omega⟩
    have hsplit : ∑ i : Fin (b - 1 + b), row i =
        row last + ∑ i ∈ Finset.univ.erase last, row i :=
      (Finset.add_sum_erase Finset.univ row (Finset.mem_univ last)).symm
    have hsplit2 : ∑ i : Fin (b - 1 + b), w * i.val =
        w * last.val + ∑ i ∈ Finset.univ.erase last, w * i.val :=
      (Finset.add_sum_erase Finset.univ (fun i : Fin (b - 1 + b) => w * i.val)
        (Finset.mem_univ last)).symm
    have herase : ∑ i ∈ Finset.univ.erase last, row i =
        ∑ i ∈ Finset.univ.erase last, w * i.val := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hne : i.val ≠ 2 * b - 2 := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
      simp [row, hne]
    rw [hsplit, herase]
    have hfull : ∑ i : Fin (b - 1 + b), w * i.val = w * ((b - 1) * b + S) := by
      rw [← Finset.mul_sum, hidx_sum]
    have hlast : row last = W + w * (b - 2) := by simp [row, last]
    rw [hlast]
    have hlv : last.val = 2 * b - 2 := rfl
    rw [hlv] at hsplit2
    omega
  have hcol_row_rel : (∑ j, col j) + b * (b - 1) * w = (∑ i, row i) + (2 * b - 2) * W := by
    have hdiff1 : w * (2 * b - 2) = w * (b - 2) + b * w := by
      have : 2 * b - 2 = (b - 2) + b := by omega
      rw [this, Nat.mul_add, Nat.mul_comm w b]
    have hdiff2 : b * (W - w) + b * w = b * W := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hwW]
    have hdiff3 : (b - 1) * W + b * W = (2 * b - 2) * W + W := by
      have : (b - 1) + b = (2 * b - 2) + 1 := by omega
      rw [← Nat.add_mul, this, Nat.add_mul, one_mul]
    have hdiff4 : w * ((b - 1) * b) = b * (b - 1) * w := by ring
    rw [Nat.mul_add, hdiff4] at hrow_sum
    omega
  have hdiscr_le : F.discr.natDegree ≤ M.det.natDegree := by
    rw [Polynomial.discr]
    refine natDegree_mul_le.trans ?_
    have hsign : (((-1 : R[X]) ^ (b * (b - 1) / 2))).natDegree = 0 := by
      rw [show (-1 : R[X]) = C (-1 : R) by simp, ← C_pow, natDegree_C]
    rw [hsign, add_zero]
  refine hdiscr_le.trans ?_
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine (natDegree_smul_le _ _).trans ?_
  by_cases hz : ∃ j, M (σ j) j = 0
  · obtain ⟨j, hj⟩ := hz
    rw [Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) hj, natDegree_zero]
    exact Nat.zero_le _
  · push Not at hz
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ => hentry (σ j) j (hz j)
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ row] at hsum
    have hprod := natDegree_prod_le Finset.univ (fun j => M (σ j) j)
    have hle1 : (∏ i, M (σ i) i).natDegree + ∑ i : Fin (b - 1 + b), row i ≤
        ∑ j : Fin (b - 1 + b), col j := le_trans (Nat.add_le_add_right hprod _) hsum
    exact Nat.le_sub_of_add_le (by linarith [hle1, hcol_row_rel])

/-- Scalar-degree (`Z`-degree) bound for the binary discriminant of `F : K[X][X][X]`. -/
theorem discr_natDegree_le {K : Type*} [Field K] (F : K[X][X][X]) {m : ℕ}
    (hb : 2 ≤ F.natDegree)
    (hTot : ∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ m) :
    F.discr.natDegree ≤ (2 * F.natDegree - 2) * m - F.natDegree * (F.natDegree - 1) := by
  have hF : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree + 1 * j ≤ m := by
    intro j hj
    have hlc : (F.coeff j).coeff (F.coeff j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hj
    have hlc2 : ((F.coeff j).coeff (F.coeff j).natDegree).coeff
        ((F.coeff j).coeff (F.coeff j).natDegree).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hlc
    have h := hTot j _ _ hlc2
    omega
  have hm : F.natDegree * 1 ≤ m := by
    have hlc : F.coeff F.natDegree ≠ 0 :=
      leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (n := 0) (by omega))
    have := hF F.natDegree hlc
    omega
  simpa only [mul_one] using natDegree_discr_le_weighted F 1 m hb hm hF

private lemma natDegree_swap_eq_degreeX {K : Type*} [Field K] (p : K[X][X]) :
    (Bivariate.swap p).natDegree = Bivariate.degreeX p :=
  Bivariate.natDegreeY_swap p

private lemma discr_natDegree_map_ringHom {R S : Type*} [CommRing R] [CommRing S]
    (φ : R[X] →+* S[X]) (hinj : Function.Injective φ) (F : R[X][X]) (w W : ℕ)
    (hb : 2 ≤ F.natDegree)
    (hF : ∀ j, F.coeff j ≠ 0 → (φ (F.coeff j)).natDegree + w * j ≤ W) :
    (φ F.discr).natDegree ≤ (2 * F.natDegree - 2) * W - F.natDegree * (F.natDegree - 1) * w := by
  have hdeg : (F.map φ).natDegree = F.natDegree := natDegree_map_eq_of_injective hinj F
  have hFmap : ∀ j, (F.map φ).coeff j ≠ 0 → ((F.map φ).coeff j).natDegree + w * j ≤ W := by
    intro j hj
    rw [coeff_map] at hj ⊢
    exact hF j (fun hz => hj (by simp [hz]))
  have hW : (F.map φ).natDegree * w ≤ W := by
    have hlc : (F.map φ).coeff (F.map φ).natDegree ≠ 0 :=
      leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (n := 0) (by omega))
    have h := hFmap (F.map φ).natDegree hlc
    have hcomm : (F.map φ).natDegree * w = w * (F.map φ).natDegree := Nat.mul_comm _ _
    omega
  have hbound := natDegree_discr_le_weighted (F.map φ) w W (by omega) hW hFmap
  rw [discr_map_of_natDegree_eq φ F hdeg, hdeg] at hbound
  exact hbound

/-- Coordinate-degree (`X`-degree) bound for the binary discriminant of `F : K[X][X][X]`. -/
theorem discr_degreeX_le {K : Type*} [Field K] (F : K[X][X][X]) {d W : ℕ}
    (hb : 2 ≤ F.natDegree)
    (hWt : ∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → a + j * d ≤ W) :
    Bivariate.degreeX F.discr ≤
      (2 * F.natDegree - 2) * W - F.natDegree * (F.natDegree - 1) * d := by
  rw [← natDegree_swap_eq_degreeX]
  refine discr_natDegree_map_ringHom Bivariate.swap.toRingHom Bivariate.swap.injective F d W hb ?_
  intro j hj
  change (Bivariate.swap (F.coeff j)).natDegree + d * j ≤ W
  rw [natDegree_swap_eq_degreeX]
  obtain ⟨i, hi, heq, _⟩ := Bivariate.exists_max_index_degreeX (F.coeff j) hj
  have ha := leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi)
  have h := hWt j i _ ha
  rw [← heq]
  have hcomm : d * j = j * d := Nat.mul_comm d j
  omega

/-- An irreducible polynomial `F : K[X][X][X]` of value degree `b ≥ 2` with `(b : K) ≠ 0`
has nonzero binary discriminant. -/
theorem discr_ne_zero {K : Type*} [Field K] (F : K[X][X][X]) (hIrr : Irreducible F)
    (hb : 2 ≤ F.natDegree) (hchar : (F.natDegree : K) ≠ 0) : F.discr ≠ 0 := by
  have hF0 : F ≠ 0 := hIrr.ne_zero
  have hpos : 0 < F.degree := natDegree_pos_iff_degree_pos.mp (by omega)
  have hlead : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF0
  have hder0 : F.derivative ≠ 0 := by
    intro hz
    have hcoeff := congrArg (fun p : K[X][X][X] => p.coeff (F.natDegree - 1)) hz
    rw [coeff_derivative, coeff_zero, show F.natDegree - 1 + 1 = F.natDegree by omega] at hcoeff
    have hcast : ((F.natDegree - 1 : ℕ) + 1 : K[X][X]) = C (C (F.natDegree : K)) := by
      rw [← Nat.cast_add_one, show F.natDegree - 1 + 1 = F.natDegree by omega]
      simp
    rw [hcast] at hcoeff
    have hcne : (C (C (F.natDegree : K)) : K[X][X]) ≠ 0 :=
      C_ne_zero.mpr (C_ne_zero.mpr hchar)
    exact (mul_ne_zero hlead hcne) hcoeff
  have hnd : ¬ F ∣ F.derivative := fun hdvd =>
    (natDegree_le_of_dvd hdvd hder0).not_gt ((natDegree_derivative_lt (by omega)))
  let L := FractionRing K[X][X]
  let φ := algebraMap K[X][X] L
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hprim : F.IsPrimitive := hIrr.isPrimitive (by omega)
  have hirrL : Irreducible (F.map φ) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := L)).mp hIrr
  have hndL : ¬ F.map φ ∣ F.derivative.map φ := fun hd =>
    hnd ((hprim.dvd_iff_fraction_map_dvd_fraction_map L).mpr hd)
  have hcop : IsCoprime (F.map φ) (F.derivative.map φ) :=
    (hirrL.isCoprime_or_dvd _).resolve_right hndL
  have hres0 : resultant (F.map φ) (F.derivative.map φ) ≠ 0 :=
    Polynomial.resultant_ne_zero _ _ hcop
  have hderdeg : F.derivative.natDegree ≤ F.natDegree - 1 := natDegree_derivative_le F
  have hpad : resultant (F.map φ) (F.derivative.map φ) (F.map φ).natDegree
      ((F.map φ).natDegree - 1) ≠ 0 := by
    have h1 := resultant_add_right_deg (F.map φ) (F.derivative.map φ) (F.map φ).natDegree
      (F.derivative.map φ).natDegree ((F.map φ).natDegree - 1 - (F.derivative.map φ).natDegree) le_rfl
    have hle : (F.derivative.map φ).natDegree ≤ (F.map φ).natDegree - 1 := by
      rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj]
      exact hderdeg
    rw [Nat.add_sub_of_le hle, coeff_natDegree] at h1
    rw [h1]
    exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hirrL.ne_zero)) hres0
  intro hdz
  apply hpad
  rw [natDegree_map_eq_of_injective hinj, resultant_map_map, resultant_deriv hpos, hdz, mul_zero,
    map_zero]

end WeightedDiscr

/-! ## Section 2: Discriminant transformation laws (`C c *`, `taylor`, `reflect`) -/

section DiscrTransform

/-- Scaling a positive-degree polynomial by a nonzero constant multiplies `discr` by `c^(2d-2)`. -/
theorem discr_C_mul {R : Type*} [CommRing R] [IsDomain R] (f : R[X])
    (hf : 0 < f.natDegree) {c : R} (hc : c ≠ 0) :
    (C c * f).discr = c ^ (2 * f.natDegree - 2) * f.discr := by
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  have hdeg : (C c * f).natDegree = f.natDegree := natDegree_C_mul hc
  have hlc : (C c * f).leadingCoeff = c * f.leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C]
  have hpos : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hf
  have hpos' : 0 < (C c * f).degree := natDegree_pos_iff_degree_pos.mp (hdeg ▸ hf)
  have hres1 := Polynomial.resultant_deriv hpos'
  have hres2 := Polynomial.resultant_deriv hpos
  rw [hdeg, hlc, derivative_C_mul, resultant_C_mul_left,
    resultant_C_mul_right, hres2] at hres1
  have hpow : c ^ (f.natDegree - 1) * c ^ f.natDegree = c * c ^ (2 * f.natDegree - 2) := by
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  have hne : (-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2) * (c * f.leadingCoeff) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (mul_ne_zero hc (leadingCoeff_ne_zero.mpr hf0))
  apply mul_left_cancel₀ hne
  linear_combination -hres1 + (f.discr * f.leadingCoeff * (-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) * hpow

private lemma derivative_taylor_eq {R : Type*} [CommRing R] (a : R) (f : R[X]) :
    (f.taylor a).derivative = f.derivative.taylor a := by
  rw [taylor_apply, taylor_apply, derivative_comp, derivative_add, derivative_X, derivative_C,
    add_zero, one_mul]

/-- Translation `taylor a` preserves `Polynomial.discr`. -/
theorem discr_taylor {R : Type*} [CommRing R] [IsDomain R] (f : R[X])
    (hf : 0 < f.natDegree) (a : R) : (f.taylor a).discr = f.discr := by
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  have hdeg : (f.taylor a).natDegree = f.natDegree := natDegree_taylor f a
  have hlc : (f.taylor a).leadingCoeff = f.leadingCoeff := by
    rw [leadingCoeff, hdeg, coeff_taylor_natDegree]
  have hpos : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hf
  have hpos' : 0 < (f.taylor a).degree := natDegree_pos_iff_degree_pos.mp (hdeg ▸ hf)
  have h1 := Polynomial.resultant_deriv hpos'
  have h2 := Polynomial.resultant_deriv hpos
  rw [hdeg, hlc, derivative_taylor_eq] at h1
  have hderdeg : (f.derivative.taylor a).natDegree = f.derivative.natDegree := natDegree_taylor _ a
  have hpad1 := resultant_add_right_deg (f.taylor a) (f.derivative.taylor a)
    (f.taylor a).natDegree (f.derivative.taylor a).natDegree
    (f.natDegree - 1 - f.derivative.natDegree) le_rfl
  have hpad2 := resultant_add_right_deg f f.derivative f.natDegree f.derivative.natDegree
    (f.natDegree - 1 - f.derivative.natDegree) le_rfl
  rw [coeff_natDegree, hlc] at hpad1
  rw [hdeg, hderdeg, Nat.add_sub_of_le (natDegree_derivative_le f)] at hpad1
  rw [Nat.add_sub_of_le (natDegree_derivative_le f), coeff_natDegree] at hpad2
  have hres_eq : resultant (f.taylor a) (f.derivative.taylor a) f.natDegree (f.natDegree - 1) =
      resultant f f.derivative f.natDegree (f.natDegree - 1) := by
    rw [hpad1, hpad2]
    congr 1
    have ht := Polynomial.resultant_taylor f f.derivative a
    rw [hdeg, hderdeg] at ht
    exact ht
  rw [hres_eq, h2] at h1
  have hne : (-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (leadingCoeff_ne_zero.mpr hf0)
  exact mul_left_cancel₀ hne (by linear_combination -h1)

private lemma discr_of_prod_linear {Ω : Type*} [Field Ω] {b : ℕ} (hb : 2 ≤ b)
    (c : Ω) (hc : c ≠ 0) (r : Fin b → Ω) :
    (C c * ∏ i : Fin b, (X - C (r i))).discr =
      (-1 : Ω) ^ (b * (b - 1) / 2) * c ^ (2 * b - 2) *
        ∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (r i - r j) := by
  let p : Polynomial Ω := C c * ∏ i : Fin b, (X - C (r i))
  have hm : (∏ i : Fin b, (X - C (r i))).Monic :=
    monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (r i))
  have hpd : (∏ i : Fin b, (X - C (r i))).natDegree = b := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (r i))]
    simp
  have hpdeg : p.natDegree = b := by
    dsimp [p]
    rw [natDegree_C_mul hc, hpd]
  have hplc : p.leadingCoeff = c := by
    dsimp [p]
    rw [leadingCoeff_mul, leadingCoeff_C, hm.leadingCoeff, mul_one]
  have hpos : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (by omega)
  have hsplits : p.Splits := by
    dsimp [p]
    exact (Splits.C c).mul (Splits.prod (fun i _ => Splits.X_sub_C (r i)))
  have hroots : p.roots = (Finset.univ.val.map r) := by
    have hprod_ne : (∏ i : Fin b, (X - C (r i))) ≠ 0 := hm.ne_zero
    dsimp [p]
    rw [roots_C_mul _ hc, roots_prod _ _ hprod_ne]
    simp
  have hder_eval (i : Fin b) :
      p.derivative.eval (r i) = c * ∏ j ∈ Finset.univ.erase i, (r i - r j) := by
    have hfac : p = (X - C (r i)) * (C c * ∏ j ∈ Finset.univ.erase i, (X - C (r j))) := by
      dsimp [p]
      rw [← Finset.mul_prod_erase Finset.univ (fun j => X - C (r j)) (Finset.mem_univ i)]
      ring
    rw [hfac, derivative_mul]
    simp only [eval_add, eval_mul, derivative_X_sub_C, one_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, add_zero, eval_prod]
  have hres := Polynomial.resultant_deriv hpos
  rw [hpdeg, hplc] at hres
  have hprod := Polynomial.resultant_eq_prod_eval p p.derivative (b - 1)
    (hpdeg ▸ natDegree_derivative_le p) hsplits
  rw [hpdeg, hplc, hroots, Multiset.map_map] at hprod
  have hprod_fin : ((Finset.univ.val.map (p.derivative.eval ∘ r)).prod) =
      ∏ i : Fin b, p.derivative.eval (r i) := rfl
  rw [hprod_fin] at hprod
  have hprod_val : (∏ i : Fin b, p.derivative.eval (r i)) =
      c ^ b * ∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (r i - r j) := by
    simp_rw [hder_eval]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod_val, ← mul_assoc, ← pow_add] at hprod
  rw [hprod] at hres
  have hpow : c ^ (b - 1 + b) = c * c ^ (2 * b - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at hres
  have hsign_sq : ((-1 : Ω) ^ (b * (b - 1) / 2)) * ((-1 : Ω) ^ (b * (b - 1) / 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hne : (-1 : Ω) ^ (b * (b - 1) / 2) * c ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hc
  apply mul_left_cancel₀ hne
  calc
    (-1 : Ω) ^ (b * (b - 1) / 2) * c * p.discr
        = c * c ^ (2 * b - 2) * ∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (r i - r j) := hres.symm
    _ = ((-1 : Ω) ^ (b * (b - 1) / 2) * (-1 : Ω) ^ (b * (b - 1) / 2)) *
          (c * c ^ (2 * b - 2) * ∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (r i - r j)) := by
        rw [hsign_sq, one_mul]
    _ = (-1 : Ω) ^ (b * (b - 1) / 2) * c *
          ((-1 : Ω) ^ (b * (b - 1) / 2) * c ^ (2 * b - 2) *
            ∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (r i - r j)) := by ring

private lemma reflect_prod_X_sub_C {Ω : Type*} [Field Ω] {b : ℕ} (r : Fin b → Ω) :
    (∏ i : Fin b, (X - C (r i))).reflect b = ∏ i : Fin b, (1 - C (r i) * X) := by
  have h : ∀ (s : Finset (Fin b)),
      (∏ i ∈ s, (X - C (r i))).reflect s.card = ∏ i ∈ s, (1 - C (r i) * X) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
        Nat.add_comm, reflect_mul _ _ (natDegree_X_sub_C_le _)]
      · rw [ih]
        congr 1
        rw [sub_eq_add_neg, ← map_neg, reflect_add, reflect_one_X, reflect_C]
        simp [sub_eq_add_neg]
      · have hm : ∀ j ∈ s, (X - C (r j)).Monic := fun j _ => monic_X_sub_C _
        rw [natDegree_prod_of_monic s _ hm]
        simp
  simpa using h Finset.univ

/-- Reflecting a polynomial of degree `b ≥ 2` with nonzero constant term preserves `Polynomial.discr`. -/
theorem discr_reflect {R : Type*} [CommRing R] [IsDomain R] (f : R[X])
    (hb : 2 ≤ f.natDegree) (h0 : f.coeff 0 ≠ 0) :
    (f.reflect f.natDegree).discr = f.discr := by
  let Ω := AlgebraicClosure (FractionRing R)
  let φ : R →+* Ω := (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R))
  have hinj : Function.Injective φ :=
    (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  set b := f.natDegree with hb_def
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by omega)
  have hrefdeg : (f.reflect b).natDegree = b := by
    apply le_antisymm (natDegree_reflect_le.trans (by omega))
    apply le_natDegree_of_ne_zero
    simpa [coeff_reflect, revAt_le le_rfl] using h0
  apply hinj
  rw [← discr_map_of_natDegree_eq φ f (natDegree_map_eq_of_injective hinj f),
    ← discr_map_of_natDegree_eq φ (f.reflect b) (natDegree_map_eq_of_injective hinj _),
    ← reflect_map]
  let p : Polynomial Ω := f.map φ
  have hpdeg : p.natDegree = b := natDegree_map_eq_of_injective hinj f
  have hplc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (n := 0) (by omega))
  have hp0 : p.coeff 0 ≠ 0 := by
    rw [coeff_map]
    exact (map_ne_zero_iff φ hinj).mpr h0
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = b := hpdeg ▸ hsplits.natDegree_eq_card_roots.symm
  let L := p.roots.toList
  have hLlen : L.length = b := by simp [L, hcard]
  let r : Fin b → Ω := fun i => L[i.val]'(by omega)
  have hmult : p.roots = (Finset.univ.val.map r) := by
    have h1 : (L : Multiset Ω) = p.roots := Multiset.coe_toList p.roots
    rw [← h1]
    have h2 : L = List.ofFn r := by
      apply List.ext_getElem (by simp [hLlen])
      intro n h1 h2
      simp [r]
    rw [h2, List.ofFn_eq_map]
    change ((List.finRange b).map r : Multiset Ω) = (Finset.univ.val.map r)
    rw [← Multiset.map_coe]
    rfl
  have hp_eq : p = C p.leadingCoeff * ∏ i : Fin b, (X - C (r i)) := by
    have h := hsplits.eq_prod_roots
    rw [hmult, Multiset.map_map] at h
    simpa only [Finset.prod_eq_multiset_prod, Function.comp_apply] using h
  have hrne : ∀ i : Fin b, r i ≠ 0 := by
    intro i hi
    have hmem : r i ∈ p.roots := by
      rw [hmult]
      exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hroot : p.eval 0 = 0 := by
      have hr : p.IsRoot (r i) :=
        (mem_roots (ne_zero_of_natDegree_gt (n := 0) (by omega))).mp hmem
      rwa [IsRoot.def, hi] at hr
    rw [← coeff_zero_eq_eval_zero] at hroot
    exact hp0 hroot
  let c₀ : Ω := p.leadingCoeff * ∏ i : Fin b, (-r i)
  have hc₀ : c₀ ≠ 0 :=
    mul_ne_zero hplc (Finset.prod_ne_zero_iff.mpr fun i _ => neg_ne_zero.mpr (hrne i))
  have hq_eq : p.reflect b = C c₀ * ∏ i : Fin b, (X - C (r i)⁻¹) := by
    conv_lhs => rw [hp_eq]
    rw [reflect_C_mul, reflect_prod_X_sub_C]
    have hfactor : ∀ i : Fin b, (1 - C (r i) * X : Polynomial Ω) = C (-r i) * (X - C (r i)⁻¹) := by
      intro i
      rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ (hrne i)]
      simp only [C_neg, C_1]
      ring
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← C_mul]
  change (p.reflect b).discr = p.discr
  rw [hq_eq, hp_eq, discr_of_prod_linear hb c₀ hc₀ (fun i => (r i)⁻¹),
    discr_of_prod_linear hb p.leadingCoeff hplc r]
  rw [mul_assoc, mul_assoc]
  congr 1
  have hPne : (∏ i : Fin b, r i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hrne i
  have hc₀_pow : c₀ ^ (2 * b - 2) = p.leadingCoeff ^ (2 * b - 2) * (∏ i : Fin b, r i) ^ (2 * b - 2) := by
    dsimp [c₀]
    rw [mul_pow, Finset.prod_neg, mul_pow, ← pow_mul, Finset.card_univ]
    have heven : Even (Fintype.card (Fin b) * (2 * b - 2)) := by
      refine Even.mul_left ?_ _
      exact ⟨b - 1, by omega⟩
    rw [heven.neg_one_pow, one_mul]
  have hdiff_inv :
      (∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, ((r i)⁻¹ - (r j)⁻¹)) =
        ((∏ i : Fin b, r i) ^ (2 * b - 2))⁻¹ *
          (∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (r i - r j)) := by
    have hterm : ∀ i : Fin b, ∀ j ∈ Finset.univ.erase i,
        (r i)⁻¹ - (r j)⁻¹ = (-1) * ((r i)⁻¹ * (r j)⁻¹) * (r i - r j) := by
      intro i j _
      calc (r i)⁻¹ - (r j)⁻¹
          = (r i)⁻¹ * (r j * (r j)⁻¹) - (r i * (r i)⁻¹) * (r j)⁻¹ := by
              rw [mul_inv_cancel₀ (hrne i), mul_inv_cancel₀ (hrne j), mul_one, one_mul]
        _ = (-1) * ((r i)⁻¹ * (r j)⁻¹) * (r i - r j) := by ring
    calc
      (∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, ((r i)⁻¹ - (r j)⁻¹))
          = ∏ i : Fin b, ∏ j ∈ Finset.univ.erase i,
              ((-1 : Ω) * ((r i)⁻¹ * (r j)⁻¹) * (r i - r j)) := by
            refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => hterm i j hj
      _ = (∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (-1 : Ω)) *
            (∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, ((r i)⁻¹ * (r j)⁻¹)) *
            (∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (r i - r j)) := by
            simp_rw [Finset.prod_mul_distrib]
      _ = ((∏ i : Fin b, r i) ^ (2 * b - 2))⁻¹ *
            (∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (r i - r j)) := by
            congr 1
            have hneg : (∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (-1 : Ω)) = 1 := by
              simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                Finset.card_univ, Fintype.card_fin, ← pow_mul]
              rw [Nat.mul_comm]
              exact (Nat.even_mul_pred_self b).neg_one_pow
            rw [hneg, one_mul]
            have hinvprod :
                (∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, ((r i)⁻¹ * (r j)⁻¹)) =
                  (∏ i : Fin b, (r i)⁻¹) ^ (2 * b - 2) := by
              simp_rw [Finset.prod_mul_distrib, Finset.prod_const,
                Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
              have hinner : ∀ i : Fin b,
                  (∏ j ∈ Finset.univ.erase i, (r j)⁻¹) = (∏ j : Fin b, (r j)⁻¹) * r i := by
                intro i
                rw [← Finset.mul_prod_erase Finset.univ (fun j => (r j)⁻¹) (Finset.mem_univ i),
                  mul_comm (r i)⁻¹, mul_assoc, inv_mul_cancel₀ (hrne i), mul_one]
              simp_rw [hinner, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
                Fintype.card_fin]
              rw [Finset.prod_pow, Finset.prod_inv_distrib]
              set P : Ω := ∏ x : Fin b, r x
              have hP : P⁻¹ ^ b * P = P⁻¹ ^ (b - 1) := by
                rw [show b = (b - 1) + 1 by omega, pow_succ, mul_assoc,
                  inv_mul_cancel₀ hPne, mul_one, Nat.add_sub_cancel]
              rw [hP, ← pow_add, show b - 1 + (b - 1) = 2 * b - 2 by omega]
            rw [hinvprod, Finset.prod_inv_distrib, inv_pow]
  rw [hc₀_pow, hdiff_inv]
  have hcancel : (∏ i : Fin b, r i) ^ (2 * b - 2) * ((∏ i : Fin b, r i) ^ (2 * b - 2))⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ hPne)
  linear_combination (p.leadingCoeff ^ (2 * b - 2) *
    ∏ i : Fin b, ∏ j ∈ Finset.univ.erase i, (r i - r j)) * hcancel

end DiscrTransform

/-! ## Section 3: Three-way squarefree factor split of `Δ : K[X][X]` -/

section FactorSplit

private lemma eq_map_C_of_degreeX_eq_zero {K : Type*} [Field K] {p : K[X][X]}
    (h : Bivariate.degreeX p = 0) : p = (p.map (evalRingHom 0)).map C := by
  ext n m
  rw [coeff_map, coeff_map, coeff_C]
  have hn : (p.coeff n).natDegree = 0 :=
    Nat.eq_zero_of_le_zero ((Bivariate.coeff_natDegree_le_degreeX p n).trans h.le)
  have hC := eq_C_of_natDegree_eq_zero hn
  conv_lhs => rw [hC, coeff_C]
  split_ifs with hm
  · subst hm; exact Polynomial.coeff_zero_eq_eval_zero (p.coeff n)
  · rfl

private lemma prod_finset_squarefree_of_normalizedFactors {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] [NormalizedGCDMonoid R] [UniqueFactorizationMonoid R]
    {Δ : R} (s : Finset R)
    (hs : s ⊆ (UniqueFactorizationMonoid.normalizedFactors Δ).toFinset) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_mem : a ∈ UniqueFactorizationMonoid.normalizedFactors Δ :=
      Multiset.mem_toFinset.mp (hs (Finset.mem_insert_self a s))
    have ha_irr : Irreducible a := UniqueFactorizationMonoid.irreducible_of_normalized_factor a ha_mem
    have hs_sub : s ⊆ (UniqueFactorizationMonoid.normalizedFactors Δ).toFinset :=
      (Finset.subset_insert a s).trans hs
    have hsq_s : Squarefree (∏ p ∈ s, p) := ih hs_sub
    rw [squarefree_mul_iff]
    refine ⟨?_, ha_irr.squarefree, hsq_s⟩
    rw [ha_irr.isRelPrime_iff_not_dvd]
    intro hdvd
    have ha_prime : Prime a := ha_irr.prime
    obtain ⟨b, hb, hab⟩ := ha_prime.exists_mem_finset_dvd hdvd
    have hb_mem : b ∈ UniqueFactorizationMonoid.normalizedFactors Δ :=
      Multiset.mem_toFinset.mp (hs_sub hb)
    have hb_irr : Irreducible b := UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb_mem
    have hassoc : Associated a b := ha_irr.associated_of_dvd hb_irr hab
    have heq : a = b :=
      UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated ha_mem hb_mem hassoc
    exact ha (heq ▸ hb)

/-- Three-way squarefree factorization of any nonzero `Δ : K[X][X]` into horizontal `V(Z)`,
vertical `U(X)`, and mixed `H(X, Z)` factors, capturing every prime divisor of `Δ` with `H`
free of horizontal and vertical factors. -/
theorem factor_split {K : Type*} [Field K] (Δ : K[X][X]) (hΔ : Δ ≠ 0) :
    ∃ (V U : K[X]) (H : K[X][X]),
      V ≠ 0 ∧ U ≠ 0 ∧ H ≠ 0 ∧
      Squarefree (V.map C * C U * H) ∧
      V.map C * C U * H ∣ Δ ∧
      (∀ p : K[X][X], Prime p → p ∣ Δ → p ∣ V.map C * C U * H) ∧
      V.natDegree + H.natDegree ≤ Δ.natDegree ∧
      U.natDegree + Bivariate.degreeX H ≤ Bivariate.degreeX Δ ∧
      (∀ p : K[X][X], Prime p → p ∣ H → p.natDegree ≠ 0 ∧ Bivariate.degreeX p ≠ 0) ∧
      (∀ x : K, H.map (evalRingHom x) ≠ 0) ∧
      (∀ z : K, H.eval (C z) ≠ 0) := by
  classical
  let nf := UniqueFactorizationMonoid.normalizedFactors Δ
  let S : Finset K[X][X] := nf.toFinset
  let S_vert := S.filter (fun p => p.natDegree = 0)
  let S_horz := S.filter (fun p => p.natDegree ≠ 0 ∧ Bivariate.degreeX p = 0)
  let S_mix := S.filter (fun p => p.natDegree ≠ 0 ∧ Bivariate.degreeX p ≠ 0)
  let U : K[X] := ∏ p ∈ S_vert, p.coeff 0
  let V : K[X] := ∏ p ∈ S_horz, p.map (evalRingHom 0)
  let H : K[X][X] := ∏ p ∈ S_mix, p
  have hCU : C U = ∏ p ∈ S_vert, p := by
    dsimp [U]
    rw [map_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    exact (eq_C_of_natDegree_eq_zero (Finset.mem_filter.mp hp).2).symm
  have hVC : V.map C = ∏ p ∈ S_horz, p := by
    dsimp [V]
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    exact (eq_map_C_of_degreeX_eq_zero (Finset.mem_filter.mp hp).2.2).symm
  have hdisj1 : Disjoint S_horz S_vert := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact (Finset.mem_filter.mp hp1).2.1 (Finset.mem_filter.mp hp2).2
  have hdisj2 : Disjoint (S_horz ∪ S_vert) S_mix := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rcases Finset.mem_union.mp hp1 with h | h
    · exact (Finset.mem_filter.mp hp2).2.2 (Finset.mem_filter.mp h).2.2
    · exact (Finset.mem_filter.mp hp2).2.1 (Finset.mem_filter.mp h).2
  have hunion : S_horz ∪ S_vert ∪ S_mix = S := by
    ext p
    simp only [S_horz, S_vert, S_mix, Finset.mem_union, Finset.mem_filter]
    tauto
  have hprod_eq : V.map C * C U * H = ∏ p ∈ S, p := by
    rw [hVC, hCU, ← Finset.prod_union hdisj1, ← Finset.prod_union hdisj2, hunion]
  have hsq : Squarefree (V.map C * C U * H) := by
    rw [hprod_eq]
    exact prod_finset_squarefree_of_normalizedFactors S Subset.rfl
  have hdvd : V.map C * C U * H ∣ Δ := by
    rw [hprod_eq]
    have hle : S.val ≤ nf := Multiset.dedup_le nf
    have hprod_dvd : S.val.prod ∣ nf.prod := Multiset.prod_dvd_prod_of_le hle
    have hfin : (∏ p ∈ S, p) = S.val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hfin]
    exact hprod_dvd.trans (UniqueFactorizationMonoid.prod_normalizedFactors hΔ).dvd
  have hP0 : V.map C * C U * H ≠ 0 := hsq.ne_zero
  have hVC0 : V.map C ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hP0)
  have hCU0 : C U ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hP0)
  have hV0 : V ≠ 0 := fun h => hVC0 (by simp [h])
  have hU0 : U ≠ 0 := fun h => hCU0 (by simp [h])
  have hH0 : H ≠ 0 := right_ne_zero_of_mul hP0
  have hrad : ∀ p : K[X][X], Prime p → p ∣ Δ → p ∣ V.map C * C U * H := by
    intro p hp hd
    rw [hprod_eq]
    obtain ⟨q, hq, hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hΔ hp.irreducible hd
    exact hassoc.dvd.trans (Finset.dvd_prod_of_mem _ (Multiset.mem_toFinset.mpr hq))
  have hdegZ : V.natDegree + H.natDegree ≤ Δ.natDegree := by
    have h1 := natDegree_le_of_dvd hdvd hΔ
    rw [natDegree_mul (mul_ne_zero hVC0 hCU0) hH0, natDegree_mul hVC0 hCU0, natDegree_C, add_zero,
      natDegree_map_eq_of_injective C_injective] at h1
    exact h1
  have hdegX : U.natDegree + Bivariate.degreeX H ≤ Bivariate.degreeX Δ := by
    have h1 : Bivariate.degreeX (V.map C * C U * H) ≤ Bivariate.degreeX Δ := by
      have hd' : Bivariate.swap (V.map C * C U * H) ∣ Bivariate.swap Δ :=
        map_dvd Bivariate.swap.toRingHom hdvd
      have hΔ' : Bivariate.swap Δ ≠ 0 :=
        (map_ne_zero_iff _ Bivariate.swap.injective).mpr hΔ
      simpa only [natDegree_swap_eq_degreeX] using natDegree_le_of_dvd hd' hΔ'
    rw [Bivariate.degreeX_mul _ _ (mul_ne_zero hVC0 hCU0) hH0,
      Bivariate.degreeX_mul _ _ hVC0 hCU0] at h1
    have hCUX : Bivariate.degreeX (C U) = U.natDegree := by
      simp [Bivariate.degreeX, Polynomial.support_C hU0]
    rw [hCUX] at h1
    omega
  have hH_prim : ∀ p : K[X][X], Prime p → p ∣ H → p.natDegree ≠ 0 ∧ Bivariate.degreeX p ≠ 0 := by
    intro p hp hd
    obtain ⟨q, hq, hpq⟩ := hp.exists_mem_finset_dvd hd
    have hq_mem : q ∈ nf := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    have hq_irr : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq_mem
    have hassoc : Associated p q := hp.irreducible.associated_of_dvd hq_irr hpq
    obtain ⟨u, hu⟩ := hassoc
    have hu0 : (u : K[X][X]) ≠ 0 := u.ne_zero
    have huZ : (u : K[X][X]).natDegree = 0 := natDegree_eq_zero_of_isUnit u.isUnit
    have huX : Bivariate.degreeX (u : K[X][X]) = 0 := by
      have := natDegree_eq_zero_of_isUnit (u.isUnit.map Bivariate.swap.toRingHom)
      exact (natDegree_swap_eq_degreeX (u : K[X][X])).symm.trans this
    have hpZ : p.natDegree = q.natDegree := by
      rw [← hu, natDegree_mul hp.ne_zero hu0, huZ, add_zero]
    have hpX : Bivariate.degreeX p = Bivariate.degreeX q := by
      rw [← hu, Bivariate.degreeX_mul _ _ hp.ne_zero hu0, huX, add_zero]
    rw [hpZ, hpX]
    exact (Finset.mem_filter.mp hq).2
  have hH_no_vert : ∀ x : K, H.map (evalRingHom x) ≠ 0 := by
    intro x hx
    have hdvd_x : C (X - C x) ∣ H := by
      rw [C_dvd_iff_dvd_coeff]
      intro j
      have h0 := congrArg (fun p : K[X] => p.coeff j) hx
      rw [coeff_map, coeff_zero] at h0
      exact dvd_iff_isRoot.mpr h0
    have hpx : Prime (C (X - C x) : K[X][X]) :=
      Polynomial.prime_C_iff.mpr (irreducible_X_sub_C x).prime
    exact (hH_prim _ hpx hdvd_x).1 (natDegree_C _)
  have hH_no_horz : ∀ z : K, H.eval (C z) ≠ 0 := by
    intro z hz
    have hdvd_z : (X - C (C z) : K[X][X]) ∣ H := dvd_iff_isRoot.mpr hz
    have hpz : Prime (X - C (C z) : K[X][X]) := (irreducible_X_sub_C (C z)).prime
    have hdegX_z : Bivariate.degreeX (X - C (C z) : K[X][X]) = 0 := by
      rw [show (X - C (C z) : K[X][X]) = (X - C z).map C by simp]
      unfold Bivariate.degreeX
      apply Nat.eq_zero_of_le_zero
      refine Finset.sup_le fun j _ => ?_
      rw [coeff_map, natDegree_C]
    exact (hH_prim _ hpz hdvd_z).2 hdegX_z
  exact ⟨V, U, H, hV0, hU0, hH0, hsq, hdvd, hrad, hdegZ, hdegX, hH_prim, hH_no_vert, hH_no_horz⟩

end FactorSplit

/-! ## Section 4: Plane branch DVR bounds and unramifiedness off `F.discr` -/

section BranchDVR

open NormalizedSectionSpecialization HeightOneNormalization IsDedekindDomain

attribute [local instance high] Algebra.toSMul

variable {R L : Type*} [CommRing R] [IsDomain R] [Field L] [Algebra R L] [IsFractionRing R L]

private noncomputable abbrev polynomialFractionAlgebra (k : Type*) [Field k] :
    Algebra k[X] (FractionRing k[X]) := inferInstance

local instance planeFractionAlgebra : Algebra R[X] (FractionRing L[X]) :=
  (genericCoeffs (R := R) (L := L)).toAlgebra

omit [IsDomain R] in
private theorem planeFraction : IsFractionRing R[X] (FractionRing L[X]) := by
  let : Algebra R[X] L[X] := Polynomial.algebra R L
  let : Algebra L[X] (FractionRing L[X]) := polynomialFractionAlgebra L
  let : Algebra R[X] (FractionRing L[X]) := planeFractionAlgebra
  let : IsScalarTower R[X] L[X] (FractionRing L[X]) := IsScalarTower.of_algebraMap_eq' rfl
  let M := (nonZeroDivisors R).map (Polynomial.C : R →+* R[X])
  let : IsLocalization M L[X] := Polynomial.isLocalization _ _
  have hi : Function.Injective (algebraMap R[X] L[X]) :=
    Polynomial.map_injective _ (IsFractionRing.injective R L)
  have hm : (nonZeroDivisors L[X]).comap (algebraMap R[X] L[X]) = nonZeroDivisors R[X] :=
    le_antisymm (comap_nonZeroDivisors_le_of_injective hi)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hi)
  rw [IsFractionRing, ← hm]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (nonZeroDivisors L[X]) _ fun _ h ↦ h.mem_nonZeroDivisors

attribute [local instance] planeFraction

local instance curveFinite (F : R[X][X]) [h : Fact (Irreducible
    (F.map (genericCoeffs (R := R) (L := L))))] :
    FiniteDimensional (FractionRing L[X]) (Curve (L := L) F) :=
  (AdjoinRoot.powerBasis h.out.ne_zero).finite

/-- The branch DVR `branchRing hp w` viewed as a `Subring` of `Curve F`. -/
def branchSubring {F : R[X][X]}
    [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    Subring (Curve (L := L) F) where
  carrier := (branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w : Set _)
  one_mem' := (branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w).one_mem
  mul_mem' ha hb := (branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w).mul_mem ha hb
  zero_mem' := (branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w).zero_mem
  add_mem' ha hb := (branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w).add_mem ha hb
  neg_mem' {a} ha := by
    rw [← neg_one_mul]
    have hneg1 : (-1 : Curve (L := L) F) ∈
        branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w := by
      simpa using (branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w).algebraMap_mem (-1)
    exact (branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w).mul_mem hneg1 ha

/-- Ring equivalence identifying `branchRing hp w` and `branchSubring hp w`. -/
def branchSubringEquiv {F : R[X][X]}
    [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w ≃+*
      branchSubring (R := R) (L := L) (F := F) hp w where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Canonical inclusion of the base DVR `localBase` into the branch DVR `branchSubring`. -/
def baseToBranch {F : R[X][X]}
    [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    localBase (FractionRing L[X]) hp →+* branchSubring (R := R) (L := L) (F := F) hp w where
  toFun r := ⟨algebraMap (FractionRing L[X]) (Curve (L := L) F) r.1, by
    change algebraMap (FractionRing L[X]) (Curve (L := L) F) r.1 ∈
      branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w
    exact (branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w).algebraMap_mem
      ⟨algebraMap (FractionRing L[X]) (Curve (L := L) F) r.1, isIntegral_algebraMap⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/-- Canonical inclusion of `localNormalization` into `branchSubring`. -/
def normToBranch {F : R[X][X]}
    [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp →+*
      branchSubring (R := R) (L := L) (F := F) hp w where
  toFun c := ⟨c.1, (branchRing (K := FractionRing L[X]) (E := Curve (L := L) F) hp w).algebraMap_mem c⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Embed the base DVR `localBase (FractionRing L[X]) hp` as a subring of the branch DVR
`branchSubring hp w`. -/
def baseSubring {F : R[X][X]}
    [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    Subring (branchSubring (R := R) (L := L) (F := F) hp w) :=
  (baseToBranch (R := R) (L := L) (F := F) hp w).range

/-- The natural ring equivalence between `localBase` and `baseSubring` inside `branchSubring`. -/
def baseEquiv {F : R[X][X]}
    [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    localBase (FractionRing L[X]) hp ≃+* baseSubring (R := R) (L := L) (F := F) hp w :=
  RingEquiv.ofBijective (baseToBranch (R := R) (L := L) (F := F) hp w).rangeRestrict
    ⟨fun a b h => by
      have hE : algebraMap (FractionRing L[X]) (Curve (L := L) F) a.1 =
          algebraMap (FractionRing L[X]) (Curve (L := L) F) b.1 :=
        congrArg (fun x : baseSubring (R := R) (L := L) (F := F) hp w => (x.1 : Curve (L := L) F)) h
      exact Subtype.ext ((algebraMap (FractionRing L[X]) (Curve (L := L) F)).injective hE),
      (baseToBranch (R := R) (L := L) (F := F) hp w).rangeRestrict_surjective⟩

private lemma baseEquiv_coe {F : R[X][X]}
    [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp))
    (r₀ : localBase (FractionRing L[X]) hp) :
    (baseEquiv (R := R) (L := L) (F := F) hp w r₀ :
      branchSubring (R := R) (L := L) (F := F) hp w) =
    baseToBranch (R := R) (L := L) (F := F) hp w r₀ := rfl

private lemma dvr_maximalIdeal_ne_bot (R₀ : Type*) [CommRing R₀] [IsDomain R₀]
    [IsDiscreteValuationRing R₀] :
    IsLocalRing.maximalIdeal R₀ ≠ ⊥ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  exact Ideal.span_singleton_eq_bot.not.mpr hϖ.ne_zero

private lemma dvr_ramification_inertia_le
    (R₀ KF O E : Type*) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Field KF] [Algebra R₀ KF] [IsFractionRing R₀ KF]
    [Field E] [Algebra KF E] [Algebra R₀ E] [IsScalarTower R₀ KF E]
    [CommRing O] [Algebra R₀ O] [Algebra O E] [IsScalarTower R₀ O E]
    [Algebra.IsIntegral R₀ O] [IsDedekindDomain O] [IsFractionRing O E]
    [Module.Finite R₀ O] (w : HeightOneSpectrum O) :
    w.asIdeal.under R₀ = IsLocalRing.maximalIdeal R₀ ∧
    w.asIdeal.LiesOver (IsLocalRing.maximalIdeal R₀) ∧
    0 < w.asIdeal.ramificationIdx R₀ ∧
    w.asIdeal.ramificationIdx R₀ ≤ Module.finrank KF E ∧
    0 < w.asIdeal.inertiaDeg R₀ ∧
    w.asIdeal.inertiaDeg R₀ ≤ Module.finrank KF E := by
  have : FaithfulSMul R₀ O := FaithfulSMul.of_field_isFractionRing R₀ O KF E
  have hw_under_ne : w.asIdeal.under R₀ ≠ ⊥ := Ideal.IsIntegral.under_ne_bot R₀ w.ne_bot
  have hw_under_prime : (w.asIdeal.under R₀).IsPrime := Ideal.IsPrime.under R₀ w.asIdeal
  have hw_under : w.asIdeal.under R₀ = IsLocalRing.maximalIdeal R₀ :=
    IsLocalRing.eq_maximalIdeal (hw_under_prime.isMaximal hw_under_ne)
  have hw_lies : w.asIdeal.LiesOver (IsLocalRing.maximalIdeal R₀) := ⟨hw_under.symm⟩
  have htf : Module.IsTorsionFree R₀ O := by
    refine ⟨fun r hr x y hxy => ?_⟩
    have hr0 : r ≠ 0 := fun hz => one_ne_zero (hr.1 (by simp [hz]))
    have hne : algebraMap R₀ O r ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R₀ O)).mpr hr0
    exact mul_left_cancel₀ hne (by simpa only [Algebra.smul_def] using hxy)
  have : Module.Free R₀ O := Module.free_of_finite_type_torsion_free'
  have hfinRC : Module.finrank R₀ O = Module.finrank KF E :=
    (IsFractionRing.finrank_eq R₀ KF O E).symm
  have hm0 : IsLocalRing.maximalIdeal R₀ ≠ ⊥ := dvr_maximalIdeal_ne_bot R₀
  have hm_map_ne : (IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ O) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (IsLocalRing.maximalIdeal R₀) O
  rw [hfinRC] at hsum
  let w_over : (IsLocalRing.maximalIdeal R₀).primesOver O := ⟨w.asIdeal, w.isPrime, hw_lies⟩
  have hw_le : w.asIdeal.ramificationIdx R₀ * w.asIdeal.inertiaDeg R₀ ≤ Module.finrank KF E := by
    rw [← hsum]
    exact Finset.single_le_sum
      (f := fun q : (IsLocalRing.maximalIdeal R₀).primesOver O =>
        q.1.ramificationIdx R₀ * q.1.inertiaDeg R₀)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w_over)
  have he_pos : 0 < w.asIdeal.ramificationIdx R₀ :=
    Ideal.ramificationIdx_pos_of_isDedekindDomain w.asIdeal hm_map_ne
  have hf_pos : 0 < w.asIdeal.inertiaDeg R₀ := Ideal.inertiaDeg_pos w.asIdeal R₀
  exact ⟨hw_under, hw_lies, he_pos, (Nat.le_mul_of_pos_right _ hf_pos).trans hw_le,
    hf_pos, (Nat.le_mul_of_pos_left _ he_pos).trans hw_le⟩

private lemma dvr_base_map_eq_maximalIdeal_pow
    (R₀ O B : Type*) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [CommRing O] [IsDedekindDomain O] [Algebra R₀ O] [FaithfulSMul R₀ O]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra O B] [Algebra R₀ B] [IsScalarTower R₀ O B]
    (w : HeightOneSpectrum O) [IsLocalization.AtPrime B w.asIdeal]
    (hw_lies : w.asIdeal.LiesOver (IsLocalRing.maximalIdeal R₀)) :
    (IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ B) =
      (IsLocalRing.maximalIdeal B) ^ (w.asIdeal.ramificationIdx R₀) := by
  have hm0 : IsLocalRing.maximalIdeal R₀ ≠ ⊥ := dvr_maximalIdeal_ne_bot R₀
  have hm_map_ne : (IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ O) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  obtain ⟨I, hwI, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hm_map_ne w.asIdeal
  have hnot : ¬ I ≤ w.asIdeal := by
    intro hle
    rw [sup_of_le_left hle] at hwI
    exact w.isPrime.ne_top hwI
  have hram : (UniqueFactorizationMonoid.normalizedFactors
      ((IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ O))).count w.asIdeal =
      w.asIdeal.ramificationIdx R₀ :=
    (Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hm_map_ne).symm
  rw [hram] at hfac
  have hmapB := congrArg (Ideal.map (algebraMap O B)) hfac
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R₀ O B, Ideal.map_mul, Ideal.map_pow,
    IsLocalization.AtPrime.map_eq_top_of_not_le (S := B) hnot, Ideal.mul_top,
    IsLocalization.AtPrime.map_eq_maximalIdeal w.asIdeal B] at hmapB
  exact hmapB

private lemma dvr_residue_finrank_eq
    (R₀ O B Rloc : Type*) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [CommRing O] [IsDedekindDomain O] [Algebra R₀ O] [Module.Finite R₀ O]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra O B] [Algebra R₀ B] [IsScalarTower R₀ O B]
    [CommRing Rloc] [IsLocalRing Rloc] [Algebra Rloc B] [IsLocalHom (algebraMap Rloc B)]
    (w : HeightOneSpectrum O) [IsLocalization.AtPrime B w.asIdeal]
    (hw_lies : w.asIdeal.LiesOver (IsLocalRing.maximalIdeal R₀))
    (hRe : R₀ ≃+* Rloc)
    (hcompat : ∀ r : R₀, algebraMap Rloc B (hRe r) = algebraMap R₀ B r) :
    Module.finrank (IsLocalRing.ResidueField Rloc) (IsLocalRing.ResidueField B) =
      w.asIdeal.inertiaDeg R₀ := by
  have : IsLocalization.AtPrime R₀ (IsLocalRing.maximalIdeal R₀) :=
    IsLocalization.self (M := (IsLocalRing.maximalIdeal R₀).primeCompl)
      (fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx)
  let eR₀ : Localization.AtPrime (IsLocalRing.maximalIdeal R₀) ≃ₐ[R₀] R₀ :=
    IsLocalization.algEquiv (IsLocalRing.maximalIdeal R₀).primeCompl _ R₀
  let fR : Localization.AtPrime (IsLocalRing.maximalIdeal R₀) ≃+* Rloc := eR₀.toRingEquiv.trans hRe
  have : IsLocalHom fR.toRingHom :=
    ⟨fun x hx => by simpa using hx.map fR.symm.toRingHom⟩
  let eR : (IsLocalRing.maximalIdeal R₀).ResidueField ≃+* IsLocalRing.ResidueField Rloc :=
    IsLocalRing.ResidueField.mapEquiv fR
  let eB₀ : Localization.AtPrime w.asIdeal ≃ₐ[O] B :=
    IsLocalization.algEquiv w.asIdeal.primeCompl _ B
  have : IsLocalHom eB₀.toRingEquiv.toRingHom :=
    ⟨fun x hx => by simpa using hx.map eB₀.toRingEquiv.symm.toRingHom⟩
  let eB : w.asIdeal.ResidueField ≃+* IsLocalRing.ResidueField B :=
    IsLocalRing.ResidueField.mapEquiv eB₀.toRingEquiv
  let _ : Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal R₀))
      (Localization.AtPrime w.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (IsLocalRing.maximalIdeal R₀) w.asIdeal
  have hinertia : w.asIdeal.inertiaDeg R₀ =
      Module.finrank (IsLocalRing.maximalIdeal R₀).ResidueField w.asIdeal.ResidueField :=
    Ideal.inertiaDeg_eq (IsLocalRing.maximalIdeal R₀) w.asIdeal
  have hcomm : (algebraMap (IsLocalRing.ResidueField Rloc) (IsLocalRing.ResidueField B)).comp
      eR.toRingHom =
      eB.toRingHom.comp
        (algebraMap (IsLocalRing.maximalIdeal R₀).ResidueField w.asIdeal.ResidueField) := by
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    have hL : eR (algebraMap R₀ (IsLocalRing.maximalIdeal R₀).ResidueField x) =
        IsLocalRing.residue Rloc (hRe x) := by
      rw [IsScalarTower.algebraMap_apply R₀ (Localization.AtPrime (IsLocalRing.maximalIdeal R₀))]
      change IsLocalRing.ResidueField.map fR.toRingHom
        (IsLocalRing.residue _ (algebraMap R₀ _ x)) = _
      rw [IsLocalRing.ResidueField.map_residue]
      simp [fR, eR₀.commutes x]
    have hR : algebraMap (IsLocalRing.maximalIdeal R₀).ResidueField w.asIdeal.ResidueField
        (algebraMap R₀ (IsLocalRing.maximalIdeal R₀).ResidueField x) =
        IsLocalRing.residue _ (algebraMap O (Localization.AtPrime w.asIdeal) (algebraMap R₀ O x)) := by
      rw [← IsScalarTower.algebraMap_apply R₀ (IsLocalRing.maximalIdeal R₀).ResidueField
        w.asIdeal.ResidueField,
        IsScalarTower.algebraMap_apply R₀ O w.asIdeal.ResidueField,
        IsScalarTower.algebraMap_apply O (Localization.AtPrime w.asIdeal) w.asIdeal.ResidueField]
      rfl
    rw [hL, hR]
    change IsLocalRing.ResidueField.map (algebraMap Rloc B) (IsLocalRing.residue Rloc (hRe x)) =
      IsLocalRing.ResidueField.map eB₀.toRingEquiv.toRingHom
        (IsLocalRing.residue _ (algebraMap O _ (algebraMap R₀ O x)))
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue]
    simp [eB₀.commutes, hcompat x, IsScalarTower.algebraMap_apply R₀ O B]
  rw [hinertia]
  exact (Algebra.finrank_eq_of_equiv_equiv eR eB hcomm).symm

private lemma dvr_ramificationIdx_eq_one_of_monic_unit_discr
    (R₀ KF O E : Type*) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Field KF] [Algebra R₀ KF] [IsFractionRing R₀ KF]
    [Field E] [Algebra KF E] [Algebra R₀ E] [IsScalarTower R₀ KF E]
    [FiniteDimensional KF E] [Algebra.IsSeparable KF E]
    [CommRing O] [Algebra R₀ O] [Algebra O E] [IsScalarTower R₀ O E]
    [IsIntegralClosure O R₀ E] [IsDedekindDomain O] [IsFractionRing O E]
    [Algebra.IsIntegral R₀ O] [Module.Finite R₀ O]
    (G : R₀[X]) (hGmonic : G.Monic) (hb : 2 ≤ G.natDegree)
    (hGdeg : G.natDegree = Module.finrank KF E) (hGdiscr : IsUnit G.discr)
    (T : E) (hT_root : aeval T G = 0)
    (hT_gen : Algebra.adjoin KF ({T} : Set E) = ⊤)
    (w : HeightOneSpectrum O) :
    w.asIdeal.LiesOver (IsLocalRing.maximalIdeal R₀) ∧ w.asIdeal.ramificationIdx R₀ = 1 := by
  have : FaithfulSMul R₀ O := FaithfulSMul.of_field_isFractionRing R₀ O KF E
  have htf : Module.IsTorsionFree R₀ O := by
    refine ⟨fun r hr x y hxy => ?_⟩
    have hr0 : r ≠ 0 := fun hz => one_ne_zero (hr.1 (by simp [hz]))
    have hne : algebraMap R₀ O r ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R₀ O)).mpr hr0
    exact mul_left_cancel₀ hne (by simpa only [Algebra.smul_def] using hxy)
  obtain ⟨t, htE⟩ := IsIntegralClosure.isIntegral_iff (A := O) (R := R₀) (B := E) |>.mp
    ⟨G, hGmonic, hT_root⟩
  have hT_root' : aeval (algebraMap O E t) G = 0 := htE ▸ hT_root
  have hT_gen' : Algebra.adjoin KF ({algebraMap O E t} : Set E) = ⊤ := htE ▸ hT_gen
  have hTint : IsIntegral KF T := Algebra.IsIntegral.isIntegral (R := KF) T
  have hminK_deg : (minpoly KF T).natDegree = G.natDegree := by
    have htop : IntermediateField.adjoin KF ({T} : Set E) = ⊤ := by
      rw [IntermediateField.adjoin_eq_top_iff]
      exact hT_gen
    have h1 := IntermediateField.adjoin.finrank hTint
    rw [htop, IntermediateField.finrank_top'] at h1
    omega
  have hGK_monic : (G.map (algebraMap R₀ KF)).Monic := hGmonic.map _
  have hGK_deg : (G.map (algebraMap R₀ KF)).natDegree = G.natDegree := hGmonic.natDegree_map _
  have hdvdK : minpoly KF T ∣ G.map (algebraMap R₀ KF) :=
    minpoly.dvd KF T (by simpa [aeval_map_algebraMap] using hT_root)
  have hminK_eq : minpoly KF T = G.map (algebraMap R₀ KF) := by
    obtain ⟨q, hq⟩ := hdvdK
    have hq0 : q ≠ 0 := fun hz => hGK_monic.ne_zero (by rw [hq, hz, mul_zero])
    have hqdeg : q.natDegree = 0 := by
      have := congrArg Polynomial.natDegree hq
      rw [hGK_deg, natDegree_mul (minpoly.ne_zero hTint) hq0, hminK_deg] at this
      omega
    have hqmon : q.Monic := by
      have hlc := congrArg Polynomial.leadingCoeff hq
      rw [hGK_monic.leadingCoeff, leadingCoeff_mul, (minpoly.monic hTint).leadingCoeff,
        one_mul] at hlc
      exact hlc.symm
    have hq1 : q = 1 := eq_one_of_monic_natDegree_zero hqmon hqdeg
    rw [hq, hq1, mul_one]
  have hmin_eq : minpoly R₀ t = G := by
    have ht_int : IsIntegral R₀ t := Algebra.IsIntegral.isIntegral t
    have hmin_map : (minpoly R₀ t).map (algebraMap R₀ KF) = G.map (algebraMap R₀ KF) := by
      rw [← hminK_eq, ← htE]
      exact (minpoly.isIntegrallyClosed_eq_field_fractions KF E ht_int).symm
    exact Polynomial.map_injective _ (IsFractionRing.injective R₀ KF) hmin_map
  have hres_unit : IsUnit (resultant G G.derivative G.natDegree (G.natDegree - 1)) := by
    have hpos : 0 < G.degree := natDegree_pos_iff_degree_pos.mp (by omega)
    rw [Polynomial.resultant_deriv hpos, hGmonic.leadingCoeff, mul_one]
    exact (isUnit_neg_one.pow _).mul hGdiscr
  obtain ⟨P, Q, _, _, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    (m := G.natDegree) (n := G.natDegree - 1) G G.derivative le_rfl
    (natDegree_derivative_le G) (by omega)
  have ht_root : aeval t G = 0 := by
    apply IsFractionRing.injective O E
    rw [← aeval_algebraMap_apply, map_zero]
    exact hT_root'
  obtain ⟨u_res, hu_res⟩ := hres_unit
  have hGder_unit : IsUnit (aeval t G.derivative) := by
    have hev := congrArg (aeval t) hbez
    rw [map_add, map_mul, map_mul, ht_root, zero_mul, zero_add, aeval_C, ← hu_res] at hev
    refine isUnit_iff_exists_inv.mpr ⟨aeval t Q * algebraMap R₀ O (↑u_res⁻¹ : R₀), ?_⟩
    calc aeval t G.derivative * (aeval t Q * algebraMap R₀ O (↑u_res⁻¹ : R₀))
        = (aeval t G.derivative * aeval t Q) * algebraMap R₀ O (↑u_res⁻¹ : R₀) :=
            (mul_assoc _ _ _).symm
      _ = algebraMap R₀ O (u_res : R₀) * algebraMap R₀ O (↑u_res⁻¹ : R₀) := by rw [hev]
      _ = algebraMap R₀ O ((u_res : R₀) * (↑u_res⁻¹ : R₀)) := (map_mul _ _ _).symm
      _ = 1 := by rw [Units.mul_inv, map_one]
  have hmem_diff : aeval t (minpoly R₀ t).derivative ∈ differentIdeal R₀ O :=
    aeval_derivative_mem_differentIdeal R₀ KF E t hT_gen'
  rw [hmin_eq] at hmem_diff
  have hdiff_top : differentIdeal R₀ O = ⊤ := Ideal.eq_top_of_isUnit_mem _ hmem_diff hGder_unit
  have hm0 : IsLocalRing.maximalIdeal R₀ ≠ ⊥ := dvr_maximalIdeal_ne_bot R₀
  have hm_map_ne : (IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ O) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hw_under_ne : w.asIdeal.under R₀ ≠ ⊥ := Ideal.IsIntegral.under_ne_bot R₀ w.ne_bot
  have hw_under_prime : (w.asIdeal.under R₀).IsPrime := Ideal.IsPrime.under R₀ w.asIdeal
  have hw_lies : w.asIdeal.LiesOver (IsLocalRing.maximalIdeal R₀) :=
    ⟨(IsLocalRing.eq_maximalIdeal (hw_under_prime.isMaximal hw_under_ne)).symm⟩
  obtain ⟨I, _, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hm_map_ne w.asIdeal
  set e := (UniqueFactorizationMonoid.normalizedFactors
    ((IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ O))).count w.asIdeal
  have he_eq : e = w.asIdeal.ramificationIdx R₀ :=
    (Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hm_map_ne).symm
  have he_pos : 0 < e := he_eq ▸ Ideal.ramificationIdx_pos_of_isDedekindDomain w.asIdeal hm_map_ne
  have hdiff_dvd := pow_sub_one_dvd_differentIdeal_aux R₀ KF E w.asIdeal he_pos.ne' hm0 ⟨I, hfac⟩
  rw [hdiff_top] at hdiff_dvd
  refine ⟨hw_lies, ?_⟩
  rw [← he_eq]
  by_contra hne
  have hge : 1 ≤ e - 1 := by omega
  have hw_dvd_top : w.asIdeal ∣ (⊤ : Ideal O) :=
    (pow_one w.asIdeal ▸ pow_dvd_pow w.asIdeal hge).trans hdiff_dvd
  exact w.isPrime.ne_top (eq_top_iff.mpr (Ideal.dvd_iff_le.mp hw_dvd_top))

private lemma branchSubring_isLocalization [IsNoetherianRing R]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    [Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F)]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    let _ := (normToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
    IsLocalization.AtPrime (branchSubring (R := R) (L := L) (F := F) hp w) w.asIdeal := by
  let KF := FractionRing L[X]
  let E := Curve (L := L) F
  let R₀ := localBase KF hp
  let O := localNormalization (K := KF) E hp
  let Bsub := HeightOneNormalization.branchRing (K := KF) (E := E) hp w
  let B : Subring E := branchSubring (R := R) (L := L) (F := F) hp w
  have : IsDiscreteValuationRing R₀ := localBase_dvr hp
  have : IsFractionRing R₀ KF := Localization.subalgebra.isFractionRing_ofField ..
  have : IsFractionRing O E := IsIntegralClosure.isFractionRing_of_finite_extension R₀ KF E O
  let _ : Algebra O B := (normToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
  have : IsLocalization.AtPrime Bsub w.asIdeal :=
    Localization.subalgebra.isLocalization_ofField E w.asIdeal.primeCompl
      w.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsLocalization.isLocalization_of_algEquiv w.asIdeal.primeCompl
    ({ branchSubringEquiv (R := R) (L := L) (F := F) hp w with commutes' := fun _ => rfl } :
      Bsub ≃ₐ[O] B)

private lemma branchSubring_dvr [IsNoetherianRing R]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    [Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F)]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    IsDiscreteValuationRing (branchSubring (R := R) (L := L) (F := F) hp w) ∧
    IsFractionRing (branchSubring (R := R) (L := L) (F := F) hp w) (Curve (L := L) F) := by
  let KF := FractionRing L[X]
  let E := Curve (L := L) F
  let R₀ := localBase KF hp
  let O := localNormalization (K := KF) E hp
  let Bsub := HeightOneNormalization.branchRing (K := KF) (E := E) hp w
  let B : Subring E := branchSubring (R := R) (L := L) (F := F) hp w
  have : IsDiscreteValuationRing R₀ := localBase_dvr hp
  have : IsFractionRing R₀ KF := Localization.subalgebra.isFractionRing_ofField ..
  have : IsDedekindDomain O := integralClosure.isDedekindDomain R₀ KF E
  have : IsFractionRing O E := IsIntegralClosure.isFractionRing_of_finite_extension R₀ KF E O
  let _ : Algebra O B := (normToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
  have : IsLocalization.AtPrime B w.asIdeal := branchSubring_isLocalization F hp w
  refine ⟨IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O w.ne_bot B, ?_⟩
  have hBsub_frac : IsFractionRing Bsub E := (branchRing_dvr (K := KF) (E := E) hp w).2
  constructor; constructor
  · rintro ⟨x, hx⟩
    exact isUnit_iff_ne_zero.mpr (fun h => nonZeroDivisors.ne_zero hx (Subtype.ext h))
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj (nonZeroDivisors Bsub) y
    refine ⟨⟨branchSubringEquiv (R := R) (L := L) (F := F) hp w x,
      ⟨branchSubringEquiv (R := R) (L := L) (F := F) hp w s.1, ?_⟩⟩, e⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact (map_ne_zero_iff _ (branchSubringEquiv (R := R) (L := L) (F := F) hp w).injective).mpr
      (nonZeroDivisors.ne_zero s.2)
  · intro x y h
    exact ⟨1, by simpa using Subtype.ext h⟩

omit [IsDomain R] in
private lemma curve_finrank_eq_natDegree (F : R[X][X])
    [hIrr : Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))] :
    Module.finrank (FractionRing L[X]) (Curve (L := L) F) = F.natDegree := by
  let hpb := AdjoinRoot.powerBasis hIrr.out.ne_zero
  rw [hpb.finrank, AdjoinRoot.powerBasis_dim]
  change (F.map (algebraMap R[X] (FractionRing L[X]))).natDegree = F.natDegree
  exact natDegree_map_eq_of_injective (IsFractionRing.injective R[X] (FractionRing L[X])) F

private lemma branch_localHom [IsNoetherianRing R]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    [Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F)]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp))
    (hw_under : ∀ r₀ : localBase (FractionRing L[X]) hp, ¬ IsUnit r₀ →
      algebraMap (localBase (FractionRing L[X]) hp)
        (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp) r₀ ∈ w.asIdeal) :
    let B := branchSubring (R := R) (L := L) (F := F) hp w
    let Rloc := baseSubring (R := R) (L := L) (F := F) hp w
    IsLocalHom (algebraMap Rloc B) := by
  let KF := FractionRing L[X]
  let E := Curve (L := L) F
  let R₀ := localBase KF hp
  let O := localNormalization (K := KF) E hp
  let B : Subring E := branchSubring (R := R) (L := L) (F := F) hp w
  let Rloc : Subring B := baseSubring (R := R) (L := L) (F := F) hp w
  have : IsDiscreteValuationRing R₀ := localBase_dvr hp
  have : IsDiscreteValuationRing B := (branchSubring_dvr F hp w).1
  let _ : Algebra O B := (normToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
  have : IsLocalization.AtPrime B w.asIdeal := branchSubring_isLocalization F hp w
  let hRe : R₀ ≃+* Rloc := baseEquiv (R := R) (L := L) (F := F) hp w
  constructor
  intro r hr
  obtain ⟨r₀, rfl⟩ := hRe.surjective r
  by_contra hnot
  have hnot₀ : ¬ IsUnit r₀ := fun hu => hnot (hu.map hRe.toRingHom)
  have hrc : algebraMap R₀ O r₀ ∈ w.asIdeal := hw_under r₀ hnot₀
  have hmemB : algebraMap Rloc B (hRe r₀) ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal w.asIdeal B]
    have heq : algebraMap Rloc B (hRe r₀) = algebraMap O B (algebraMap R₀ O r₀) := Subtype.ext rfl
    rw [heq]
    exact Ideal.mem_map_of_mem (algebraMap O B) hrc
  exact IsLocalRing.notMem_maximalIdeal.mpr hr hmemB

private lemma branch_residue_separable [IsNoetherianRing R]
    {K : Type*} [Field K] [Algebra K R]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    [Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F)]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp))
    (hchar : ∀ r : ℕ, 0 < r → r ≤ F.natDegree → (r : K) ≠ 0)
    [IsLocalRing (baseSubring (R := R) (L := L) (F := F) hp w)]
    [IsLocalRing (branchSubring (R := R) (L := L) (F := F) hp w)]
    [IsLocalHom (algebraMap (baseSubring (R := R) (L := L) (F := F) hp w)
      (branchSubring (R := R) (L := L) (F := F) hp w))]
    (hf_pos : 0 < Module.finrank (IsLocalRing.ResidueField (baseSubring (R := R) (L := L) (F := F) hp w))
      (IsLocalRing.ResidueField (branchSubring (R := R) (L := L) (F := F) hp w)))
    (hf_le : Module.finrank (IsLocalRing.ResidueField (baseSubring (R := R) (L := L) (F := F) hp w))
      (IsLocalRing.ResidueField (branchSubring (R := R) (L := L) (F := F) hp w)) ≤ F.natDegree) :
    Algebra.IsSeparable
      (IsLocalRing.ResidueField (baseSubring (R := R) (L := L) (F := F) hp w))
      (IsLocalRing.ResidueField (branchSubring (R := R) (L := L) (F := F) hp w)) := by
  let KF := FractionRing L[X]
  let R₀ := localBase KF hp
  let Rloc := baseSubring (R := R) (L := L) (F := F) hp w
  let B := branchSubring (R := R) (L := L) (F := F) hp w
  let hRe : R₀ ≃+* Rloc := baseEquiv (R := R) (L := L) (F := F) hp w
  have hf_pos' : 0 < Module.finrank (IsLocalRing.ResidueField Rloc) (IsLocalRing.ResidueField B) :=
    hf_pos
  have hf_le' : Module.finrank (IsLocalRing.ResidueField Rloc) (IsLocalRing.ResidueField B) ≤
      F.natDegree := hf_le
  have : FiniteDimensional (IsLocalRing.ResidueField Rloc) (IsLocalRing.ResidueField B) :=
    Module.finite_of_finrank_pos hf_pos'
  constructor
  intro x
  have hint : IsIntegral (IsLocalRing.ResidueField Rloc) x := Algebra.IsIntegral.isIntegral x
  have hirr := minpoly.irreducible hint
  have hdeg_le : (minpoly (IsLocalRing.ResidueField Rloc) x).natDegree ≤ F.natDegree := by
    have h1 := IntermediateField.adjoin.finrank hint
    have h2 : Module.finrank (IsLocalRing.ResidueField Rloc)
        (IntermediateField.adjoin (IsLocalRing.ResidueField Rloc) {x}).toSubmodule ≤
        Module.finrank (IsLocalRing.ResidueField Rloc) (IsLocalRing.ResidueField B) :=
      Submodule.finrank_le _
    exact (h1.symm.trans_le h2).trans hf_le'
  have hdeg_pos : 0 < (minpoly (IsLocalRing.ResidueField Rloc) x).natDegree :=
    minpoly.natDegree_pos hint
  change (minpoly (IsLocalRing.ResidueField Rloc) x).Separable
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  intro hdz
  have hcoeff := congrArg (fun g => g.coeff ((minpoly (IsLocalRing.ResidueField Rloc) x).natDegree - 1)) hdz
  rw [coeff_derivative, coeff_zero, show (minpoly (IsLocalRing.ResidueField Rloc) x).natDegree - 1 + 1 =
    (minpoly (IsLocalRing.ResidueField Rloc) x).natDegree by omega,
    coeff_natDegree, (minpoly.monic hint).leadingCoeff, one_mul] at hcoeff
  have hcast : (((minpoly (IsLocalRing.ResidueField Rloc) x).natDegree - 1 : ℕ) + 1 :
      IsLocalRing.ResidueField Rloc) =
      ((minpoly (IsLocalRing.ResidueField Rloc) x).natDegree : IsLocalRing.ResidueField Rloc) := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hdeg_pos]
  rw [hcast] at hcoeff
  let kToRes : K →+* IsLocalRing.ResidueField Rloc :=
    (IsLocalRing.residue Rloc).comp
      (hRe.toRingHom.comp ((algebraMap R[X] R₀).comp (C.comp (algebraMap K R))))
  have hne : ((minpoly (IsLocalRing.ResidueField Rloc) x).natDegree : K) ≠ 0 :=
    hchar _ hdeg_pos hdeg_le
  have hne' : ((minpoly (IsLocalRing.ResidueField Rloc) x).natDegree : IsLocalRing.ResidueField Rloc) ≠ 0 := by
    rw [← map_natCast kToRes]
    exact (map_ne_zero_iff kToRes kToRes.injective).mpr hne
  exact hne' hcoeff

private lemma subalgebra_finite_localization
    (R₀ O B Rloc : Type*) [CommRing R₀] [CommRing O] [IsDomain O] [Algebra R₀ O] [Module.Finite R₀ O]
    [CommRing B] [Algebra O B] [Algebra R₀ B] [IsScalarTower R₀ O B]
    [CommRing Rloc] [Algebra Rloc B]
    (w : HeightOneSpectrum O) [IsLocalization.AtPrime B w.asIdeal]
    (hRe : R₀ ≃+* Rloc)
    (hcompat : ∀ r₀ : R₀, algebraMap Rloc B (hRe r₀) = algebraMap R₀ B r₀)
    (hinj : Function.Injective (algebraMap O B)) :
    ∃ (A : Subalgebra Rloc B) (_ : Module.Finite Rloc A)
      (S : Submonoid A), IsLocalization S B := by
  let ψ : O →+* B := algebraMap O B
  let A : Subalgebra Rloc B :=
    { carrier := Set.range ψ
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul ψ a b⟩
      one_mem' := ⟨1, map_one ψ⟩
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add ψ a b⟩
      zero_mem' := ⟨0, map_zero ψ⟩
      algebraMap_mem' := fun r => by
        obtain ⟨r₀, rfl⟩ := hRe.surjective r
        exact ⟨algebraMap R₀ O r₀, by rw [hcompat, IsScalarTower.algebraMap_apply R₀ O B]⟩ }
  let f : O →+* A := ψ.codRestrict A.toSubring (fun c => ⟨c, rfl⟩)
  have hf_bij : Function.Bijective f := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), ?_⟩
    rintro ⟨_, c, rfl⟩
    exact ⟨c, Subtype.ext rfl⟩
  let hOe : O ≃+* A := RingEquiv.ofBijective f hf_bij
  have hAfin : Module.Finite Rloc A := by
    classical
    obtain ⟨t, ht⟩ := (inferInstance : Module.Finite R₀ O).fg_top
    refine ⟨⟨t.image hOe, ?_⟩⟩
    rw [eq_top_iff]
    intro a _
    obtain ⟨c, rfl⟩ := hOe.surjective a
    have hc : c ∈ Submodule.span R₀ (t : Set O) := ht.symm ▸ Submodule.mem_top
    refine Submodule.span_induction
      (p := fun z _ => hOe z ∈ Submodule.span Rloc ((t.image hOe : Finset A) : Set A))
      (fun x hx => Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem hOe hx)))
      (by simp)
      (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
      (fun r₀ x _ hx => ?_) hc
    have hsmul : hOe (r₀ • x) = (hRe r₀) • hOe x := by
      apply Subtype.ext
      rw [Subalgebra.coe_smul, Algebra.smul_def, Algebra.smul_def]
      change ψ (algebraMap R₀ O r₀ * x) = algebraMap Rloc B (hRe r₀) * ψ x
      rw [map_mul, hcompat, IsScalarTower.algebraMap_apply R₀ O B]
    rw [hsmul]
    exact Submodule.smul_mem _ _ hx
  let S : Submonoid A := w.asIdeal.primeCompl.map hOe.toMonoidHom
  refine ⟨A, hAfin, S, ?_⟩
  constructor; constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩⟩
    change IsUnit (algebraMap O B c)
    exact IsLocalization.map_units B ⟨c, hc⟩
  · intro y
    obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj w.asIdeal.primeCompl y
    exact ⟨⟨hOe c, ⟨hOe s.1, s.1, s.2, rfl⟩⟩, e⟩
  · intro x y h
    obtain ⟨cx, rfl⟩ := hOe.surjective x
    obtain ⟨cy, rfl⟩ := hOe.surjective y
    have h' : algebraMap O B cx = algebraMap O B cy := h
    have hcx : cx = cy := IsLocalization.injective B w.asIdeal.primeCompl_le_nonZeroDivisors h'
    exact ⟨1, by simp [hcx]⟩

private lemma branch_finite_localization [IsNoetherianRing R]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    [Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F)]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    let B := branchSubring (R := R) (L := L) (F := F) hp w
    let Rloc := baseSubring (R := R) (L := L) (F := F) hp w
    ∃ (A : Subalgebra Rloc B) (_ : Module.Finite Rloc A)
      (S : Submonoid A), IsLocalization S B := by
  let KF := FractionRing L[X]
  let E := Curve (L := L) F
  let R₀ := localBase KF hp
  let O := localNormalization (K := KF) E hp
  let B : Subring E := branchSubring (R := R) (L := L) (F := F) hp w
  let Rloc : Subring B := baseSubring (R := R) (L := L) (F := F) hp w
  have : IsDiscreteValuationRing R₀ := localBase_dvr hp
  have : IsFractionRing R₀ KF := Localization.subalgebra.isFractionRing_ofField ..
  have : IsFractionRing O E := IsIntegralClosure.isFractionRing_of_finite_extension R₀ KF E O
  have : Module.Finite R₀ O := localNormalization_finite hp
  let _ : Algebra O B := (normToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
  let _ : Algebra R₀ B := (baseToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
  have : IsScalarTower R₀ O B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization.AtPrime B w.asIdeal := branchSubring_isLocalization F hp w
  exact subalgebra_finite_localization R₀ O B Rloc w (baseEquiv (R := R) (L := L) (F := F) hp w)
    (fun r₀ => baseEquiv_coe hp w r₀)
    (fun a b h => Subtype.ext (congrArg (fun x : B => (x : E)) h))

private lemma branch_base_derivation_compat [IsNoetherianRing R]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    [Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F)]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp))
    (δ : Derivation ℤ R[X] R[X])
    (D : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F))
    (hδ : ∀ c, D (planeBase (L := L) F c) = planeBase F (δ c)) :
    let B := branchSubring (R := R) (L := L) (F := F) hp w
    let Rloc := baseSubring (R := R) (L := L) (F := F) hp w
    let π : Rloc := baseEquiv (R := R) (L := L) (F := F) hp w
      (algebraMap R[X] (localBase (FractionRing L[X]) hp) p)
    (∀ r : Rloc, D ((r : B) : Curve (L := L) F) ∈ B) ∧
    (p ∣ δ p → ∃ c : Rloc, D ((π : B) : Curve (L := L) F) =
      ((π : B) : Curve (L := L) F) * ((c : B) : Curve (L := L) F)) := by
  let KF := FractionRing L[X]
  let E := Curve (L := L) F
  let R₀ := localBase KF hp
  let B : Subring E := branchSubring (R := R) (L := L) (F := F) hp w
  let Rloc : Subring B := baseSubring (R := R) (L := L) (F := F) hp w
  let _ : Algebra R₀ B := (baseToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
  let hRe : R₀ ≃+* Rloc := baseEquiv (R := R) (L := L) (F := F) hp w
  let π : Rloc := hRe (algebraMap R[X] R₀ p)
  have hbase_mem : ∀ r : Rloc, D ((r : B) : E) ∈ B := by
    intro r
    obtain ⟨r₀, rfl⟩ := hRe.surjective r
    obtain ⟨a, s, hs, hr₀⟩ := r₀.property
    have hps : ¬ p ∣ s := fun h => hs (Ideal.mem_span_singleton.mpr h)
    have hs0 : s ≠ 0 := fun h => hps (h ▸ dvd_zero p)
    have hsK : algebraMap R[X] KF s ≠ 0 := by
      simpa using (IsFractionRing.injective R[X] KF).ne hs0
    have hsE : planeBase (L := L) F s ≠ 0 := by
      change algebraMap KF E (algebraMap R[X] KF s) ≠ 0
      exact (map_ne_zero_iff _ (algebraMap KF E).injective).mpr hsK
    have heq : (r₀ : KF) * algebraMap R[X] KF s = algebraMap R[X] KF a := by
      rw [hr₀, mul_assoc, inv_mul_cancel₀ hsK, mul_one]
    have heqE : ((hRe r₀ : B) : E) * planeBase (L := L) F s = planeBase (L := L) F a := by
      have h := congrArg (algebraMap KF E) heq
      rw [map_mul] at h
      exact h
    have hd := congrArg D heqE
    rw [D.leibniz, hδ, hδ] at hd
    simp only [smul_eq_mul] at hd
    have hDval : D ((hRe r₀ : B) : E) =
        algebraMap KF E ((algebraMap R[X] KF (δ a) * algebraMap R[X] KF s -
          algebraMap R[X] KF a * algebraMap R[X] KF (δ s)) /
          (algebraMap R[X] KF (s * s))) := by
      have hss : planeBase (L := L) F s * planeBase (L := L) F s ≠ 0 := mul_ne_zero hsE hsE
      apply mul_right_cancel₀ hss
      simp only [map_div₀, map_sub, map_mul]
      change D ((hRe r₀ : B) : E) * (planeBase F s * planeBase F s) =
        (planeBase F (δ a) * planeBase F s - planeBase F a * planeBase F (δ s)) /
          (planeBase F s * planeBase F s) * (planeBase F s * planeBase F s)
      rw [div_mul_cancel₀ _ hss]
      linear_combination planeBase F s * hd - planeBase F (δ s) * heqE
    have hss_mem : s * s ∈ (divisor hp).asIdeal.primeCompl :=
      (divisor hp).asIdeal.primeCompl.mul_mem hs hs
    have hmem_R₀ : ((algebraMap R[X] KF (δ a) * algebraMap R[X] KF s -
        algebraMap R[X] KF a * algebraMap R[X] KF (δ s)) /
        (algebraMap R[X] KF (s * s))) ∈ R₀ := by
      refine ⟨δ a * s - a * δ s, s * s, hss_mem, ?_⟩
      simp [map_sub, map_mul, div_eq_mul_inv]
    rw [hDval]
    exact (algebraMap R₀ B ⟨_, hmem_R₀⟩).property
  refine ⟨hbase_mem, ?_⟩
  rintro ⟨q, hq⟩
  refine ⟨hRe (algebraMap R[X] R₀ q), ?_⟩
  change D (planeBase (L := L) F p) = planeBase (L := L) F p * planeBase (L := L) F q
  rw [hδ, hq, map_mul]

private lemma isUnit_natCast_of_ringHom {K B : Type*} [Field K] [CommRing B]
    (φ : K →+* B) {n : ℕ} (hn : (n : K) ≠ 0) : IsUnit (n : B) := by
  rw [← map_natCast φ]
  exact (isUnit_iff_ne_zero.mpr hn).map φ

private lemma dvr_uniformizer_factor_of_gen
    (R₀ O : Type*) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [CommRing O] [IsDedekindDomain O] [Algebra R₀ O] [FaithfulSMul R₀ O]
    {E : Type*} [CommRing E] [IsDomain E] (B : Subring E) [IsDiscreteValuationRing B]
    [Algebra O B] [Algebra R₀ B] [IsScalarTower R₀ O B]
    (Rloc : Subring B) (hRe : R₀ ≃+* Rloc) (hcompat : ∀ r₀, (hRe r₀ : B) = algebraMap R₀ B r₀)
    (w : HeightOneSpectrum O) [IsLocalization.AtPrime B w.asIdeal]
    (hw_lies : w.asIdeal.LiesOver (IsLocalRing.maximalIdeal R₀))
    (π₀ : R₀) (hπ₀_gen : IsLocalRing.maximalIdeal R₀ = Ideal.span {π₀})
    (n : ℕ) (hn : w.asIdeal.ramificationIdx R₀ = n) :
    ∃ (u : B) (v : Bˣ), Irreducible u ∧ (hRe π₀ : B) = u ^ n * v := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπ_span : Ideal.span {algebraMap R₀ B π₀} = Ideal.span {u ^ n} := by
    have h1 : Ideal.span {algebraMap R₀ B π₀} =
        (IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ B) := by
      rw [hπ₀_gen, Ideal.map_span, Set.image_singleton]
    rw [h1, dvr_base_map_eq_maximalIdeal_pow R₀ O B w hw_lies, hn,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer u).mp hu, Ideal.span_singleton_pow]
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hπ_span.symm
  exact ⟨u, v, hu, (hcompat π₀).trans hv.symm⟩

private lemma localBase_maximalIdeal_eq_span [IsNoetherianRing R] {p : R[X]} (hp : Prime p) :
    @IsLocalRing.maximalIdeal (localBase (FractionRing L[X]) hp) _
      (localBase_dvr (K := FractionRing L[X]) hp).toIsLocalRing =
    Ideal.span {algebraMap R[X] (localBase (FractionRing L[X]) hp) p} := by
  let R₀ := localBase (FractionRing L[X]) hp
  let _ : IsDiscreteValuationRing R₀ := localBase_dvr hp
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (divisor hp).asIdeal R₀]
  simp only [divisor, Ideal.map_span, Set.image_singleton]
  rfl

private lemma branch_uniformizer_pow [IsNoetherianRing R]
    {K : Type*} [Field K] [Algebra K R]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    [Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F)]
    {p : R[X]} (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp))
    (hchar : ∀ r : ℕ, 0 < r → r ≤ F.natDegree → (r : K) ≠ 0) :
    let B := branchSubring (R := R) (L := L) (F := F) hp w
    let Rloc := baseSubring (R := R) (L := L) (F := F) hp w
    let π : Rloc := baseEquiv (R := R) (L := L) (F := F) hp w
      (algebraMap R[X] (localBase (FractionRing L[X]) hp) p)
    ∃ (_ : IsDiscreteValuationRing B) (_ : IsLocalRing Rloc) (_ : IsLocalHom (algebraMap Rloc B))
      (_ : Algebra.IsSeparable (IsLocalRing.ResidueField Rloc) (IsLocalRing.ResidueField B))
      (u : B) (e : ℕ) (v : Bˣ),
      Irreducible u ∧ IsUnit ((e + 1 : ℕ) : B) ∧ (π : B) = u ^ (e + 1) * v := by
  let KF := FractionRing L[X]
  let E := Curve (L := L) F
  let R₀ := localBase KF hp
  let O := localNormalization (K := KF) E hp
  let B : Subring E := branchSubring (R := R) (L := L) (F := F) hp w
  let Rloc : Subring B := baseSubring (R := R) (L := L) (F := F) hp w
  let _ : IsDiscreteValuationRing R₀ := localBase_dvr hp
  have : IsFractionRing R₀ KF := Localization.subalgebra.isFractionRing_ofField ..
  have : IsDedekindDomain O := integralClosure.isDedekindDomain R₀ KF E
  have : IsFractionRing O E := IsIntegralClosure.isFractionRing_of_finite_extension R₀ KF E O
  have : Module.Finite R₀ O := localNormalization_finite hp
  let _ : Algebra O B := (normToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
  let _ : Algebra R₀ B := (baseToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
  have : IsScalarTower R₀ O B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization.AtPrime B w.asIdeal := branchSubring_isLocalization F hp w
  have hBdvr : IsDiscreteValuationRing B := (branchSubring_dvr F hp w).1
  let hRe : R₀ ≃+* Rloc := baseEquiv (R := R) (L := L) (F := F) hp w
  have hRloc : IsLocalRing Rloc := hRe.isLocalRing
  have hfinE : Module.finrank KF E = F.natDegree := curve_finrank_eq_natDegree F
  obtain ⟨hw_under, hw_lies, he_pos, he_le', hf_pos, hf_le'⟩ :=
    dvr_ramification_inertia_le R₀ KF O E w
  have he_le : w.asIdeal.ramificationIdx R₀ ≤ F.natDegree := hfinE ▸ he_le'
  have hf_le : w.asIdeal.inertiaDeg R₀ ≤ F.natDegree := hfinE ▸ hf_le'
  have hRBlocal : IsLocalHom (algebraMap Rloc B) :=
    branch_localHom F hp w (fun r₀ hnot₀ => by
      have hr₀ : r₀ ∈ w.asIdeal.under R₀ :=
        hw_under.symm ▸ (IsLocalRing.mem_maximalIdeal r₀).mpr hnot₀
      exact hr₀)
  have : FaithfulSMul R₀ O := FaithfulSMul.of_field_isFractionRing R₀ O KF E
  let π₀ : R₀ := algebraMap R[X] R₀ p
  let e : ℕ := w.asIdeal.ramificationIdx R₀ - 1
  have he1 : w.asIdeal.ramificationIdx R₀ = e + 1 := (Nat.sub_add_cancel he_pos).symm
  obtain ⟨u, v, hu, hπ_eq⟩ := dvr_uniformizer_factor_of_gen R₀ O B Rloc hRe
    (fun r₀ => baseEquiv_coe hp w r₀) w hw_lies π₀
    (localBase_maximalIdeal_eq_span (R := R) (L := L) hp) (e + 1) he1
  have he_unit : IsUnit ((e + 1 : ℕ) : B) := by
    have hne : ((e + 1 : ℕ) : K) ≠ 0 := hchar (e + 1) (by omega) (he1 ▸ he_le)
    let kToB : K →+* B := (baseToBranch (R := R) (L := L) (F := F) hp w).comp
      ((algebraMap R[X] R₀).comp (C.comp (algebraMap K R)))
    exact isUnit_natCast_of_ringHom kToB hne
  have hres_eq := dvr_residue_finrank_eq R₀ O B Rloc w hw_lies hRe (fun r₀ => baseEquiv_coe hp w r₀)
  have hres_sep := branch_residue_separable F hp w hchar (hres_eq ▸ hf_pos) (hres_eq ▸ hf_le)
  exact ⟨hBdvr, hRloc, hRBlocal, hres_sep, u, e, v, hu, he_unit, hπ_eq⟩

/-- Universal ramification and residue-field inertia bounds for every branch above a prime `p`:
the base uniformizer `π` factors as `u ^ (e + 1) * v` with `e + 1 ≤ F.natDegree` and
`finrank (ResidueField R_loc) (ResidueField B) ≤ F.natDegree`. When all `1 ≤ r ≤ F.natDegree` are
nonzero in a base field `K` mapping into `R`, the extension is tamely ramified with separable
residue extension. -/
theorem branch_tame_and_separable [IsNoetherianRing R]
    {K : Type*} [Field K] [Algebra K R]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    [Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F)]
    (p : R[X]) (hp : Prime p)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp))
    (hchar : ∀ r : ℕ, 0 < r → r ≤ F.natDegree → (r : K) ≠ 0) :
    let B := branchSubring (R := R) (L := L) (F := F) hp w
    let Rloc := baseSubring (R := R) (L := L) (F := F) hp w
    ∃ (_ : IsDiscreteValuationRing B) (_ : IsFractionRing B (Curve (L := L) F))
      (_ : IsLocalRing Rloc) (_ : IsLocalHom (algebraMap Rloc B))
      (_ : Algebra.IsSeparable (IsLocalRing.ResidueField Rloc) (IsLocalRing.ResidueField B))
      (A : Subalgebra Rloc B) (_ : Module.Finite Rloc A)
      (S : Submonoid A) (_ : IsLocalization S B)
      (u : B) (e : ℕ) (v : Bˣ) (π : Rloc),
      Irreducible u ∧
      IsUnit ((e + 1 : ℕ) : B) ∧
      ((π : B) : Curve (L := L) F) = planeBase (L := L) F p ∧
      (π : B) = u ^ (e + 1) * v ∧
      (∀ (δ : Derivation ℤ R[X] R[X])
        (D : Derivation ℤ (Curve (L := L) F) (Curve (L := L) F)),
        (∀ c, D (planeBase (L := L) F c) = planeBase F (δ c)) →
        (∀ r : Rloc, D ((r : B) : Curve (L := L) F) ∈ B) ∧
        (p ∣ δ p → ∃ c : Rloc, D ((π : B) : Curve (L := L) F) =
          ((π : B) : Curve (L := L) F) * ((c : B) : Curve (L := L) F))) := by
  obtain ⟨_, hBfrac⟩ := branchSubring_dvr (R := R) (L := L) F hp w
  obtain ⟨hBdvr, hRloc, hRBlocal, hres_sep, u, e, v, hu, he_unit, hπ_fac⟩ :=
    branch_uniformizer_pow (R := R) (L := L) (K := K) F hp w hchar
  obtain ⟨A, hAfin, S, hSloc⟩ := branch_finite_localization (R := R) (L := L) F hp w
  let π := baseEquiv (R := R) (L := L) (F := F) hp w
    (algebraMap R[X] (localBase (FractionRing L[X]) hp) p)
  exact ⟨hBdvr, hBfrac, hRloc, hRBlocal, hres_sep, A, hAfin, S, hSloc, u, e, v, π,
    hu, he_unit, rfl, hπ_fac, fun δ D hδ => branch_base_derivation_compat F hp w δ D hδ⟩

private lemma branch_monic_unit_discr_generator [IsNoetherianRing R]
    {K : Type*} [Field K] [Infinite K] [Algebra K R]
    (F : R[X][X]) [hIrr : Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    {p : R[X]} (hp : Prime p) (hnd : ¬ p ∣ F.discr) :
    let KF := FractionRing L[X]
    let E := Curve (L := L) F
    let R₀ := localBase KF hp
    ∃ (G : R₀[X]) (T : E),
      G.Monic ∧ G.natDegree = F.natDegree ∧ IsUnit G.discr ∧
      aeval T G = 0 ∧
      Algebra.adjoin KF ({T} : Set E) = ⊤ := by
  classical
  let KF := FractionRing L[X]
  let E := Curve (L := L) F
  let R₀ := localBase KF hp
  have : IsDiscreteValuationRing R₀ := localBase_dvr hp
  have : IsFractionRing R₀ KF := Localization.subalgebra.isFractionRing_ofField ..
  have hdiscr_unit : IsUnit (algebraMap R[X] R₀ F.discr) := by
    have hmem : F.discr ∈ (divisor hp).asIdeal.primeCompl :=
      fun h => hnd (Ideal.mem_span_singleton.mp h)
    exact IsLocalization.map_units R₀ ⟨F.discr, hmem⟩
  let ρ : R[X] →+* IsLocalRing.ResidueField R₀ :=
    (IsLocalRing.residue R₀).comp (algebraMap R[X] R₀)
  have hFmap_ne : F.map ρ ≠ 0 := by
    intro hz
    have hprim : F.IsPrimitive := hFirr.isPrimitive (by omega)
    have hp_all : ∀ j, p ∣ F.coeff j := by
      intro j
      have h0 := congrArg (fun g => g.coeff j) hz
      rw [coeff_map, coeff_zero] at h0
      have hcomap : F.coeff j ∈ (divisor hp).asIdeal := by
        rw [← IsLocalization.AtPrime.under_maximalIdeal R₀ (divisor hp).asIdeal]
        exact (IsLocalRing.residue_eq_zero_iff _).mp h0
      exact Ideal.mem_span_singleton.mp hcomap
    exact hp.not_isUnit (hprim p ((C_dvd_iff_dvd_coeff p F).mpr hp_all))
  let kToRes : K →+* IsLocalRing.ResidueField R₀ := ρ.comp (C.comp (algebraMap K R))
  have hkinj : Function.Injective kToRes := kToRes.injective
  let bad : Finset K := ((F.map ρ).roots.toFinset).preimage kToRes hkinj.injOn
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset bad
  have ha_eval : (F.map ρ).eval (kToRes a) ≠ 0 := by
    intro hev
    exact ha (Finset.mem_preimage.mpr (Multiset.mem_toFinset.mpr ((mem_roots hFmap_ne).mpr hev)))
  let a₀ : R[X] := C (algebraMap K R a)
  have hFa_unit : IsUnit (algebraMap R[X] R₀ (F.eval a₀)) := by
    have hres : IsLocalRing.residue R₀ (algebraMap R[X] R₀ (F.eval a₀)) ≠ 0 := by
      change ρ (F.eval a₀) ≠ 0
      rw [← eval₂_at_apply, ← eval_map]
      exact ha_eval
    exact IsLocalRing.notMem_maximalIdeal.mp
      (fun hm => hres ((IsLocalRing.residue_eq_zero_iff _).mpr hm))
  set b := F.natDegree with hb_def
  let F₁ : R[X][X] := F.taylor a₀
  have hF₁deg : F₁.natDegree = b := natDegree_taylor F a₀
  have hFa₀_ne : F.eval a₀ ≠ 0 := fun hz => hFa_unit.ne_zero (by rw [hz, map_zero])
  have hF₁0 : F₁.coeff 0 ≠ 0 := by simpa [F₁, taylor_coeff_zero] using hFa₀_ne
  let Graw : R[X][X] := F₁.reflect b
  have hGraw_deg : Graw.natDegree = b := by
    apply le_antisymm (natDegree_reflect_le.trans (by omega))
    apply le_natDegree_of_ne_zero
    simpa [Graw, coeff_reflect, revAt_le le_rfl] using hF₁0
  have hGraw_lc : Graw.leadingCoeff = F.eval a₀ := by
    rw [leadingCoeff, hGraw_deg]
    simp [Graw, F₁, coeff_reflect, revAt_le le_rfl, taylor_coeff_zero]
  have hGraw_discr : Graw.discr = F.discr := by
    rw [show Graw = F₁.reflect F₁.natDegree by rw [hF₁deg],
      discr_reflect F₁ (by omega) hF₁0, discr_taylor F (by omega) a₀]
  let ua : R₀ˣ := hFa_unit.unit
  have hua : (ua : R₀) = algebraMap R[X] R₀ (F.eval a₀) := rfl
  let G : R₀[X] := C (↑ua⁻¹ : R₀) * Graw.map (algebraMap R[X] R₀)
  have hR₀inj : Function.Injective (algebraMap R[X] R₀) :=
    IsLocalization.injective R₀ (divisor hp).asIdeal.primeCompl_le_nonZeroDivisors
  have hGmap_deg : (Graw.map (algebraMap R[X] R₀)).natDegree = b :=
    (natDegree_map_eq_of_injective hR₀inj Graw).trans hGraw_deg
  have hGdeg : G.natDegree = b := by
    dsimp [G]; rw [natDegree_C_mul ua⁻¹.ne_zero, hGmap_deg]
  have hGmonic : G.Monic := by
    rw [Monic, leadingCoeff, hGdeg]
    dsimp [G]
    rw [coeff_C_mul, coeff_map, ← hGraw_deg, ← leadingCoeff, hGraw_lc, ← hua, Units.inv_mul]
  have hGdiscr_unit : IsUnit G.discr := by
    dsimp [G]
    rw [discr_C_mul _ (by omega) ua⁻¹.ne_zero,
      discr_map_of_natDegree_eq (algebraMap R[X] R₀) Graw (natDegree_map_eq_of_injective hR₀inj _),
      hGraw_discr]
    exact (ua⁻¹.isUnit.pow _).mul hdiscr_unit
  let Y : E := AdjoinRoot.root (F.map (genericCoeffs (R := R) (L := L)))
  have hYroot : F.eval₂ (planeBase (L := L) F) Y = 0 := by
    change F.eval₂ ((AdjoinRoot.of _).comp _) Y = 0
    rw [← eval₂_map]; exact AdjoinRoot.eval₂_root _
  have hYne : Y ≠ planeBase (L := L) F a₀ := by
    intro heq
    rw [heq, eval₂_at_apply] at hYroot
    have hinjE : Function.Injective (planeBase (L := L) F) :=
      (algebraMap KF E).injective.comp (IsFractionRing.injective R[X] KF)
    exact hFa₀_ne (hinjE (hYroot.trans (map_zero _).symm))
  let T : E := (Y - planeBase (L := L) F a₀)⁻¹
  have hT_root : aeval T G = 0 := by
    have hF₁root : F₁.eval₂ (planeBase (L := L) F) (Y - planeBase (L := L) F a₀) = 0 := by
      rw [show F₁ = F.comp (X + C a₀) from taylor_apply a₀ F, eval₂_comp]
      simpa using hYroot
    let _ : Invertible (Y - planeBase (L := L) F a₀) := invertibleOfNonzero (sub_ne_zero.mpr hYne)
    have href := eval₂_reflect_mul_pow (planeBase (L := L) F) (Y - planeBase (L := L) F a₀) b F₁
      (by omega)
    rw [hF₁root] at href
    have hGraw_root : Graw.eval₂ (planeBase (L := L) F) T = 0 := by
      have h0 := (mul_eq_zero.mp href).resolve_right (pow_ne_zero b (sub_ne_zero.mpr hYne))
      simpa [Graw, T, invOf_eq_inv] using h0
    have hcomp : (algebraMap R₀ E).comp (algebraMap R[X] R₀) = planeBase (L := L) F := by
      ext <;> rfl
    dsimp [G]
    rw [aeval_def, eval₂_mul, eval₂_C, eval₂_map, hcomp, hGraw_root, mul_zero]
  refine ⟨G, T, hGmonic, hGdeg, hGdiscr_unit, hT_root, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective (g := F.map (genericCoeffs (R := R) (L := L))) x
  rw [← AdjoinRoot.aeval_eq]
  have hT_ne : T ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hYne)
  have hTinv_mem : T⁻¹ ∈ Algebra.adjoin KF ({T} : Set E) := by
    have hG0 : G.coeff 0 ≠ 0 := by
      dsimp [G]
      rw [coeff_C_mul, coeff_map, show Graw.coeff 0 = F₁.coeff b from by
        simp [Graw, coeff_reflect], ← hF₁deg, coeff_natDegree]
      have hF₁lc : F₁.leadingCoeff = F.leadingCoeff := by
        rw [leadingCoeff, hF₁deg, coeff_taylor_natDegree]
      rw [hF₁lc]
      exact mul_ne_zero ua⁻¹.ne_zero
        ((map_ne_zero_iff _ hR₀inj).mpr (leadingCoeff_ne_zero.mpr hFirr.ne_zero))
    have hev := congrArg (aeval T) (Polynomial.divX_mul_X_add G)
    rw [hT_root, map_add, map_mul, aeval_X, aeval_C] at hev
    have hTinv : T⁻¹ = -(algebraMap R₀ KF (G.coeff 0))⁻¹ • aeval T G.divX := by
      have hcne : algebraMap R₀ E (G.coeff 0) ≠ 0 := by
        have hinjRE : Function.Injective (algebraMap R₀ E) :=
          (algebraMap KF E).injective.comp (IsFractionRing.injective R₀ KF)
        exact (map_ne_zero_iff _ hinjRE).mpr hG0
      apply mul_left_cancel₀ hcne
      apply mul_right_cancel₀ hT_ne
      rw [Algebra.smul_def, map_neg, map_inv₀,
        (IsScalarTower.algebraMap_apply R₀ KF E _).symm]
      have hinv : T⁻¹ * T = 1 := inv_mul_cancel₀ hT_ne
      have hinv2 : algebraMap R₀ E (G.coeff 0) * (algebraMap R₀ E (G.coeff 0))⁻¹ = 1 :=
        mul_inv_cancel₀ hcne
      linear_combination hev + algebraMap R₀ E (G.coeff 0) * hinv +
        (aeval T G.divX * T) * hinv2
    rw [hTinv]
    refine Subalgebra.smul_mem _ ?_ _
    have hGdiv : aeval T G.divX = aeval T (G.divX.map (algebraMap R₀ KF)) := by
      rw [aeval_map_algebraMap]
    rw [hGdiv]
    exact Polynomial.aeval_mem_adjoin_singleton KF T
  have hY_mem : Y ∈ Algebra.adjoin KF ({T} : Set E) := by
    have hYeq : Y = planeBase (L := L) F a₀ + T⁻¹ := by dsimp [T]; rw [inv_inv]; ring
    rw [hYeq]
    exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ (genericCoeffs a₀)) hTinv_mem
  exact Algebra.adjoin_singleton_le hY_mem (g.aeval_mem_adjoin_singleton _ _)

private lemma branch_ramificationIdx_eq_one [IsNoetherianRing R]
    {K : Type*} [Field K] [Infinite K] [Algebra K R]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    [Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F)]
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    {p : R[X]} (hp : Prime p) (hnd : ¬ p ∣ F.discr)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    w.asIdeal.LiesOver (@IsLocalRing.maximalIdeal (localBase (FractionRing L[X]) hp) _
      (localBase_dvr (K := FractionRing L[X]) hp).toIsLocalRing) ∧
    w.asIdeal.ramificationIdx (localBase (FractionRing L[X]) hp) = 1 := by
  let KF := FractionRing L[X]
  let E := Curve (L := L) F
  let R₀ := localBase KF hp
  let O := localNormalization (K := KF) E hp
  let _ : IsDiscreteValuationRing R₀ := localBase_dvr hp
  have : IsFractionRing R₀ KF := Localization.subalgebra.isFractionRing_ofField ..
  have : IsDedekindDomain O := integralClosure.isDedekindDomain R₀ KF E
  have : IsFractionRing O E := IsIntegralClosure.isFractionRing_of_finite_extension R₀ KF E O
  have : Module.Finite R₀ O := localNormalization_finite hp
  obtain ⟨G, T, hGmonic, hGdeg, hGdiscr_unit, hT_root, hT_gen⟩ :=
    branch_monic_unit_discr_generator (R := R) (L := L) (K := K) F hFirr hb hp hnd
  have hfinE : Module.finrank KF E = F.natDegree := curve_finrank_eq_natDegree F
  exact dvr_ramificationIdx_eq_one_of_monic_unit_discr R₀ KF O E G hGmonic (by omega)
    (by omega) hGdiscr_unit T hT_root hT_gen w

/-- Unramifiedness off `F.discr`: if `¬ p ∣ F.discr` and `K` is an infinite field mapping into
`R`, then for every branch `w` above `p`, the base uniformizer `π = p` is already a uniformizer of
`branchRing hp w` (`(π : B) = u * v` for an irreducible `u : B` and unit `v : Bˣ`). -/
theorem branch_unramified_of_not_dvd_discr [IsNoetherianRing R]
    {K : Type*} [Field K] [Infinite K] [Algebra K R]
    (F : R[X][X]) [Fact (Irreducible (F.map (genericCoeffs (R := R) (L := L))))]
    [Algebra.IsSeparable (FractionRing L[X]) (Curve (L := L) F)]
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    (p : R[X]) (hp : Prime p) (hnd : ¬ p ∣ F.discr)
    (w : HeightOneSpectrum (localNormalization (K := FractionRing L[X]) (Curve (L := L) F) hp)) :
    let B := branchSubring (R := R) (L := L) (F := F) hp w
    let Rloc := baseSubring (R := R) (L := L) (F := F) hp w
    ∃ (u : B) (v : Bˣ) (π : Rloc),
      Irreducible u ∧
      ((π : B) : Curve (L := L) F) = planeBase (L := L) F p ∧
      (π : B) = u * v := by
  let KF := FractionRing L[X]
  let E := Curve (L := L) F
  let R₀ := localBase KF hp
  let O := localNormalization (K := KF) E hp
  let B : Subring E := branchSubring (R := R) (L := L) (F := F) hp w
  let Rloc : Subring B := baseSubring (R := R) (L := L) (F := F) hp w
  let _ : IsDiscreteValuationRing R₀ := localBase_dvr hp
  have : IsFractionRing R₀ KF := Localization.subalgebra.isFractionRing_ofField ..
  have : IsDedekindDomain O := integralClosure.isDedekindDomain R₀ KF E
  have : IsFractionRing O E := IsIntegralClosure.isFractionRing_of_finite_extension R₀ KF E O
  let _ : Algebra O B := (normToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
  let _ : Algebra R₀ B := (baseToBranch (R := R) (L := L) (F := F) hp w).toAlgebra
  have : IsScalarTower R₀ O B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization.AtPrime B w.asIdeal := branchSubring_isLocalization F hp w
  have : IsDiscreteValuationRing B := (branchSubring_dvr F hp w).1
  have : FaithfulSMul R₀ O := FaithfulSMul.of_field_isFractionRing R₀ O KF E
  obtain ⟨hw_lies, hram1⟩ := branch_ramificationIdx_eq_one (R := R) (L := L) (K := K) F hFirr hb hp hnd w
  let hRe : R₀ ≃+* Rloc := baseEquiv (R := R) (L := L) (F := F) hp w
  let π₀ : R₀ := algebraMap R[X] R₀ p
  obtain ⟨u, v, hu, hπ_eq⟩ := dvr_uniformizer_factor_of_gen R₀ O B Rloc hRe
    (fun r₀ => baseEquiv_coe hp w r₀) w hw_lies π₀
    (localBase_maximalIdeal_eq_span (R := R) (L := L) hp) 1 hram1
  rw [pow_one] at hπ_eq
  exact ⟨u, v, hRe π₀, hu, rfl, hπ_eq⟩

end BranchDVR

#print axioms natDegree_discr_le_weighted
#print axioms discr_natDegree_le
#print axioms discr_degreeX_le
#print axioms discr_ne_zero
#print axioms discr_C_mul
#print axioms discr_taylor
#print axioms discr_reflect
#print axioms factor_split
#print axioms branch_tame_and_separable
#print axioms branch_unramified_of_not_dvd_discr

end ArkLib.ProximityGap.Frontier.DiscriminantFactorSplit
