/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.BWMatrix

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon

/-!
# BCIKS20 affine lines — the Berlekamp-Welch homogeneous matrix

This file defines `BW_homMatrix`, the homogeneous Berlekamp-Welch matrix over a commutative ring,
and proves the structural facts about its entries used to build interpolating polynomials from
proximity data over affine lines. The engine lemmas compute entry degrees in the polynomial
specialization (e.g. `BW_homMatrix_entry_natDegree_eq_zero_of_ge` and its commuted variant),
supporting the kernel / determinant arguments in `GoodCoeffs` and `JointAgreement`.
-/

set_option linter.style.longFile 2000

-- Decidability/Fintype instances are threaded through the sections; several
-- statement-level engine lemmas do not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Polynomial in
theorem BW_homMatrix_entry_natDegree_eq_zero_of_ge_comm {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F) (i : ι)
    (j : Fin ((e + 1) + (e + k))) (hj : e + 1 ≤ j.1) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X) i j).natDegree = 0 := by
  have h :=
    BW_homMatrix_entry_natDegree_eq_zero_of_ge (ι := ι) (F := F) e k ωs f0 f1 i j hj
  have hfun :
      (fun i : ι => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
        = (fun i : ι => Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X) := by
    funext i'
    rw [mul_comm Polynomial.X (Polynomial.C (f1 i'))]
  -- rewrite the auxiliary lemma with the commuting multiplication
  simpa [hfun] using h


open Matrix in
open Polynomial in
theorem RS_exists_nonzero_kernelVec_of_det_eq_zero {F : Type} [Field F] (e : ℕ)
    (K : Matrix (Fin (e + 1)) (Fin (e + 1)) (Polynomial F))
    (hdet : Matrix.det K = 0) :
    ∃ a : Fin (e + 1) → (Polynomial F), a ≠ 0 ∧ Matrix.mulVec K a = 0 := by
  classical
  rcases (Matrix.exists_mulVec_eq_zero_iff (M := K)).2 hdet with ⟨a, ha0, hmul⟩
  refine ⟨a, ha0, ?_⟩
  simpa using hmul

open Polynomial in
/-- Degree-`d` generalization of `BW_homMatrix_entry_natDegree_le_one` (the
curves case of [BCIKS20] §6.1: matrix entries are polynomials of `z`-degree at
most `k` instead of affine). Entries of the Berlekamp–Welch matrix built over
`F[X]`-constants `ωs` and arbitrary words `g` of degree ≤ `d` have degree ≤ `d`.
The line case is `d = 1`, `g i = C (f0 i) + X * C (f1 i)`. -/
theorem BW_homMatrix_entry_natDegree_le_of_natDegree_le {F : Type} [Field F]
    {ι : Type} [Fintype ι] (e k : ℕ) (ωs : ι → F) (g : ι → F[X]) (d : ℕ)
    (hd : ∀ i, (g i).natDegree ≤ d) (i : ι) (j : Fin ((e + 1) + (e + k))) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X])) g i j).natDegree ≤ d := by
  classical
  by_cases hjlt : (j.1 < e + 1)
  · -- evaluation block: g i * C(ωs i)^j — degree ≤ deg (g i) + 0
    simp only [BW_homMatrix, Matrix.of_apply, hjlt, ↓reduceIte]
    calc ((g i) * (Polynomial.C (ωs i)) ^ j.1).natDegree
        ≤ (g i).natDegree + ((Polynomial.C (ωs i)) ^ j.1).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ d + 0 := by
          refine Nat.add_le_add (hd i) ?_
          exact Polynomial.natDegree_pow_le_of_le j.1
            (le_of_eq (Polynomial.natDegree_C (ωs i)))
      _ = d := Nat.add_zero d
  · -- constraint block: -C(ωs i)^(j-(e+1)) — degree 0
    simp only [BW_homMatrix, Matrix.of_apply, hjlt, ↓reduceIte, Polynomial.natDegree_neg]
    calc ((Polynomial.C (ωs i)) ^ (j.1 - (e + 1))).natDegree
        ≤ (j.1 - (e + 1)) * (Polynomial.C (ωs i)).natDegree := Polynomial.natDegree_pow_le
      _ = 0 := by simp [Polynomial.natDegree_C]
      _ ≤ d := Nat.zero_le d


open Polynomial in
/-- Degree-`d` generalization of `RS_natDegree_det_le_of_entry_natDegree_le_one`
(the curves case of [BCIKS20] §6.1): the determinant of an `n × n` matrix of
polynomials with entries of degree ≤ `d` has degree ≤ `d * n`. The line case
is `d = 1`. -/
theorem RS_natDegree_det_le_of_entry_natDegree_le (n d : ℕ)
    (A : Matrix (Fin n) (Fin n) F[X])
    (hdeg : ∀ i j, (A i j).natDegree ≤ d) :
    (Matrix.det A).natDegree ≤ d * n := by
  classical
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (f := fun σ : Equiv.Perm (Fin n) => (Equiv.Perm.sign σ : Units ℤ) • (∏ i : Fin n, A (σ i) i)) ?_
  intro σ hσ
  have hsign :
      ((Equiv.Perm.sign σ : Units ℤ) • (∏ i : Fin n, A (σ i) i)).natDegree
        ≤ (∏ i : Fin n, A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simp [hs]
    · simp [hs]
  have hprod : (∏ i : Fin n, A (σ i) i).natDegree ≤ d * n := by
    have h1 : (∏ i : Fin n, A (σ i) i).natDegree ≤ ∑ i : Fin n, (A (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => A (σ i) i))
    have h2 : (∑ i : Fin n, (A (σ i) i).natDegree) ≤ d * n := by
      have hsum' : (∑ i ∈ (Finset.univ : Finset (Fin n)), (A (σ i) i).natDegree)
          ≤ (Finset.univ : Finset (Fin n)).card • (d : ℕ) :=
        Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => (A (σ i) i).natDegree) (n := d)
          (fun i _ => hdeg (σ i) i)
      simpa [Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm] using hsum'
    exact le_trans h1 h2
  exact le_trans hsign hprod


open Polynomial in
/-- Degree-`d` generalization of `BW_homMatrix_det_submatrix_natDegree_le_e_add_one`
(the curves case of [BCIKS20] §6.1): minors of the BW matrix over words of
degree ≤ `d` have degree ≤ `d * (e + 1)` — only the `e + 1` evaluation columns
carry degree. The line case is `d = 1`. -/
theorem BW_homMatrix_det_submatrix_natDegree_le_of_natDegree_le {F : Type} [Field F]
    {ι : Type} [Fintype ι] (e k : ℕ) (ωs : ι → F) (g : ι → F[X]) (d : ℕ)
    (hd : ∀ i, (g i).natDegree ≤ d) (r : Fin ((e + 1) + (e + k)) → ι) :
    (Matrix.det
        (Matrix.submatrix
          (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X])) g)
          r id)).natDegree ≤ d * (e + 1) := by
  classical
  set A : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.submatrix
      (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X])) g) r id with hA
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := (Finset.univ : Finset (Equiv.Perm (Fin ((e + 1) + (e + k))))))
    (f := fun σ => (Equiv.Perm.sign σ : Units ℤ) • (∏ i, A (σ i) i)) ?_
  intro σ _
  have hsign : ((Equiv.Perm.sign σ : Units ℤ) • (∏ i, A (σ i) i)).natDegree
      ≤ (∏ i, A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simp [hs]
    · simp [hs]
  refine le_trans hsign ?_
  -- column-precise entry bounds
  have hcol : ∀ j : Fin ((e + 1) + (e + k)),
      (A (σ j) j).natDegree ≤ if j.1 < e + 1 then d else 0 := by
    intro j
    by_cases hj : (j.1 < e + 1)
    · simp only [hA, Matrix.submatrix_apply, id, BW_homMatrix, Matrix.of_apply, hj, ↓reduceIte]
      calc ((g (r (σ j))) * (Polynomial.C (ωs (r (σ j)))) ^ j.1).natDegree
          ≤ (g (r (σ j))).natDegree + ((Polynomial.C (ωs (r (σ j)))) ^ j.1).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ d + 0 := by
            refine Nat.add_le_add (hd _) ?_
            exact Polynomial.natDegree_pow_le_of_le j.1
              (le_of_eq (Polynomial.natDegree_C (ωs (r (σ j)))))
        _ = d := Nat.add_zero d
    · simp only [hA, Matrix.submatrix_apply, id, BW_homMatrix, Matrix.of_apply, hj, ↓reduceIte,
        Polynomial.natDegree_neg]
      calc ((Polynomial.C (ωs (r (σ j)))) ^ (j.1 - (e + 1))).natDegree
          ≤ (j.1 - (e + 1)) * (Polynomial.C (ωs (r (σ j)))).natDegree :=
            Polynomial.natDegree_pow_le
        _ = 0 := by simp [Polynomial.natDegree_C]
  -- product over columns: degree ≤ Σ column bounds = d * (e + 1)
  calc (∏ i, A (σ i) i).natDegree
      ≤ ∑ i, (A (σ i) i).natDegree := by
        simpa using Polynomial.natDegree_prod_le
          (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (f := fun i => A (σ i) i)
    _ ≤ ∑ j : Fin ((e + 1) + (e + k)), (if j.1 < e + 1 then d else 0) :=
        Finset.sum_le_sum (fun j _ => hcol j)
    _ = d * (e + 1) := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, smul_eq_mul]
        have hcard : #{j : Fin ((e + 1) + (e + k)) | j.1 < e + 1} = e + 1 := by
          have := Fin_sum_ite_lt_e_add_one e k
          simpa [Nat.lt_succ_iff] using this
        rw [hcard, mul_comm]


open Polynomial in
/-- Branch-precise entry degree bound for the BW matrix over degree-≤`d` words:
evaluation columns (index < e+1) have degree ≤ `d`, constraint columns are
constants. -/
theorem BW_homMatrix_entry_natDegree_le_of_branch {F : Type} [Field F]
    {ι : Type} [Fintype ι] (e k : ℕ) (ωs : ι → F) (g : ι → F[X]) (d : ℕ)
    (hd : ∀ i, (g i).natDegree ≤ d) (i : ι) (j : Fin ((e + 1) + (e + k))) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X])) g i j).natDegree
      ≤ (if j.1 < e + 1 then d else 0) := by
  classical
  by_cases hj : (j.1 < e + 1)
  · simp only [BW_homMatrix, Matrix.of_apply, hj, ↓reduceIte]
    calc ((g i) * (Polynomial.C (ωs i)) ^ j.1).natDegree
        ≤ (g i).natDegree + ((Polynomial.C (ωs i)) ^ j.1).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ d + 0 := by
          refine Nat.add_le_add (hd i) ?_
          exact Polynomial.natDegree_pow_le_of_le j.1
            (le_of_eq (Polynomial.natDegree_C (ωs i)))
      _ = d := Nat.add_zero d
  · simp only [BW_homMatrix, Matrix.of_apply, hj, ↓reduceIte, Polynomial.natDegree_neg]
    calc ((Polynomial.C (ωs i)) ^ (j.1 - (e + 1))).natDegree
        ≤ (j.1 - (e + 1)) * (Polynomial.C (ωs i)).natDegree := Polynomial.natDegree_pow_le
      _ = 0 := by simp [Polynomial.natDegree_C]


open Polynomial in
/-- General per-column degree accounting for determinants (subsumes the fixed
`d`/`d·n` bounds): if every entry of column `j` has degree ≤ `b j`, the
determinant has degree ≤ `∑ j, b j`. This is the single abstraction behind all
the [BCIKS20] §4/§6.1 minor-degree bounds. -/
theorem natDegree_det_le_sum_col_bounds {F : Type} [Field F] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) F[X]) (b : Fin n → ℕ)
    (hb : ∀ i j, (A i j).natDegree ≤ b j) :
    (Matrix.det A).natDegree ≤ ∑ j, b j := by
  classical
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (f := fun σ => (Equiv.Perm.sign σ : Units ℤ) • (∏ i, A (σ i) i)) ?_
  intro σ _
  have hsign : ((Equiv.Perm.sign σ : Units ℤ) • (∏ i, A (σ i) i)).natDegree
      ≤ (∏ i, A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simp [hs]
    · simp [hs]
  refine le_trans hsign (le_trans ?_ (Finset.sum_le_sum (fun j _ => hb (σ j) j)))
  simpa using Polynomial.natDegree_prod_le
    (s := (Finset.univ : Finset (Fin n))) (f := fun i => A (σ i) i)

open Polynomial in
/-- Degree-`d` generalization of `BW_homMatrix_det_updateCol_natDegree_le_of_ge`:
replacing a CONSTRAINT column (index ≥ e+1) of a BW minor over degree-≤`d` words
by a constant unit column keeps the determinant degree ≤ `d * (e + 1)`. -/
theorem BW_homMatrix_det_updateCol_natDegree_le_of_natDegree_le_of_ge {F : Type} [Field F]
    {ι : Type} [Fintype ι] (e k : ℕ) (ωs : ι → F) (g : ι → F[X]) (d : ℕ)
    (hd : ∀ i, (g i).natDegree ≤ d) (r : Fin ((e + 1) + (e + k)) → ι)
    (i0 : Fin ((e + 1) + (e + k))) (j : Fin ((e + 1) + (e + k))) (hj : e + 1 ≤ j.1) :
    (Matrix.det
        (Matrix.updateCol
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X])) g) r id)
          j (Pi.single i0 (1 : F[X])))).natDegree ≤ d * (e + 1) := by
  classical
  have hb : ∀ i' j' : Fin ((e + 1) + (e + k)),
      ((Matrix.updateCol
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X])) g) r id)
          j (Pi.single i0 (1 : F[X]))) i' j').natDegree
        ≤ (if j'.1 < e + 1 then d else 0) := by
    intro i' j'
    by_cases hje : j' = j
    · subst hje
      have : ¬ (j'.1 < e + 1) := not_lt.mpr hj
      simp only [Matrix.updateCol_apply, this, ↓reduceIte]
      rcases eq_or_ne i' i0 with h | h <;> simp [Pi.single, Function.update, h]
    · simp only [Matrix.updateCol_apply, if_neg hje, Matrix.submatrix_apply, id]
      exact BW_homMatrix_entry_natDegree_le_of_branch e k ωs g d hd (r i') j'
  refine le_trans (natDegree_det_le_sum_col_bounds _ _ _ hb) ?_
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul]
  have hcard : #{j' : Fin ((e + 1) + (e + k)) | j'.1 < e + 1} = e + 1 := by
    have := Fin_sum_ite_lt_e_add_one e k
    simpa [Nat.lt_succ_iff] using this
  rw [hcard, mul_comm]


open Polynomial in
/-- Degree-`d` generalization of `BW_homMatrix_det_updateCol_natDegree_le_of_lt`:
replacing an EVALUATION column (index < e+1) of a BW minor over degree-≤`d`
words by a constant unit column drops the determinant degree to ≤ `d * e`. -/
theorem BW_homMatrix_det_updateCol_natDegree_le_of_natDegree_le_of_lt {F : Type} [Field F]
    {ι : Type} [Fintype ι] (e k : ℕ) (ωs : ι → F) (g : ι → F[X]) (d : ℕ)
    (hd : ∀ i, (g i).natDegree ≤ d) (r : Fin ((e + 1) + (e + k)) → ι)
    (i0 : Fin ((e + 1) + (e + k))) (j : Fin ((e + 1) + (e + k))) (hj : j.1 < e + 1) :
    (Matrix.det
        (Matrix.updateCol
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X])) g) r id)
          j (Pi.single i0 (1 : F[X])))).natDegree ≤ d * e := by
  classical
  have hb : ∀ i' j' : Fin ((e + 1) + (e + k)),
      ((Matrix.updateCol
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X])) g) r id)
          j (Pi.single i0 (1 : F[X]))) i' j').natDegree
        ≤ (if j'.1 ≤ e ∧ j' ≠ j then d else 0) := by
    intro i' j'
    by_cases hje : j' = j
    · subst hje
      simp only [Matrix.updateCol_apply]
      have : ¬ (j'.1 ≤ e ∧ j' ≠ j') := by simp
      rw [if_neg this]
      rcases eq_or_ne i' i0 with h | h <;> simp [Pi.single, Function.update, h]
    · simp only [Matrix.updateCol_apply, if_neg hje, Matrix.submatrix_apply, id]
      refine le_trans (BW_homMatrix_entry_natDegree_le_of_branch e k ωs g d hd (r i') j') ?_
      by_cases hlt : (j'.1 < e + 1)
      · rw [if_pos hlt, if_pos ⟨Nat.lt_succ_iff.mp hlt, hje⟩]
      · rw [if_neg hlt]
        exact Nat.zero_le _
  refine le_trans (natDegree_det_le_sum_col_bounds _ _ _ hb) ?_
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul]
  have hcard : #{j' : Fin ((e + 1) + (e + k)) | j'.1 ≤ e ∧ j' ≠ j} = e :=
    Fin_sum_ite_lt_and_ne_eq_e e k j (Nat.lt_succ_iff.mp hj)
  rw [hcard, mul_comm]


open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le (e d : ℕ)
    (K : Matrix ι (Fin (e + 1)) F[X])
    (hcard : e + 1 ≤ Fintype.card ι)
    (hdeg : ∀ i j, (K i j).natDegree ≤ d)
    (hdet : ∀ r : Fin (e + 1) → ι, Matrix.det (K.submatrix r id) = 0) :
    ∃ a : Fin (e + 1) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ d * e) ∧ Matrix.mulVec K a = 0 := by
  classical
  let n : ℕ := e + 1
  let P : ℕ → Prop := fun r =>
    ∃ (I : Fin r ↪ ι) (J : Fin r ↪ Fin n), Matrix.det (K.submatrix I J) ≠ (0 : F[X])
  letI : DecidablePred P := Classical.decPred _
  have P0 : P 0 := by
    refine ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, ?_⟩
    simp
  let r : ℕ := Nat.findGreatest P n
  have Pr : P r := by
    simpa [r] using
      (Nat.findGreatest_spec (P := P) (n := n) (m := 0) (Nat.zero_le n) P0)
  rcases Pr with ⟨I, J, hdetIJ⟩
  have hnotPn : ¬ P n := by
    intro hPn
    rcases hPn with ⟨I0, J0, hdet0⟩
    let A : Matrix (Fin n) (Fin n) F[X] := K.submatrix I0 id
    have hdetA : Matrix.det A = 0 := by
      simpa [A] using hdet I0
    have hdet_sub : Matrix.det (A.submatrix (Function.Embedding.refl _) J0) = 0 :=
      RS_det_submatrix_eq_zero_of_det_eq_zero n A hdetA (Function.Embedding.refl _) J0
    have hdetK : Matrix.det (K.submatrix I0 J0) = 0 := by
      change Matrix.det (K.submatrix I0 J0) = 0 at hdet_sub
      exact hdet_sub
    exact hdet0 hdetK
  have hrle : r ≤ n := by
    simpa [r] using (Nat.findGreatest_le (P := P) n)
  have hrne : r ≠ n := by
    intro hre
    have hEq : Nat.findGreatest P n = n := by
      simpa [r] using hre
    have hcond : n ≠ 0 → P n :=
      (Nat.findGreatest_eq_iff (P := P) (k := n) (m := n)).1 hEq |>.2.1
    have hn0 : n ≠ 0 := by
      simp [n]
    exact hnotPn (hcond hn0)
  have hrlt : r < n := Nat.lt_of_le_of_ne hrle hrne
  have hrle_e : r ≤ e := by
    have : r < e + 1 := by
      simpa [n] using hrlt
    exact Nat.lt_succ_iff.mp this
  have hcard' : n ≤ Fintype.card ι := by
    simpa [n] using hcard
  have hrltcardι : r < Fintype.card ι := lt_of_lt_of_le hrlt hcard'
  -- pick i0 ∉ range I
  let sI : Finset ι := Finset.univ.map I
  have hsIlt : sI.card < (Finset.univ : Finset ι).card := by
    simpa [sI] using hrltcardι
  obtain ⟨i0, -, hi0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsIlt
  have hi0 : i0 ∉ Set.range I := by
    intro hi
    rcases hi with ⟨i, rfl⟩
    apply hi0_notmem
    refine Finset.mem_map.2 ?_
    refine ⟨i, by simp, rfl⟩
  -- pick j0 ∉ range J
  let sJ : Finset (Fin n) := Finset.univ.map J
  have hsJlt : sJ.card < (Finset.univ : Finset (Fin n)).card := by
    simpa [sJ] using hrlt
  obtain ⟨j0, -, hj0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsJlt
  have hj0 : j0 ∉ Set.range J := by
    intro hj
    rcases hj with ⟨j, rfl⟩
    apply hj0_notmem
    refine Finset.mem_map.2 ?_
    refine ⟨j, by simp, rfl⟩
  let I' : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi0
  let J' : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc J hj0
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) F[X] := K.submatrix I' J'
  have hnotPr1 : ¬ P (r + 1) := by
    have hk : Nat.findGreatest P n < r + 1 := by
      simp [r]
    have hkb : r + 1 ≤ n := Nat.succ_le_of_lt hrlt
    exact Nat.findGreatest_is_greatest (P := P) (n := n) (k := r + 1) hk hkb
  have hdetB : Matrix.det B = 0 := by
    by_contra hne
    have : P (r + 1) := ⟨I', J', by simpa [B] using hne⟩
    exact hnotPr1 this
  let u : Fin (r + 1) → F[X] := fun t => B.adjugate t (Fin.last r)
  have hBu : Matrix.mulVec B u = 0 := by
    simpa [u] using
      RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n := r + 1) (A := B) (j := Fin.last r) hdetB
  have hsub_cast : B.submatrix Fin.castSucc Fin.castSucc = K.submatrix I J := by
    funext i
    funext j
    simp [B, I', J']
  have hu_last : u (Fin.last r) =
      (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) := by
    simpa [u] using RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n := r) (B := B)
  have hu_last_ne : u (Fin.last r) ≠ (0 : F[X]) := by
    have hsign : (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) ≠ (0 : F[X]) := by
      have hminus1 : (-1 : F[X]) ≠ (0 : F[X]) := by simp
      exact pow_ne_zero _ hminus1
    have hdetMinor : Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) ≠ (0 : F[X]) := by
      simpa [hsub_cast] using hdetIJ
    rw [hu_last]
    exact mul_ne_zero hsign hdetMinor
  -- degree bound on u
  have hdeg_u : ∀ t : Fin (r + 1), (u t).natDegree ≤ d * r := by
    intro t
    have hu_t : u t =
        (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)) *
          Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
      simpa [u] using RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := r) (B := B) (t := t)
    have hdeg_det : (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ d * r := by
      apply RS_natDegree_det_le_of_entry_natDegree_le (n := r) (d := d)
        (A := B.submatrix Fin.castSucc t.succAbove)
      intro i j
      -- entries come from K
      simpa [B] using hdeg (I' (Fin.castSucc i)) (J' (t.succAbove j))
    have hdeg_sign : ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree = 0 := by
      simp
    have hmul_le :
        (u t).natDegree ≤
          ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree +
            (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree := by
      simpa [hu_t] using
        (Polynomial.natDegree_mul_le
          (p := (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)))
          (q := Matrix.det (B.submatrix Fin.castSucc t.succAbove)))
    have hdeg_rhs :
        ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree +
            (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ d * r := by
      simpa [hdeg_sign] using hdeg_det
    exact le_trans hmul_le hdeg_rhs
  -- extend u to all columns
  let a : Fin n → F[X] := Function.extend (J' : Fin (r + 1) → Fin n) u (fun _ => 0)
  have ha_on : ∀ t : Fin (r + 1), a (J' t) = u t := by
    intro t
    simpa [a] using (J'.injective.extend_apply u (fun _ => 0) t)
  have ha_ne : a ≠ 0 := by
    intro ha0
    have hval : a (J' (Fin.last r)) = 0 := by
      simpa using congrArg (fun f : Fin n → F[X] => f (J' (Fin.last r))) ha0
    have : u (Fin.last r) = 0 := by
      simpa [ha_on (Fin.last r)] using hval
    exact hu_last_ne this
  have hdeg_a : ∀ j : Fin n, (a j).natDegree ≤ d * e := by
    intro j
    by_cases hj : ∃ t : Fin (r + 1), J' t = j
    · rcases hj with ⟨t, rfl⟩
      exact le_trans (by simpa [ha_on t] using hdeg_u t) (Nat.mul_le_mul_left d hrle_e)
    · have haj : a j = 0 := by
        simpa [a] using
          (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
            (b := j) hj)
      simp [haj]
  have hmul_formula (i : ι) : Matrix.mulVec K a i = ∑ t : Fin (r + 1), K i (J' t) * u t := by
    have hsum : (∑ t : Fin (r + 1), K i (J' t) * u t) = ∑ j : Fin n, K i j * a j := by
      refine (Fintype.sum_of_injective (e := (J' : Fin (r + 1) → Fin n)) (he := J'.injective)
        (f := fun t : Fin (r + 1) => K i (J' t) * u t)
        (g := fun j : Fin n => K i j * a j) ?_ ?_)
      · intro j hj
        have hb : ¬∃ t : Fin (r + 1), (J' t) = j := by
          simpa [Set.mem_range] using hj
        have haj : a j = 0 := by
          simpa [a] using
            (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
              (b := j) hb)
        simp [haj]
      · intro t
        simp [ha_on t]
    simpa [Matrix.mulVec, dotProduct] using hsum.symm
  have hmulVec : Matrix.mulVec K a = 0 := by
    funext i
    by_cases hi : i ∈ Set.range I
    · rcases hi with ⟨t, rfl⟩
      have hrow : (Matrix.mulVec B u) (Fin.castSucc t) = 0 := by
        have := congrArg (fun v : Fin (r + 1) → F[X] => v (Fin.castSucc t)) hBu
        simpa using this
      have hrow' : (∑ x : Fin (r + 1), K (I t) (J' x) * u x) = 0 := by
        simpa [Matrix.mulVec, dotProduct, B, I', J'] using hrow
      rw [hmul_formula (i := I t)]
      simpa using hrow'
    · -- i ∉ range I
      have hi' : i ∉ Set.range I := hi
      let Ii : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi'
      have hdetBi : Matrix.det (K.submatrix Ii J') = 0 := by
        by_contra hne
        have : P (r + 1) := ⟨Ii, J', by simpa using hne⟩
        exact hnotPr1 this
      let b : Fin (r + 1) → F[X] := fun j => K i (J' j)
      have hupdate : B.updateRow (Fin.last r) b = K.submatrix Ii J' := by
        funext x
        funext y
        refine Fin.lastCases (motive := fun x => (B.updateRow (Fin.last r) b) x y =
            (K.submatrix Ii J') x y) ?_ ?_ x
        · -- x = last
          simp [Matrix.updateRow_apply, b, B, Ii, I', J']
        · intro x
          simp [Matrix.updateRow_apply, b, B, Ii, I', J']
      have hdet_update : Matrix.det (B.updateRow (Fin.last r) b) = 0 := by
        simpa [hupdate] using hdetBi
      have hdet_expr : Matrix.det (B.updateRow (Fin.last r) b) =
          ∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r) := by
        simpa using
          det_updateRow_eq_sum_mul_adjugate_col (A := B) (i := Fin.last r) (b := b)
      have hsum0 : (∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r)) = 0 := by
        simpa [hdet_expr] using hdet_update
      have hsum0' : (∑ j : Fin (r + 1), K i (J' j) * u j) = 0 := by
        simpa [b, u] using hsum0
      rw [hmul_formula (i := i)]
      simpa using hsum0'
  refine ⟨a, ha_ne, ?_, hmulVec⟩
  intro t
  simpa using hdeg_a t


end CoreResults

end ProximityGap
