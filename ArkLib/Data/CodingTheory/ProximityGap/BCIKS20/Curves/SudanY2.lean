/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.JointAgreement

/-!
# Wide-kernel (Sudan) curve Berlekamp–Welch past the unique-decoding radius ([BCIKS20] §6)

The multiplicity-1 curve Berlekamp–Welch is stuck at `δ ≤` the unique-decoding radius (its
square-determinant argument needs `2e < d`). This file provides the Sudan (`Y`-degree ≥ 2)
replacement: `exists_nonzero_kernelVec_wide_natDegree_le` gives a degree-bounded nonzero kernel
vector of a *wide* matrix over `F[X]` (`|ι| < N`) via a `findGreatest`/adjugate full-row-rank
argument — with **no unique-decoding-radius hypothesis**. `exists_kernelVec_BW_homMatrixY2_curve_of_dim`
instantiates it for the `Y`-degree-2 curve interpolation matrix (pure Sudan dimension count
`N₂ > |ι|`). Infrastructure toward strict-Johnson curve list-decoding (`RSCurveListSizeResidual`).
-/
open ProximityGap Polynomial Matrix

namespace ProximityGap

set_option linter.unusedSectionVars false
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
theorem exists_nonzero_kernelVec_wide_natDegree_le {N d : ℕ}
    (K : Matrix ι (Fin N) F[X])
    (hN : Fintype.card ι < N)
    (hdeg : ∀ i j, (K i j).natDegree ≤ d) :
    ∃ a : Fin N → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ d * Fintype.card ι) ∧ Matrix.mulVec K a = 0 := by
  classical
  set nι : ℕ := Fintype.card ι with hnι
  let P : ℕ → Prop := fun r =>
    ∃ (I : Fin r ↪ ι) (J : Fin r ↪ Fin N), Matrix.det (K.submatrix I J) ≠ (0 : F[X])
  letI : DecidablePred P := Classical.decPred _
  have P0 : P 0 := ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, by simp⟩
  let r : ℕ := Nat.findGreatest P nι
  have Pr : P r := by
    simpa [r] using (Nat.findGreatest_spec (P := P) (n := nι) (m := 0) (Nat.zero_le nι) P0)
  rcases Pr with ⟨I, J, hdetIJ⟩
  have hrle : r ≤ nι := by simpa [r] using (Nat.findGreatest_le (P := P) nι)
  have hrltN : r < N := lt_of_le_of_lt hrle hN
  have hnotPr1 : ¬ P (r + 1) := by
    rcases lt_or_eq_of_le hrle with hlt | heq
    · have hk : Nat.findGreatest P nι < r + 1 := by simp [r]
      have hkb : r + 1 ≤ nι := Nat.succ_le_of_lt hlt
      exact Nat.findGreatest_is_greatest (P := P) (n := nι) (k := r + 1) hk hkb
    · rintro ⟨I0, J0, _⟩
      have : Fintype.card (Fin (r + 1)) ≤ Fintype.card ι := Fintype.card_le_of_embedding I0
      simp only [Fintype.card_fin] at this; omega
  let sJ : Finset (Fin N) := Finset.univ.map J
  have hsJlt : sJ.card < (Finset.univ : Finset (Fin N)).card := by
    simpa [sJ, Fintype.card_fin] using hrltN
  obtain ⟨j0, -, hj0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsJlt
  have hj0 : j0 ∉ Set.range J := by
    intro hj; rcases hj with ⟨j, rfl⟩
    exact hj0_notmem (Finset.mem_map.2 ⟨j, by simp, rfl⟩)
  -- ROW handling: need spare row OR full rank. We unify by always using a spare row
  -- when r < nι. When r = nι there is no spare row; but then range I = ι and we can
  -- use ANY i0 (the kernel equation for rows in range I suffices). Handle via:
  -- pick i0 from a spare row if r<nι, else (r=nι) the "outside range I" branch is vacuous.
  by_cases hrn : r < nι
  · -- ===== CASE r < nι: spare row exists =====
    let sI : Finset ι := Finset.univ.map I
    have hsIlt : sI.card < (Finset.univ : Finset ι).card := by simpa [sI] using hrn
    obtain ⟨i0, -, hi0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsIlt
    have hi0 : i0 ∉ Set.range I := by
      intro hi; rcases hi with ⟨i, rfl⟩
      exact hi0_notmem (Finset.mem_map.2 ⟨i, by simp, rfl⟩)
    let I' : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi0
    let J' : Fin (r + 1) ↪ Fin N := Fin.Embedding.snoc J hj0
    let B : Matrix (Fin (r + 1)) (Fin (r + 1)) F[X] := K.submatrix I' J'
    have hdetB : Matrix.det B = 0 := by
      by_contra hne; exact hnotPr1 ⟨I', J', by simpa [B] using hne⟩
    let u : Fin (r + 1) → F[X] := fun t => B.adjugate t (Fin.last r)
    have hBu : Matrix.mulVec B u = 0 := by
      simpa [u] using
        RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n := r + 1) (A := B) (j := Fin.last r) hdetB
    have hsub_cast : B.submatrix Fin.castSucc Fin.castSucc = K.submatrix I J := by
      funext i j; simp [B, I', J']
    have hu_last : u (Fin.last r) =
        (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) *
          Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) := by
      simpa [u] using RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n := r) (B := B)
    have hu_last_ne : u (Fin.last r) ≠ (0 : F[X]) := by
      have hsign : (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) ≠ (0 : F[X]) :=
        pow_ne_zero _ (by simp)
      have hdetMinor : Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) ≠ (0 : F[X]) := by
        simpa [hsub_cast] using hdetIJ
      rw [hu_last]; exact mul_ne_zero hsign hdetMinor
    have hdeg_u : ∀ t : Fin (r + 1), (u t).natDegree ≤ d * r := by
      intro t
      have hu_t : u t =
          (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)) *
            Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
        simpa [u] using RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := r) (B := B) (t := t)
      have hdeg_det : (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ d * r := by
        apply RS_natDegree_det_le_of_entry_natDegree_le (n := r) (d := d)
        intro i j; simpa [B] using hdeg (I' (Fin.castSucc i)) (J' (t.succAbove j))
      have hmul_le :
          (u t).natDegree ≤
            ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree +
              (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree := by
        simpa [hu_t] using
          (Polynomial.natDegree_mul_le
            (p := (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)))
            (q := Matrix.det (B.submatrix Fin.castSucc t.succAbove)))
      have : ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree = 0 := by simp
      omega
    -- extend u to all columns of K
    let a : Fin N → F[X] := Function.extend (J' : Fin (r + 1) → Fin N) u (fun _ => 0)
    have ha_on : ∀ t : Fin (r + 1), a (J' t) = u t := fun t => by
      simpa [a] using (J'.injective.extend_apply u (fun _ => 0) t)
    have ha_ne : a ≠ 0 := by
      intro ha0
      have hval : a (J' (Fin.last r)) = 0 := by
        simpa using congrArg (fun f : Fin N → F[X] => f (J' (Fin.last r))) ha0
      exact hu_last_ne (by simpa [ha_on (Fin.last r)] using hval)
    have hdeg_a : ∀ j : Fin N, (a j).natDegree ≤ d * nι := by
      intro j
      by_cases hj : ∃ t : Fin (r + 1), J' t = j
      · rcases hj with ⟨t, rfl⟩
        exact le_trans (by simpa [ha_on t] using hdeg_u t) (Nat.mul_le_mul_left d hrle)
      · have haj : a j = 0 := by
          simpa [a] using
            (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin N)) (g := u) (e' := fun _ => 0)
              (b := j) hj)
        simp [haj]
    have hmul_formula (i : ι) : Matrix.mulVec K a i = ∑ t : Fin (r + 1), K i (J' t) * u t := by
      have hsum : (∑ t : Fin (r + 1), K i (J' t) * u t) = ∑ j : Fin N, K i j * a j := by
        refine (Fintype.sum_of_injective (e := (J' : Fin (r + 1) → Fin N)) (he := J'.injective)
          (f := fun t : Fin (r + 1) => K i (J' t) * u t)
          (g := fun j : Fin N => K i j * a j) ?_ ?_)
        · intro j hj
          have hb : ¬∃ t : Fin (r + 1), (J' t) = j := by simpa [Set.mem_range] using hj
          have haj : a j = 0 := by
            simpa [a] using
              (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin N)) (g := u) (e' := fun _ => 0)
                (b := j) hb)
          simp [haj]
        · intro t; simp [ha_on t]
      simpa [Matrix.mulVec] using hsum.symm
    have hmulVec : Matrix.mulVec K a = 0 := by
      funext i
      by_cases hi : i ∈ Set.range I
      · rcases hi with ⟨t, rfl⟩
        have hrow : (Matrix.mulVec B u) (Fin.castSucc t) = 0 := by
          simpa using congrArg (fun v : Fin (r + 1) → F[X] => v (Fin.castSucc t)) hBu
        have hrow' : (∑ x : Fin (r + 1), K (I t) (J' x) * u x) = 0 := by
          simpa [Matrix.mulVec, B, I', J'] using hrow
        rw [hmul_formula (i := I t)]; simpa using hrow'
      · have hi' : i ∉ Set.range I := hi
        let Ii : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi'
        have hdetBi : Matrix.det (K.submatrix Ii J') = 0 := by
          by_contra hne; exact hnotPr1 ⟨Ii, J', by simpa using hne⟩
        let b : Fin (r + 1) → F[X] := fun j => K i (J' j)
        have hupdate : B.updateRow (Fin.last r) b = K.submatrix Ii J' := by
          funext x y
          refine Fin.lastCases (motive := fun x => (B.updateRow (Fin.last r) b) x y =
              (K.submatrix Ii J') x y) ?_ ?_ x
          · simp [Matrix.updateRow_apply, b, B, Ii, I', J']
          · intro x; simp [Matrix.updateRow_apply, b, B, Ii, I', J']
        have hdet_update : Matrix.det (B.updateRow (Fin.last r) b) = 0 := by
          simpa [hupdate] using hdetBi
        have hdet_expr : Matrix.det (B.updateRow (Fin.last r) b) =
            ∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r) := by
          simpa using det_updateRow_eq_sum_mul_adjugate_col (A := B) (i := Fin.last r) (b := b)
        have hsum0' : (∑ j : Fin (r + 1), K i (J' j) * u j) = 0 := by
          simpa [b, u] using (by simpa [hdet_expr] using hdet_update :
            (∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r)) = 0)
        rw [hmul_formula (i := i)]; simpa using hsum0'
    exact ⟨a, ha_ne, fun t => hdeg_a t, hmulVec⟩
  · -- ===== CASE r = nι: full row rank =====
    have hrEq : r = nι := le_antisymm hrle (Nat.le_of_not_lt hrn)
    have hnιpos : 0 < nι := by rw [hnι]; exact Fintype.card_pos (α := ι)
    -- I : Fin r ↪ ι with r = card ι, so I is surjective
    have hIsurj : Function.Surjective (I ∘ (Fin.cast hrEq.symm)) := by
      have hbij : Function.Bijective (I ∘ (Fin.cast hrEq.symm)) := by
        rw [Fintype.bijective_iff_injective_and_card]
        refine ⟨(I.injective).comp (Fin.cast_injective _), ?_⟩
        simp [hnι]
      exact hbij.2
    let z0 : Fin r := ⟨0, by omega⟩
    let J' : Fin (r + 1) ↪ Fin N := Fin.Embedding.snoc J hj0
    let ρ : Fin (r + 1) → ι := fun t => Fin.lastCases (I z0) (fun s => I s) t
    let B : Matrix (Fin (r + 1)) (Fin (r + 1)) F[X] := Matrix.of fun s t => K (ρ s) (J' t)
    have hrep : B (Fin.last r) = B (Fin.castSucc z0) := by
      funext t; simp only [B, Matrix.of_apply, ρ]; rw [Fin.lastCases_last, Fin.lastCases_castSucc]
    have hne_idx : (Fin.last r) ≠ (Fin.castSucc z0) := by
      rw [ne_eq, Fin.last, Fin.castSucc, Fin.ext_iff]; simp [z0, Fin.castAdd]; omega
    have hdetB : Matrix.det B = 0 := Matrix.det_zero_of_row_eq hne_idx hrep
    let u : Fin (r + 1) → F[X] := fun t => B.adjugate t (Fin.last r)
    have hBu : Matrix.mulVec B u = 0 := by
      simpa [u] using
        RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n := r + 1) (A := B) (j := Fin.last r) hdetB
    have hsub_cast : B.submatrix Fin.castSucc Fin.castSucc = K.submatrix I J := by
      funext s t
      simp only [B, Matrix.submatrix_apply, Matrix.of_apply, ρ, J']
      rw [Fin.lastCases_castSucc]; congr 1; simp [Fin.Embedding.snoc]
    have hu_last : u (Fin.last r) =
        (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) *
          Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) := by
      simpa [u] using RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n := r) (B := B)
    have hu_last_ne : u (Fin.last r) ≠ (0 : F[X]) := by
      have hsign : (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) ≠ (0 : F[X]) :=
        pow_ne_zero _ (by simp)
      have hdetMinor : Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) ≠ (0 : F[X]) := by
        simpa [hsub_cast] using hdetIJ
      rw [hu_last]; exact mul_ne_zero hsign hdetMinor
    have hdeg_u : ∀ t : Fin (r + 1), (u t).natDegree ≤ d * nι := by
      intro t
      have hu_t : u t =
          (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)) *
            Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
        simpa [u] using RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := r) (B := B) (t := t)
      have hdeg_det : (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ d * r := by
        apply RS_natDegree_det_le_of_entry_natDegree_le (n := r) (d := d)
        intro i j; simpa [B] using hdeg (ρ (Fin.castSucc i)) (J' (t.succAbove j))
      have hmul_le :
          (u t).natDegree ≤
            ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree +
              (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree := by
        simpa [hu_t] using
          (Polynomial.natDegree_mul_le (p := (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)))
            (q := Matrix.det (B.submatrix Fin.castSucc t.succAbove)))
      have hz : ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree = 0 := by simp
      have : (u t).natDegree ≤ d * r := by omega
      calc (u t).natDegree ≤ d * r := this
        _ ≤ d * nι := Nat.mul_le_mul_left d hrle
    let a : Fin N → F[X] := Function.extend (J' : Fin (r + 1) → Fin N) u (fun _ => 0)
    have ha_on : ∀ t : Fin (r + 1), a (J' t) = u t := fun t => by
      simpa [a] using (J'.injective.extend_apply u (fun _ => 0) t)
    have ha_ne : a ≠ 0 := by
      intro ha0
      have hval : a (J' (Fin.last r)) = 0 := by
        simpa using congrArg (fun f : Fin N → F[X] => f (J' (Fin.last r))) ha0
      exact hu_last_ne (by simpa [ha_on (Fin.last r)] using hval)
    have hdeg_a : ∀ j : Fin N, (a j).natDegree ≤ d * nι := by
      intro j
      by_cases hj : ∃ t : Fin (r + 1), J' t = j
      · rcases hj with ⟨t, rfl⟩; simpa [ha_on t] using hdeg_u t
      · have haj : a j = 0 := by
          simpa [a] using
            (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin N)) (g := u) (e' := fun _ => 0)
              (b := j) hj)
        simp [haj]
    have hmul_formula (i : ι) : Matrix.mulVec K a i = ∑ t : Fin (r + 1), K i (J' t) * u t := by
      have hsum : (∑ t : Fin (r + 1), K i (J' t) * u t) = ∑ j : Fin N, K i j * a j := by
        refine (Fintype.sum_of_injective (e := (J' : Fin (r + 1) → Fin N)) (he := J'.injective)
          (f := fun t : Fin (r + 1) => K i (J' t) * u t)
          (g := fun j : Fin N => K i j * a j) ?_ ?_)
        · intro j hj
          have hb : ¬∃ t : Fin (r + 1), (J' t) = j := by simpa [Set.mem_range] using hj
          have haj : a j = 0 := by
            simpa [a] using
              (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin N)) (g := u) (e' := fun _ => 0)
                (b := j) hb)
          simp [haj]
        · intro t; simp [ha_on t]
      simpa [Matrix.mulVec] using hsum.symm
    have hmulVec : Matrix.mulVec K a = 0 := by
      funext i
      obtain ⟨t, rfl⟩ := hIsurj i
      have hrow : (Matrix.mulVec B u) (Fin.castSucc (Fin.cast hrEq.symm t)) = 0 := by
        simpa using congrArg (fun v : Fin (r + 1) → F[X] => v (Fin.castSucc (Fin.cast hrEq.symm t))) hBu
      have hrow' : (∑ x : Fin (r + 1), K (I (Fin.cast hrEq.symm t)) (J' x) * u x) = 0 := by
        have h0 : (∑ x : Fin (r + 1), B (Fin.castSucc (Fin.cast hrEq.symm t)) x * u x) = 0 := by
          simpa [Matrix.mulVec, dotProduct] using hrow
        have hBeq : ∀ x, B (Fin.castSucc (Fin.cast hrEq.symm t)) x = K (I (Fin.cast hrEq.symm t)) (J' x) := by
          intro x; simp only [B, Matrix.of_apply, ρ]; rw [Fin.lastCases_castSucc]
        simpa [hBeq] using h0
      rw [hmul_formula (i := (I ∘ (Fin.cast hrEq.symm)) t)]
      simpa using hrow'
    exact ⟨a, ha_ne, fun t => hdeg_a t, hmulVec⟩


-- ===== Y-degree-2 curve interpolation matrix =====
def BW_homMatrixY2 {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    (e0 e1 e2 : ℕ) (ωs : ι → R) (f : ι → R) :
    Matrix ι (Fin ((e0 + 1) + (e1 + 1) + (e2 + 1))) R :=
  Matrix.of fun i j =>
    if _ : j.1 < e0 + 1 then (ωs i) ^ j.1
    else if _ : j.1 < (e0 + 1) + (e1 + 1) then f i * (ωs i) ^ (j.1 - (e0 + 1))
    else (f i)^2 * (ωs i) ^ (j.1 - ((e0 + 1) + (e1 + 1)))

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] in
theorem BW_homMatrixY2_entry_natDegree_le
    (e0 e1 e2 k : ℕ) (ωs : ι → F) (g : ι → F[X]) (hg : ∀ i, (g i).natDegree ≤ k)
    (i : ι) (j : Fin ((e0+1)+(e1+1)+(e2+1))) :
    (BW_homMatrixY2 (ι := ι) e0 e1 e2 (fun i => (Polynomial.C (ωs i) : F[X])) g i j).natDegree
      ≤ 2 * k := by
  classical
  simp only [BW_homMatrixY2, Matrix.of_apply]
  split
  · rw [← Polynomial.C_pow]; simp
  · split
    · rw [← Polynomial.C_pow]
      calc (g i * Polynomial.C (ωs i ^ _)).natDegree
          ≤ (g i).natDegree + (Polynomial.C (ωs i ^ _) : F[X]).natDegree := Polynomial.natDegree_mul_le
        _ ≤ k + 0 := by gcongr; exact hg i; simp
        _ ≤ 2 * k := by omega
    · rw [← Polynomial.C_pow]
      calc ((g i)^2 * Polynomial.C (ωs i ^ _)).natDegree
          ≤ ((g i)^2).natDegree + (Polynomial.C (ωs i ^ _) : F[X]).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 2 * k + 0 := by
              gcongr
              · calc ((g i)^2).natDegree ≤ 2 * (g i).natDegree := by
                      rw [sq]; exact le_trans Polynomial.natDegree_mul_le (by omega)
                    _ ≤ 2 * k := by gcongr; exact hg i
              · simp
        _ ≤ 2 * k := by omega

/-- **Y-degree-2 (Sudan) curve interpolant existence, beyond the unique-decoding wall.**
For a degree-`k` curve word `g i = ∑ₜ C(u t i) Xᵗ` (X = curve parameter), the Y-degree-2
homogeneous interpolation matrix over `F[X]` has a nonzero kernel of bounded X-degree
whenever the column count exceeds `|ι|` (the Sudan feasibility `N₂ > n`).
The resulting kernel `(a₀, a₁, a₂)` are the X-coefficient vectors of the bivariate
interpolant `Q(X,Y) = B₀(X) + Y·B₁(X) + Y²·B₂(X)` vanishing on the curve at every point.
NO unique-decoding-radius hypothesis: `e0, e1, e2` are free, so the radius can be chosen
strictly beyond `(1-ρ)/2` (Sudan crosses UDR; verified arithmetically). -/
theorem exists_kernelVec_BW_homMatrixY2_curve_of_dim
    (e0 e1 e2 k : ℕ) (ωs : ι → F) (g : ι → F[X]) (hg : ∀ i, (g i).natDegree ≤ k)
    (hdim : Fintype.card ι < (e0 + 1) + (e1 + 1) + (e2 + 1)) :
    ∃ a : Fin ((e0 + 1) + (e1 + 1) + (e2 + 1)) → F[X],
      a ≠ 0 ∧
      (∀ t, (a t).natDegree ≤ 2 * k * Fintype.card ι) ∧
      Matrix.mulVec
        (BW_homMatrixY2 (ι := ι) e0 e1 e2 (fun i => (Polynomial.C (ωs i) : F[X])) g) a = 0 := by
  exact exists_nonzero_kernelVec_wide_natDegree_le
    (BW_homMatrixY2 (ι := ι) e0 e1 e2 (fun i => (Polynomial.C (ωs i) : F[X])) g)
    hdim
    (BW_homMatrixY2_entry_natDegree_le (F := F) e0 e1 e2 k ωs g hg)

end ProximityGap
#print axioms ProximityGap.exists_kernelVec_BW_homMatrixY2_curve_of_dim
#print axioms ProximityGap.exists_nonzero_kernelVec_wide_natDegree_le
#print axioms ProximityGap.BW_homMatrixY2_entry_natDegree_le
