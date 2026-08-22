/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.BWMatrix
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Good coefficients for parameterized curves ([BCIKS20] §6.1)

Curves analogue of `AffineLines/GoodCoeffs.lean`: the set of curve parameters
`z` at which the degree-`k` parameterized curve through the words
`u 0, …, u k` is `δ`-close to the Reed–Solomon code, and the per-parameter
close-codeword extraction. The line case is `k = 1`
(`u 0 + z • u 1 = ∑ t : Fin 2, z ^ t • u t`).
-/

namespace ProximityGap

-- Decidability/Fintype instances are threaded through the section; several
-- statement-level extraction lemmas do not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The set of curve parameters `z : F` at which the degree-`k` parameterized
curve through `u 0, …, u k` is `δ`-close to the Reed–Solomon code. Curves
analogue of `RS_goodCoeffs` (the line case is `k = 1`). -/
noncomputable def RS_goodCoeffsCurve {k deg : ℕ} {domain : ι ↪ F}
    (u : WordStack F (Fin (k + 1)) ι) (δ : ℝ≥0) : Finset F :=
  Finset.filter
    (fun z : F =>
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code domain deg) ≤ δ)
    Finset.univ

open Polynomial in
/-- At every good curve parameter there is a codeword polynomial within the
floor-`δ` Hamming radius. Curves analogue of `RS_exists_Pz_of_mem_goodCoeffs`. -/
theorem RS_exists_Pz_of_mem_goodCoeffsCurve {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg] (u : WordStack F (Fin (k + 1)) ι) {z : F}
    (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    ∃ Pz : F[X], Pz.natDegree < deg ∧
      Δ₀(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, Pz.eval ∘ domain)
        ≤ Nat.floor (δ * Fintype.card ι) := by
  classical
  have hrel :
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code domain deg) ≤ δ := by
    simpa [RS_goodCoeffsCurve] using hz
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  have hdist :
      Δ₀(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        (ReedSolomon.code domain deg : Set (ι → F))) ≤ (e : ℕ∞) := by
    have h :=
      (Code.relDistFromCode_le_iff_distFromCode_le
          (u := ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
          (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)).1 hrel
    simpa [e] using h
  rcases
      (Code.closeToCode_iff_closeToCodeword_of_minDist
            (u := ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
            (C := (ReedSolomon.code domain deg : Set (ι → F))) (e := e)).1 hdist with
    ⟨v, hvC, hvdist⟩
  rcases hvC with ⟨Pz, hPz, rfl⟩
  refine ⟨Pz, ?_, ?_⟩
  · exact ReedSolomon.natDegree_lt_of_mem_degreeLT (deg := deg) hPz
  · simpa [e] using hvdist

open scoped BigOperators in
open Polynomial in
theorem RS_exists_kernelVec_BW_homMatrix_eval_of_mem_goodCoeffsCurve
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι) {z : F}
    (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    ∃ a : Fin (e + 1) → F,
      ∃ b : Fin (e + deg) → F,
        a ≠ 0 ∧
          Matrix.mulVec
              (BW_homMatrix (ι := ι) e deg (fun i => domain i)
                (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i))
              (Fin.append a b) = 0 := by
  classical
  -- Unfold the `let e := ...` in the goal, but avoid changing the quantifier structure
  simp only
  -- Name the error bound (this rewrites occurrences of the floor expression)
  set e : ℕ := Nat.floor (δ * Fintype.card ι) with he
  -- Get the close polynomial `Pz`
  obtain ⟨Pz, hPzdeg, hdist⟩ :=
    RS_exists_Pz_of_mem_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) (δ := δ) u (z :=
      z) hz
  have hdist' : Δ₀(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, Pz.eval ∘ domain) ≤ e := by
    simpa [he] using hdist
  -- Extract a small set of disagreement coordinates
  obtain ⟨D, hDcard, hAgree⟩ :=
    (Code.closeToWord_iff_exists_possibleDisagreeCols
        (u := ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
        (v := Pz.eval ∘ domain)
        (e := e)).1 hdist'
  -- Error-locator polynomial and the corresponding `Q`
  set E : F[X] := ∏ i ∈ D, (Polynomial.X - Polynomial.C (domain i)) with hE
  set Q : F[X] := E * Pz with hQ
  -- Coefficient vectors (truncated to the required degrees)
  let a : Fin (e + 1) → F := fun t => E.coeff t.1
  let b : Fin (e + deg) → F := fun s => Q.coeff s.1
  have hE_monic : E.Monic := by
    -- `E` is a product of monic linear factors
    simpa [hE] using (Polynomial.monic_prod_X_sub_C (b := fun i : ι => domain i) (s := D))
  have hE_natDegree : E.natDegree = D.card := by
    -- degree of product of monic polynomials is sum of degrees
    have hdeg :=
      Polynomial.natDegree_prod_of_monic (s := D)
        (f := fun i : ι => (Polynomial.X - Polynomial.C (domain i) : F[X]))
        (by
          intro i hi
          simpa using (Polynomial.monic_X_sub_C (domain i)))
    -- simplify the RHS
    convert hdeg using 1
    simp
  have hE_deg_lt : E.natDegree < e + 1 := by
    have : D.card < e + 1 := Nat.lt_succ_of_le hDcard
    simpa [hE_natDegree] using this
  have hQ_deg_lt : Q.natDegree < e + deg := by
    -- `natDegree (E*Pz) ≤ natDegree E + natDegree Pz`
    have hmul : Q.natDegree ≤ E.natDegree + Pz.natDegree := by
      simpa [hQ] using (Polynomial.natDegree_mul_le (p := E) (q := Pz))
    have hPz_le : Pz.natDegree ≤ deg - 1 := Nat.le_pred_of_lt hPzdeg
    have hE_le : E.natDegree ≤ e := by
      simpa [hE_natDegree] using hDcard
    have hsum_le : E.natDegree + Pz.natDegree ≤ e + (deg - 1) := Nat.add_le_add hE_le hPz_le
    have hle : Q.natDegree ≤ e + (deg - 1) := le_trans hmul (by simpa [Nat.add_assoc] using hsum_le)
    -- turn into a strict inequality
    have hdegpos : 0 < deg := Nat.pos_of_neZero deg
    have : e + (deg - 1) < e + deg :=
      Nat.add_lt_add_left (Nat.pred_lt (Nat.ne_of_gt hdegpos)) e
    exact lt_of_le_of_lt hle this
  -- `a` is nonzero because the leading coefficient of `E` is 1
  have ha_ne : a ≠ 0 := by
    have hcard_lt : D.card < e + 1 := Nat.lt_succ_of_le hDcard
    let t0 : Fin (e + 1) := ⟨D.card, hcard_lt⟩
    have hcoeff : E.coeff D.card = 1 := by
      have hlead : E.leadingCoeff = 1 := hE_monic.leadingCoeff
      simpa [Polynomial.leadingCoeff, hE_natDegree] using hlead
    have ht0 : a t0 = 1 := by
      simpa [a, t0] using hcoeff
    intro hzero
    have hz0 : a t0 = 0 := by
      simpa using congrArg (fun f => f t0) hzero
    have h1 : (1 : F) = 0 := by
      rwa [ht0] at hz0
    exact one_ne_zero h1
  refine ⟨a, b, ha_ne, ?_⟩
  -- Show the vector is in the kernel via the characterization lemma
  apply (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (e := e) (k := deg)
      (ωs := fun i => domain i)
      (f := fun i => (∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i))
      (a := a) (b := b)).2
  intro i
  -- Convert the coefficient sums into polynomial evaluations
  have hsum_a : (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) = E.eval (domain i) := by
    have hfin : (∑ t : Fin (e + 1), a t * (domain i) ^ t.1)
        = ∑ n ∈ Finset.range (e + 1), E.coeff n * (domain i) ^ n := by
      simpa [a] using
        (Fin.sum_univ_eq_sum_range (f := fun n : ℕ => E.coeff n * (domain i) ^ n) (n := e + 1))
    have heval : E.eval (domain i) = ∑ n ∈ Finset.range (e + 1), E.coeff n * (domain i) ^ n :=
      Polynomial.eval_eq_sum_range' (p := E) (n := e + 1) hE_deg_lt (domain i)
    simpa [hfin] using heval.symm
  have hsum_b : (∑ s : Fin (e + deg), b s * (domain i) ^ s.1) = Q.eval (domain i) := by
    have hfin : (∑ s : Fin (e + deg), b s * (domain i) ^ s.1)
        = ∑ n ∈ Finset.range (e + deg), Q.coeff n * (domain i) ^ n := by
      simpa [b] using
        (Fin.sum_univ_eq_sum_range (f := fun n : ℕ => Q.coeff n * (domain i) ^ n) (n := e + deg))
    have heval : Q.eval (domain i) = ∑ n ∈ Finset.range (e + deg), Q.coeff n * (domain i) ^ n :=
      Polynomial.eval_eq_sum_range' (p := Q) (n := e + deg) hQ_deg_lt (domain i)
    simpa [hfin] using heval.symm
  -- Reduce to showing `E.eval ω * f = Q.eval ω` and discharge by cases
  by_cases hiD : i ∈ D
  · -- On error positions, `E(ω_i)=0`
    have hE0 : E.eval (domain i) = 0 := by
      -- expand `E` and use that evaluation commutes with products
      rw [hE]
      rw [Polynomial.eval_prod (s := D)
        (p := fun j : ι => (Polynomial.X - Polynomial.C (domain j) : F[X]))
        (x := domain i)]
      refine Finset.prod_eq_zero hiD ?_
      simp
    calc
      (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) * ((∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i))
          = (E.eval (domain i)) * ((∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i)) := by rw [hsum_a]
      _ = 0 := by simp [hE0]
      _ = Q.eval (domain i) := by
            have hmul_eval : Q.eval (domain i) = (E.eval (domain i)) * (Pz.eval (domain i)) := by
              rw [hQ, Polynomial.eval_mul]
            simp [hmul_eval, hE0]
      _ = ∑ s : Fin (e + deg), b s * (domain i) ^ s.1 := by rw [hsum_b]
  · -- On agreement positions, `f_i = Pz(ω_i)`
    have hf_eq : ((∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i)) = Pz.eval (domain i) := by
      have := hAgree i hiD
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    calc
      (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) * ((∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i))
          = (E.eval (domain i)) * ((∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i)) := by rw [hsum_a]
      _ = (E.eval (domain i)) * (Pz.eval (domain i)) := by simp [hf_eq]
      _ = Q.eval (domain i) := by
            rw [hQ, Polynomial.eval_mul]
      _ = ∑ s : Fin (e + deg), b s * (domain i) ^ s.1 := by rw [hsum_b]

open Polynomial in
/-- Evaluation commutes with the BW matrix construction for arbitrary
polynomial words (generic form of `BW_homMatrix_map_evalRingHom`). -/
theorem BW_homMatrix_map_evalRingHom_poly {e k : ℕ} (ωs : ι → F) (g : ι → F[X]) (z : F) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X])) g).map
        (Polynomial.eval z)
      = BW_homMatrix (ι := ι) e k ωs (fun i => (g i).eval z) := by
  ext i j
  by_cases hj : (j.1 ≤ e) <;>
    simp [BW_homMatrix, Matrix.map_apply, hj]

open scoped BigOperators in
open Polynomial in
open Matrix in
/-- Curves analogue of `RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt`
([BCIKS20] §6.1): with more than `k · n` good curve parameters, every square
minor of the BW matrix over the degree-`k` polynomial words vanishes
identically — the minors have degree ≤ `k * (e + 1) ≤ k · n < |S|` and vanish
at every good parameter. -/
theorem RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffsCurve_card_gt
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card
      > k * Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    let N : ℕ := (e + 1) + (e + deg)
    ∀ r : Fin N ↪ ι,
      Matrix.det
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e deg
              (fun i => (Polynomial.C (domain i) : F[X]))
              (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
            r id) = 0 := by
  classical
  dsimp
  intro r
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  let N : ℕ := (e + 1) + (e + deg)
  let S : Finset F := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ
  let g : ι → F[X] := fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)
  have hg : ∀ i, (g i).natDegree ≤ k := by
    intro i
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro t _
    refine le_trans Polynomial.natDegree_mul_le ?_
    simp only [Polynomial.natDegree_C, Polynomial.natDegree_pow, Polynomial.natDegree_X,
      mul_one, Nat.zero_add]
    exact Nat.le_of_lt_succ t.isLt
  let M : Matrix ι (Fin N) F[X] :=
    BW_homMatrix (ι := ι) e deg (fun i => (Polynomial.C (domain i) : F[X])) g
  let A : Matrix (Fin N) (Fin N) F[X] :=
    Matrix.submatrix M (r : Fin N → ι) (id : Fin N → Fin N)
  -- degree bound k(e+1) via the d-generalized minor lemma
  have hdeg_det : (Matrix.det A).natDegree ≤ k * (e + 1) := by
    simpa [A, M, N, e] using
      (BW_homMatrix_det_submatrix_natDegree_le_of_natDegree_le (ι := ι) (F := F) e deg
        (ωs := fun i => domain i) (g := g) (d := k) hg (r := (r : Fin N → ι)))
  have he1_le : e + 1 ≤ Fintype.card ι := by
    simpa [e] using
      (RS_floor_mul_card_ι_add_one_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) (hdeg := hdeg) (hδ := hδ))
  have hk_le : k * (e + 1) ≤ k * Fintype.card ι := Nat.mul_le_mul_left k he1_le
  have hS' : k * Fintype.card ι < S.card := by
    simpa [S] using hS
  have hdeg_lt : (Matrix.det A).natDegree < S.card :=
    lt_of_le_of_lt (le_trans hdeg_det hk_le) hS'
  -- det(A) vanishes at every good parameter
  have heval : ∀ z ∈ S, (Matrix.det A).eval z = 0 := by
    intro z hz
    have hz' : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ := by
      simpa [S] using hz
    have hk :=
      RS_exists_kernelVec_BW_homMatrix_eval_of_mem_goodCoeffsCurve (k := k) (deg := deg)
        (domain := domain) (δ := δ) (u := u) (z := z) hz'
    dsimp at hk
    rcases hk with ⟨a, b, ha0, hmul⟩
    let v : Fin N → F := Fin.append a b
    have hv_ne : v ≠ 0 := by
      intro hv
      apply ha0
      ext i
      have hvi : v (Fin.castAdd (e + deg) i) = (0 : Fin N → F) (Fin.castAdd (e + deg) i) :=
        congrArg (fun f => f (Fin.castAdd (e + deg) i)) hv
      simpa [v, N] using hvi
    let Mz : Matrix ι (Fin N) F :=
      BW_homMatrix (ι := ι) e deg (fun i => domain i)
        (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i)
    have hmulMz : Mz *ᵥ v = 0 := by
      simpa [Mz, v, N, e] using hmul
    have hmulSub :
        (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) *ᵥ v = 0 := by
      ext i
      have hi : (Mz *ᵥ v) (r i) = 0 := by
        simpa using congrArg (fun f => f (r i)) hmulMz
      simpa [Matrix.mulVec, Matrix.submatrix] using hi
    have hdetMz :
        Matrix.det (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) = 0 := by
      exact (Matrix.exists_mulVec_eq_zero_iff
        (M := Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N))).1
        ⟨v, hv_ne, hmulSub⟩
    have hdet_eval : (Matrix.det A).eval z = Matrix.det (A.map (Polynomial.eval z)) := by
      simpa [Polynomial.coe_evalRingHom] using (RingHom.map_det (Polynomial.evalRingHom z) A)
    have hAmap : A.map (Polynomial.eval z) =
        Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N) := by
      have hMmap : M.map (Polynomial.eval z) = Mz := by
        rw [show M.map (Polynomial.eval z)
            = BW_homMatrix (ι := ι) e deg (fun i => domain i) (fun i => (g i).eval z) from
          BW_homMatrix_map_evalRingHom_poly (e := e) (k := deg)
            (ωs := fun i => domain i) (g := g) z]
        have hgeval : (fun i => (g i).eval z)
            = fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i := by
          funext i
          simp only [g, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_pow, Polynomial.eval_X]
          exact Finset.sum_congr rfl fun t _ => mul_comm _ _
        rw [hgeval]
      ext i j
      change (M.map (Polynomial.eval z)) (r i) j = Mz (r i) j
      rw [hMmap]
    rw [hdet_eval]
    simpa [hAmap] using hdetMz
  have hdetA0 : Matrix.det A = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (p := Matrix.det A) (s := S) heval
      (by simpa using hdeg_lt)
  simpa [A, M, N, e] using hdetA0

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffsCurve_card_gt_fun
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k *
      Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    let N : ℕ := (e + 1) + (e + deg)
    ∀ r : Fin N → ι,
      Matrix.det
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e deg
              (fun i => (Polynomial.C (domain i) : F[X]))
              (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
            r id) = 0 := by
  classical
  dsimp
  intro r
  by_cases hinj : Function.Injective r
  · let r' :
        Fin ((Nat.floor (δ * Fintype.card ι) + 1) + (Nat.floor (δ * Fintype.card ι) + deg)) ↪ ι :=
      ⟨r, hinj⟩
    have h :=
      RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffsCurve_card_gt
        (k := k) (deg := deg) (domain := domain) (δ := δ) u hdeg hδ hS
    dsimp at h
    exact h r'
  · have hinj' :
        ∃ i j : Fin ((Nat.floor (δ * Fintype.card ι) + 1) + (Nat.floor (δ * Fintype.card ι) + deg)),
        r i = r j ∧ i ≠ j := by
      -- unfold Injective and push negation
      have : ¬ (∀ i j, r i = r j → i = j) := by
        simpa [Function.Injective] using hinj
      push Not at this
      -- `this` is now ∃ i j, r i = r j ∧ i ≠ j
      simpa [and_left_comm, and_assoc, and_comm] using this
    rcases hinj' with ⟨i, j, hij, hne⟩
    have hrow : (Matrix.submatrix
        (BW_homMatrix (ι := ι) (Nat.floor (δ * Fintype.card ι)) deg
          (fun i => (Polynomial.C (domain i) : F[X]))
          (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
        r id) i =
        (Matrix.submatrix
          (BW_homMatrix (ι := ι) (Nat.floor (δ * Fintype.card ι)) deg
            (fun i => (Polynomial.C (domain i) : F[X]))
            (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
          r id) j := by
      ext k
      simp [Matrix.submatrix, hij]
    -- determinant is zero due to repeated rows
    exact Matrix.det_zero_of_row_eq (M :=
        Matrix.submatrix
          (BW_homMatrix (ι := ι) (Nat.floor (δ * Fintype.card ι)) deg
            (fun i => (Polynomial.C (domain i) : F[X]))
            (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
          r id) hne hrow


open scoped BigOperators in
open Polynomial in
open Matrix in
open BerlekampWelch in
theorem RS_exists_nonzero_kernelVec_BW_homMatrix_of_goodCoeffsCurve_card_gt
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k *
      Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    ∃ a : Fin (e + 1) → F[X],
      ∃ b : Fin (e + deg) → F[X],
        Fin.append a b ≠ 0 ∧
          (∀ t, (a t).natDegree ≤ k * e) ∧
            (∀ s, (b s).natDegree ≤ k * (e + 1)) ∧
              Matrix.mulVec
                  (BW_homMatrix (ι := ι) e deg
                    (fun i => (Polynomial.C (domain i) : F[X]))
                    (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
                  (Fin.append a b) = 0 := by
  classical
  -- unfold the initial `let e := ...`
  dsimp
  set e : ℕ := Nat.floor (δ * Fintype.card ι) with he
  let m : ℕ := e + 1
  let n : ℕ := e + deg
  let N : ℕ := m + n
  let M : Matrix ι (Fin N) F[X] :=
    BW_homMatrix (ι := ι) e deg (fun i => (Polynomial.C (domain i) : F[X]))
      (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ))
  have hdetM : ∀ r : Fin N → ι, Matrix.det (Matrix.submatrix M r id) = 0 := by
    intro r
    simpa [M, N, m, n, he] using
      (RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffsCurve_card_gt_fun (k := k) (deg := deg)
        (domain := domain) (δ := δ) (u := u) hdeg hδ hS r)
  have hcard_n : n ≤ Fintype.card ι := by
    simpa [n, e, he] using
      (RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) hdeg hδ)
  obtain ⟨rB⟩ : Nonempty (Fin n ↪ ι) := by
    classical
    refine Function.Embedding.nonempty_of_card_le ?_
    simpa using hcard_n
  let cL : Fin m → Fin N := fun j => Fin.castAdd n j
  let cR : Fin n → Fin N := fun j => Fin.natAdd m j
  let L : Matrix ι (Fin m) F[X] := Matrix.submatrix M id cL
  let R : Matrix ι (Fin n) F[X] := Matrix.submatrix M id cR
  let A21 : Matrix (Fin n) (Fin m) F[X] := Matrix.submatrix M rB cL
  let D : Matrix (Fin n) (Fin n) F[X] := Matrix.submatrix M rB cR
  have hD : D = -Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X])) := by
    funext i j
    have hj' : ¬ e + 1 + (j : ℕ) ≤ e := by
      omega
    simp [D, M, BW_homMatrix, cR, Matrix.vandermonde, m, hj']
  have hvB : Function.Injective (fun i : Fin n => domain (rB i)) := by
    intro i1 i2 h
    apply rB.injective
    apply domain.injective
    exact h
  have hdetV : IsUnit
      (Matrix.det
        (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X])))) := by
    simpa using
      (RS_isUnit_det_vandermonde_C_of_injective (F := F) n (fun i : Fin n => domain (rB i)) hvB)
  have hdetD : IsUnit (Matrix.det D) := by
    have hunitNeg : IsUnit ((-1 : F[X]) ^ Fintype.card (Fin n)) := by
      simpa using (isUnit_neg_one (α := F[X])).pow (Fintype.card (Fin n))
    have hdetD' :
        Matrix.det D =
          (-1 : F[X]) ^ Fintype.card (Fin n) *
            Matrix.det
              (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X]))) := by
      simp [hD, Matrix.det_neg]
    refine hdetD'.symm ▸ (hunitNeg.mul hdetV)
  letI : Invertible D := Matrix.invertibleOfIsUnitDet D hdetD
  let K0 : Matrix ι (Fin m) F[X] := L - R * (⅟D * A21)
  have hdetK0 : ∀ rA : Fin m → ι, Matrix.det (K0.submatrix rA id) = 0 := by
    intro rA
    let r : Fin N → ι := Fin.append rA rB
    have hdetA : Matrix.det (M.submatrix r id) = 0 := hdetM r
    let eSum : (Fin m ⊕ Fin n) ≃ Fin N := finSumFinEquiv (m := m) (n := n)
    let Ablocks : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) F[X] :=
      (M.submatrix r id).submatrix eSum eSum
    have hdetAblocks : Matrix.det Ablocks = 0 := by
      have hdetEq : Matrix.det Ablocks = Matrix.det (M.submatrix r id) := by
        simpa [Ablocks] using (Matrix.det_submatrix_equiv_self (e := eSum) (M.submatrix r id))
      simpa [hdetEq] using hdetA
    have hAblocks_eq :
        Ablocks = Matrix.fromBlocks (L.submatrix rA id) (R.submatrix rA id) A21 D := by
      funext i j
      cases i <;> cases j <;>
        simp (config := { zeta := true })
          [Ablocks, eSum, L, R, A21, D, r, cL, cR, Matrix.fromBlocks, N, m, n]
    have hmul :
        Matrix.det D *
            Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21) =
          0 := by
      have hformula :=
        (Matrix.det_fromBlocks₂₂ (A := L.submatrix rA id) (B := R.submatrix rA id)
          (C := A21) (D := D))
      simpa [hAblocks_eq, hformula, Matrix.mul_assoc] using hdetAblocks
    have hdetSchur :
        Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21) = 0 := by
      exact (IsUnit.mul_right_eq_zero (a := Matrix.det D)
        (b := Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21)) hdetD).1 hmul
    simpa [K0, Matrix.submatrix_sub, Matrix.submatrix_mul, Matrix.submatrix_submatrix,
      Matrix.mul_assoc, Function.comp, L, R] using hdetSchur
  have hg : ∀ i : ι,
      ((∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ) : F[X])).natDegree ≤ k := by
    intro i
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro t _
    refine le_trans Polynomial.natDegree_mul_le ?_
    simp only [Polynomial.natDegree_C, Polynomial.natDegree_pow, Polynomial.natDegree_X,
      mul_one, Nat.zero_add]
    exact Nat.le_of_lt_succ t.isLt
  have hdegL : ∀ i j, (L i j).natDegree ≤ k := by
    intro i j
    simpa [L, cL, M] using
      (BW_homMatrix_entry_natDegree_le_of_natDegree_le (F := F) (ι := ι) e deg
        (ωs := fun i => domain i)
        (g := (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
        (d := k) hg i (cL j))
  have hdegA21 : ∀ i j, (A21 i j).natDegree ≤ k := by
    intro i j
    simpa [A21, cL, M] using
      (BW_homMatrix_entry_natDegree_le_of_natDegree_le (F := F) (ι := ι) e deg
        (ωs := fun i => domain i)
        (g := (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
        (d := k) hg (rB i) (cL j))
  have hdegR0 : ∀ i j, (R i j).natDegree = 0 := by
    intro i j
    have hj : e + 1 ≤ (cR j).1 := by
      simp [cR, m]
    have hle := BW_homMatrix_entry_natDegree_le_of_branch (F := F) (ι := ι) e deg
      (ωs := fun i => domain i)
      (g := (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
      (d := k) hg i (cR j)
    rw [if_neg (by omega : ¬ ((cR j).1 < e + 1))] at hle
    simpa [R, cR, M] using Nat.le_zero.mp hle
  have hdegInvD0 : ∀ i j : Fin n, (D⁻¹ i j).natDegree = 0 := by
    intro i j
    simpa [hD] using
      (RS_natDegree_inv_neg_vandermonde_C_eq_zero
        (F := F) n (fun t : Fin n => domain (rB t)) hvB i j)
  have hdegInvDA21 : ∀ i j, ((⅟D * A21) i j).natDegree ≤ k := by
    intro i j
    classical
    have hterm : ∀ kk ∈ (Finset.univ : Finset (Fin n)),
        ((⅟D i kk) * (A21 kk j)).natDegree ≤ k := by
      intro kk hk
      have hInv' : (D⁻¹ i kk).natDegree = 0 := hdegInvD0 i kk
      calc
        ((⅟D i kk) * (A21 kk j)).natDegree ≤ (⅟D i kk).natDegree + (A21 kk j).natDegree :=
          Polynomial.natDegree_mul_le
        _ = 0 + (A21 kk j).natDegree := by
          simp [Matrix.invOf_eq_nonsing_inv, hInv']
        _ = (A21 kk j).natDegree := by simp
        _ ≤ k := hdegA21 kk j
    have hsum :=
      Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
        (n := k) (f := fun k : Fin n => (⅟D i k) * (A21 k j)) hterm
    simpa [Matrix.mul_apply] using hsum
  have hdegRInvDA21 : ∀ i j, ((R * (⅟D * A21)) i j).natDegree ≤ k := by
    intro i j
    classical
    have hterm : ∀ kk ∈ (Finset.univ : Finset (Fin n)),
        (R i kk * ((⅟D * A21) kk j)).natDegree ≤ k := by
      intro kk hk
      have hR : (R i kk).natDegree = 0 := hdegR0 i kk
      calc
        (R i kk * ((⅟D * A21) kk j)).natDegree ≤ (R i kk).natDegree + ((⅟D * A21) kk j).natDegree :=
          Polynomial.natDegree_mul_le
        _ = 0 + ((⅟D * A21) kk j).natDegree := by simp [hR]
        _ = ((⅟D * A21) kk j).natDegree := by simp
        _ ≤ k := hdegInvDA21 kk j
    have hsum :=
      Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
        (n := k) (f := fun k : Fin n => R i k * ((⅟D * A21) k j)) hterm
    simpa [Matrix.mul_apply] using hsum
  have hdegK0 : ∀ i j, (K0 i j).natDegree ≤ k := by
    intro i j
    have hsub : (L i j - (R * (⅟D * A21)) i j).natDegree ≤
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree :=
      Polynomial.natDegree_sub_le (L i j) ((R * (⅟D * A21)) i j)
    have hmax :
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree ≤ k := by
      exact max_le_iff.mpr ⟨hdegL i j, hdegRInvDA21 i j⟩
    have : (K0 i j).natDegree ≤
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree := by
      simpa [K0] using hsub
    exact le_trans this hmax
  have hcard_m : m ≤ Fintype.card ι := by
    simpa [m, e, he] using
      (RS_floor_mul_card_ι_add_one_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) hdeg hδ)
  obtain ⟨a, ha0, ha_deg, haKer⟩ :=
    RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le (ι := ι) (F := F) e k K0
      (by simpa [m] using hcard_m) hdegK0 (by
        intro rA
        simpa [m, K0] using hdetK0 rA)
  let b : Fin n → F[X] := -(⅟D).mulVec (A21.mulVec a)
  refine ⟨a, b, ?_, ha_deg, ?_, ?_⟩
  · intro happ
    apply ha0
    funext t
    have := congrArg (fun f : Fin N → F[X] => f (Fin.castAdd n t)) happ
    simpa [Fin.append_left, m, n, N, b] using this
  · intro s
    classical
    have hdegA21mulVec : ∀ i : Fin n, ((A21.mulVec a) i).natDegree ≤ k * (e + 1) := by
      intro i
      have hterm : ∀ t ∈ (Finset.univ : Finset (Fin m)),
          (A21 i t * a t).natDegree ≤ k * (e + 1) := by
        intro t ht
        have hA : (A21 i t).natDegree ≤ k := hdegA21 i t
        have ha : (a t).natDegree ≤ k * e := ha_deg t
        have hmul : (A21 i t * a t).natDegree ≤ (A21 i t).natDegree + (a t).natDegree :=
          Polynomial.natDegree_mul_le
        have hadd : (A21 i t).natDegree + (a t).natDegree ≤ k + k * e := Nat.add_le_add hA ha
        have : (A21 i t * a t).natDegree ≤ k + k * e := le_trans hmul hadd
        calc (A21 i t * a t).natDegree ≤ k + k * e := this
          _ = k * (e + 1) := by ring
      have hsum :=
        Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin m)))
          (n := k * (e + 1)) (f := fun t : Fin m => A21 i t * a t) hterm
      simpa [Matrix.mulVec, dotProduct] using hsum
    have hdegInvDmulVec : ∀ i : Fin n, ((⅟D).mulVec (A21.mulVec a) i).natDegree ≤ k * (e + 1) := by
      intro i
      have hterm : ∀ kk ∈ (Finset.univ : Finset (Fin n)),
          ((⅟D i kk) * (A21.mulVec a kk)).natDegree ≤ k * (e + 1) := by
        intro kk hk
        have hInv' : (D⁻¹ i kk).natDegree = 0 := hdegInvD0 i kk
        have hA : ((A21.mulVec a) kk).natDegree ≤ k * (e + 1) := hdegA21mulVec kk
        calc
          ((⅟D i kk) * (A21.mulVec a kk)).natDegree ≤
              (⅟D i kk).natDegree + (A21.mulVec a kk).natDegree :=
            Polynomial.natDegree_mul_le
          _ = 0 + (A21.mulVec a kk).natDegree := by
            simp [Matrix.invOf_eq_nonsing_inv, hInv']
          _ = (A21.mulVec a kk).natDegree := by simp
          _ ≤ k * (e + 1) := hA
      have hsum :=
        Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
          (n := k * (e + 1)) (f := fun k : Fin n => (⅟D i k) * (A21.mulVec a k)) hterm
      simpa [Matrix.mulVec, dotProduct] using hsum
    simpa [b] using hdegInvDmulVec s
  · -- kernel equation
    have hRb : Matrix.mulVec R b = -Matrix.mulVec (R * (⅟D * A21)) a := by
      ext i
      simp [b, Matrix.mulVec_neg, Matrix.mulVec_mulVec]
    have hLR : Matrix.mulVec L a + Matrix.mulVec R b = 0 := by
      have haKer' : Matrix.mulVec (L - R * (⅟D * A21)) a = 0 := by
        simpa [K0] using haKer
      have haKer'' : Matrix.mulVec L a - Matrix.mulVec (R * (⅟D * A21)) a = 0 := by
        simpa [Matrix.sub_mulVec] using haKer'
      simpa [sub_eq_add_neg, hRb] using haKer''
    have hsplit : Matrix.mulVec M (Fin.append a b) = Matrix.mulVec L a + Matrix.mulVec R b := by
      simpa [L, R, cL, cR, N] using
        (RS_mulVec_append_castAdd_natAdd (ι := ι) (R := F[X]) m n M a b)
    change Matrix.mulVec M (Fin.append a b) = 0
    rw [hsplit]
    exact hLR

omit [Nonempty ι] in
theorem card_RS_goodCoeffsCurve_gt_of_prob_gt_kn_div_q
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{ let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code domain deg)
        ≤ δ]
        > (k * Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0)) :
    (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k * Fintype.card ι := by
  classical
  -- predicate defining the good coefficients
  let P : F → Prop := fun z : F =>
    δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code domain deg) ≤ δ
  -- uniform probability equals (card of filter) / (card of the field)
  have hPr :
      Pr_{ let z ← $ᵖ F }[ P z ] =
        ((Finset.filter (α := F) P Finset.univ).card : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    classical
    -- Expand the probability mass at `True`
    simp only [Bind.bind, PMF.bind, PMF.uniformOfFintype_apply, pure, PMF.pure_apply, eq_iff_iff,
      mul_ite, mul_one, mul_zero, ENNReal.coe_natCast]
    simp only [DFunLike.coe, true_iff]
    -- Reduce the infinite sum to the finite support
    rw [
      tsum_eq_sum (α := ENNReal) (β := F)
        (f := fun a => if P a then (↑(Fintype.card F))⁻¹ else 0)
        (s := Finset.filter P Finset.univ)
        (hf := fun b => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro hb
          simp only [hb, if_false])
    ]
    -- Evaluate the resulting finite sum
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    rw [Finset.sum_const]
    rw [nsmul_eq_mul']
    rw [mul_comm]
    conv_lhs =>
      rw [← div_eq_mul_inv]
    -- Filtering twice is the same as filtering once
    have h_card_eq : {x ∈ filter P univ | P x} = filter P univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [and_self_iff]
    rw [h_card_eq]
  -- restate the hypothesis using `P`
  have hprobP :
      Pr_{ let z ← $ᵖ F }[ P z ]
        > ((k * Fintype.card ι : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    simpa [P, Nat.cast_mul] using hprob
  -- rewrite the probability lower bound as a ratio comparison
  have hprobQ := hprobP
  rw [hPr] at hprobQ
  -- switch to `<` form
  have hlt :
      (((k * Fintype.card ι : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ENNReal)
        <
          (((Finset.filter (α := F) P Finset.univ).card : ℝ≥0) /
            (Fintype.card F : ℝ≥0) : ENNReal) :=
    (gt_iff_lt).1 hprobQ
  have hq0 : (Fintype.card F : ENNReal) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hqtop : (Fintype.card F : ENNReal) ≠ ⊤ := by
    exact ENNReal.natCast_ne_top (Fintype.card F)
  have hcard_cast :
      ((k * Fintype.card ι : ℕ) : ENNReal) <
        ((Finset.filter (α := F) P Finset.univ).card : ENNReal) := by
    -- rewrite both sides of `hlt` as ENNReal divisions and cancel
    have hlt' :
        ((k * Fintype.card ι : ℕ) : ENNReal) / (Fintype.card F : ENNReal)
          < ((Finset.filter (α := F) P Finset.univ).card : ENNReal) /
              (Fintype.card F : ENNReal) := by
      have hq0' : (Fintype.card F : ℝ≥0) ≠ 0 := by
        simp [Fintype.card_ne_zero]
      simpa [ENNReal.coe_div (r := (Fintype.card F : ℝ≥0)) hq0', ENNReal.coe_natCast] using hlt
    exact (ENNReal.div_lt_div_iff_left (hc₀ := hq0) (hc := hqtop)).1 hlt'
  have hcard_nat : k * Fintype.card ι < (Finset.filter (α := F) P Finset.univ).card := by
    exact Nat.cast_lt.mp hcard_cast
  -- identify the filtered finset with `RS_goodCoeffs`
  simpa [RS_goodCoeffsCurve, P, gt_iff_lt] using hcard_nat

open scoped BigOperators in
open Polynomial in
open Matrix in
omit [Nonempty ι] [Fintype F] [DecidableEq F] in
theorem RS_a_ne_zero_of_BW_homMatrix_mulVec_eq_zero_curve {k deg : ℕ} {domain : ι ↪ F} {e : ℕ}
    (u : WordStack F (Fin (k + 1)) ι)
    {a : Fin (e + 1) → F[X]} {b : Fin (e + deg) → F[X]}
    (hdeg : e + deg ≤ Fintype.card ι)
    (happend : Fin.append a b ≠ 0)
    (hMul :
      Matrix.mulVec
          (BW_homMatrix (ι := ι) e deg
            (fun i => (Polynomial.C (domain i) : F[X]))
            (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
          (Fin.append a b) = 0) :
    a ≠ 0 := by
  intro ha0
  -- Pointwise equality derived from the mulVec hypothesis
  have hEq :
      ∀ i : ι,
        (∑ t : Fin (e + 1), a t * (Polynomial.C (domain i) : F[X]) ^ t.1) *
            (∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)) =
          ∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1 :=
    (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (R := F[X]) e deg
          (fun i => (Polynomial.C (domain i) : F[X]))
          (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ))
          a b).1 hMul
  have hVand :
      ∀ i : ι,
        (∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1) = 0 := by
    intro i
    -- With a = 0, the left sum is 0, so the RHS must be 0.
    have hi := (hEq i).symm
    simpa [ha0] using hi
  have hb0 : b = 0 :=
    RS_vandermonde_coeffs_eq_zero (ι := ι) (F := F) (m := e + deg) (domain := domain) hdeg b hVand
  have happend0 : Fin.append a b = 0 := by
    ext i
    cases i using Fin.addCases <;> simp [ha0, hb0]
  exact happend happend0
open Polynomial in
/-- Curves analogue of `RS_exists_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt`:
the global kernel vector repackaged with `a ≠ 0`. -/
theorem RS_exists_kernelVec_BW_homMatrix_of_goodCoeffsCurve_card_gt
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card
      > k * Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    ∃ a : Fin (e + 1) → F[X],
      ∃ b : Fin (e + deg) → F[X],
        a ≠ 0 ∧
          (∀ t, (a t).natDegree ≤ k * e) ∧
            (∀ s, (b s).natDegree ≤ k * (e + 1)) ∧
              Matrix.mulVec
                  (BW_homMatrix (ι := ι) e deg
                    (fun i => (Polynomial.C (domain i) : F[X]))
                    (fun i => ∑ t : Fin (k + 1), Polynomial.C (u t i) * Polynomial.X ^ (t : ℕ)))
                  (Fin.append a b) = 0 := by
  classical
  dsimp
  have h :=
    RS_exists_nonzero_kernelVec_BW_homMatrix_of_goodCoeffsCurve_card_gt
      (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) hdeg hδ hS
  dsimp at h
  rcases h with ⟨a, b, happend, ha_deg, hb_deg, hMul⟩
  have hdeg' : Nat.floor (δ * Fintype.card ι) + deg ≤ Fintype.card ι :=
    RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR
      (deg := deg) (domain := domain) (δ := δ) (hdeg := hdeg) (hδ := hδ)
  have ha0 : a ≠ 0 :=
    RS_a_ne_zero_of_BW_homMatrix_mulVec_eq_zero_curve
      (k := k) (deg := deg) (domain := domain) (e := Nat.floor (δ * Fintype.card ι))
      (u := u) (a := a) (b := b) hdeg' happend hMul
  exact ⟨a, b, ha0, ha_deg, hb_deg, hMul⟩

end CoreResults

end ProximityGap
