/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowPadeBridge

/-!
# The reconstruction pencil (#371, round 13): branch (i) of the window dichotomy

The Padé reconstruction system in inverse-free form: a scalar `γ` is
*reconstruction-solvable* at profile `(j, w)` when

  `ℓ₀ℓ₁ ∣ Z_D·h − (A + γB)·Z`,   `deg h ≤ j`, `deg Z ≤ w`, `Z ≠ 0`,

(`Z_D` the domain vanishing polynomial, `A := ℓ₁R₀`, `B := ℓ₀R₁`).  Via the landed
Padé bridge every mca-bad scalar is reconstruction-solvable (`Z := Z_T` the missing-set
polynomial).  The system is linear in the `(j+1) + (w+1)` unknown coefficients with
`2w` equations, and the coefficient matrix is a **γ-linear pencil** — so the WB-1
dichotomy applies one level up:

* **branch (i)** (this file): if some square row-selection has a not-identically-zero
  determinant polynomial, then the solvable scalars are among its roots:
  **`#bad ≤ j + w + 2`** — already inside the linear budget at every stratum;
* branch (ii) (the degenerate pencil: all minors vanish identically) proceeds by the
  adjugate-family incidence count (next file).

Generic stacks live in branch (i) with zero-to-few roots (the campaign's universal
random-probe zeros); the adversarial families (coset, normalizer) are branch (ii).
-/

open Finset Polynomial Matrix
open scoped NNReal

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section RecPencil

variable (dom : Fin n ↪ F) {k w j : ℕ}
variable (ℓ₀ ℓ₁ R₀ R₁ : F[X])

/-- The domain vanishing polynomial. -/
noncomputable def domZ (dom : Fin n ↪ F) : F[X] :=
  Finset.univ.prod fun i => X - C (dom i)

/-- Reconstruction solvability at profile `(j, w)`: the inverse-free Padé system. -/
noncomputable def RecSolvable (j w : ℕ) (γ : F) : Prop :=
  ∃ h Z : F[X], Z ≠ 0 ∧ h.natDegree ≤ j ∧ Z.natDegree ≤ w ∧
    (ℓ₀ * ℓ₁) ∣ (domZ dom * h - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z)

/-- **The bridge feeds the pencil**: every mca-bad scalar of a genuine coprime stack
is reconstruction-solvable at the witness profile. -/
theorem recSolvable_of_mcaEvent (hk : 1 ≤ k)
    (hℓ₀d : ℓ₀.natDegree ≤ w) (hℓ₁d : ℓ₁.natDegree ≤ w)
    (hR₀d : R₀.natDegree ≤ w + k - 1) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen₀ : ¬ ℓ₀ ∣ R₀)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) {γ : F}
    (hbad : mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ) :
    RecSolvable dom ℓ₀ ℓ₁ R₀ R₁ (2 * w + k - 1 - (n - w)) w γ := by
  obtain ⟨S, h, P, hScard, hPd, hdeg, hid⟩ := mcaEvent_factored dom hk
    hℓ₀d hℓ₁d hR₀d hR₁d hℓ₀v hℓ₁v hcop hgen₀ hδn hbad
  set ZT : F[X] := (Finset.univ \ S).prod fun i => X - C (dom i) with hZT
  refine ⟨h, ZT, ?_, ?_, ?_, ?_⟩
  · -- ZT ≠ 0: product of monic linears
    rw [hZT]
    exact (monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (dom i))).ne_zero
  · -- deg h ≤ j: from the bridge budget
    omega
  · -- deg ZT = n − |S| ≤ w
    have hZTdeg : ZT.natDegree = (Finset.univ \ S).card := by
      rw [hZT, natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero (dom i))]
      simp [natDegree_X_sub_C]
    have hcard : (Finset.univ \ S).card = n - S.card := by
      rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ, Fintype.card_fin]
    have hSn : S.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ S)
      rwa [Finset.card_univ, Fintype.card_fin] at this
    omega
  · -- the divisibility: multiply the bridge identity by ZT
    have hpart : ZT * (S.prod fun i => X - C (dom i)) = domZ dom := by
      rw [hZT, domZ]
      exact Finset.prod_sdiff (Finset.subset_univ S)
    refine ⟨-(ZT * P), ?_⟩
    calc domZ dom * h - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * ZT
        = ZT * ((S.prod fun i => X - C (dom i)) * h)
          - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * ZT := by
          rw [← hpart]; ring
      _ = ZT * (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁) - P * (ℓ₀ * ℓ₁))
          - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * ZT := by rw [hid]
      _ = ℓ₀ * ℓ₁ * -(ZT * P) := by ring

/-- The reconstruction coefficient matrix: rows = the `2w` reduced coefficients,
columns = the `(j+1)` h-coefficients and `(w+1)` Z-coefficients. -/
noncomputable def recMatrix (j w : ℕ) (γ : F) :
    Matrix (Fin (2 * w)) (Fin (j + 1) ⊕ Fin (w + 1)) F :=
  fun r => Sum.elim
    (fun t => (((domZ dom * X ^ (t : ℕ))) %ₘ (ℓ₀ * ℓ₁)).coeff r)
    (fun s => -((((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ))) %ₘ (ℓ₀ * ℓ₁)).coeff r)

/-- The `h`-polynomial of a coefficient vector. -/
noncomputable def recH (v : Fin (j + 1) ⊕ Fin (w + 1) → F) : F[X] :=
  ∑ t : Fin (j + 1), C (v (Sum.inl t)) * X ^ (t : ℕ)

/-- The `Z`-polynomial of a coefficient vector. -/
noncomputable def recZ (v : Fin (j + 1) ⊕ Fin (w + 1) → F) : F[X] :=
  ∑ s : Fin (w + 1), C (v (Sum.inr s)) * X ^ (s : ℕ)

theorem recH_natDegree_le (v : Fin (j + 1) ⊕ Fin (w + 1) → F) :
    (recH (j := j) (w := w) v).natDegree ≤ j := by
  refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
  calc (C (v (Sum.inl t)) * X ^ (t : ℕ)).natDegree
      ≤ (C (v (Sum.inl t))).natDegree + (X ^ (t : ℕ) : F[X]).natDegree :=
        natDegree_mul_le
    _ ≤ 0 + t := Nat.add_le_add (le_of_eq (natDegree_C _))
        (le_of_eq (natDegree_X_pow _))
    _ ≤ j := by have := t.2; omega

theorem recZ_natDegree_le (v : Fin (j + 1) ⊕ Fin (w + 1) → F) :
    (recZ (j := j) (w := w) v).natDegree ≤ w := by
  refine natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
  calc (C (v (Sum.inr s)) * X ^ (s : ℕ)).natDegree
      ≤ (C (v (Sum.inr s))).natDegree + (X ^ (s : ℕ) : F[X]).natDegree :=
        natDegree_mul_le
    _ ≤ 0 + s := Nat.add_le_add (le_of_eq (natDegree_C _))
        (le_of_eq (natDegree_X_pow _))
    _ ≤ w := by have := s.2; omega

/-- `%ₘ` distributes over finite sums (additivity of `modByMonic` in the dividend). -/
theorem modByMonic_finset_sum (m : F[X]) {ι : Type} (s : Finset ι) (f : ι → F[X]) :
    (∑ i ∈ s, f i) %ₘ m = ∑ i ∈ s, (f i %ₘ m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_modByMonic, ih]

/-- The matrix action computes the reduced combination's coefficients. -/
theorem recMatrix_mulVec (j w : ℕ) (γ : F)
    (hmonic : (ℓ₀ * ℓ₁).Monic)
    (v : Fin (j + 1) ⊕ Fin (w + 1) → F) (r : Fin (2 * w)) :
    (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).mulVec v r
      = ((domZ dom * recH (j := j) (w := w) v
          - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * recZ (j := j) (w := w) v)
          %ₘ (ℓ₀ * ℓ₁)).coeff r := by
  have hexp : domZ dom * recH (j := j) (w := w) v
      - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * recZ (j := j) (w := w) v
      = (∑ t : Fin (j + 1), C (v (Sum.inl t)) * (domZ dom * X ^ (t : ℕ)))
        - (∑ s : Fin (w + 1), C (v (Sum.inr s))
            * ((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ))) := by
    rw [recH, recZ, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hexp]
  have hsum1 : ((∑ t : Fin (j + 1), C (v (Sum.inl t)) * (domZ dom * X ^ (t : ℕ)))
      %ₘ (ℓ₀ * ℓ₁))
      = ∑ t : Fin (j + 1),
          (C (v (Sum.inl t)) * (domZ dom * X ^ (t : ℕ))) %ₘ (ℓ₀ * ℓ₁) :=
    modByMonic_finset_sum _ _ _
  have hsum2 : ((∑ s : Fin (w + 1), C (v (Sum.inr s))
      * ((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ))) %ₘ (ℓ₀ * ℓ₁))
      = ∑ s : Fin (w + 1),
          (C (v (Sum.inr s)) * ((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ)))
            %ₘ (ℓ₀ * ℓ₁) :=
    modByMonic_finset_sum _ _ _
  have hRHS : (((∑ t : Fin (j + 1), C (v (Sum.inl t)) * (domZ dom * X ^ (t : ℕ)))
      - (∑ s : Fin (w + 1), C (v (Sum.inr s))
          * ((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ)))) %ₘ (ℓ₀ * ℓ₁)).coeff r
      = (∑ t : Fin (j + 1),
          v (Sum.inl t) * (((domZ dom * X ^ (t : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r))
        - (∑ s : Fin (w + 1), v (Sum.inr s)
            * ((((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r)) := by
    rw [sub_modByMonic, hsum1, hsum2, coeff_sub, finset_sum_coeff, finset_sum_coeff]
    congr 1
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [← smul_eq_C_mul, smul_modByMonic, coeff_smul, smul_eq_mul]
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [← smul_eq_C_mul, smul_modByMonic, coeff_smul, smul_eq_mul]
  have hLHS : (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).mulVec v r
      = (∑ t : Fin (j + 1),
          v (Sum.inl t) * (((domZ dom * X ^ (t : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r))
        - (∑ s : Fin (w + 1), v (Sum.inr s)
            * ((((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r)) := by
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [recMatrix]
      show (((domZ dom * X ^ (t : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r) * v (Sum.inl t)
        = v (Sum.inl t) * (((domZ dom * X ^ (t : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r)
      ring
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [recMatrix]
      show (-((((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r))
          * v (Sum.inr s)
        = -(v (Sum.inr s)
            * ((((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r))
      ring
  rw [hLHS, hRHS]

/-- Reconstruction-solvable scalars have nontrivial matrix kernels. -/
theorem recMatrix_kernel_of_recSolvable {j w : ℕ}
    (hw : 1 ≤ w) (hjw : j < 2 * w)
    (hmonic : (ℓ₀ * ℓ₁).Monic) (hdeg : (ℓ₀ * ℓ₁).natDegree = 2 * w) {γ : F}
    (hsol : RecSolvable dom ℓ₀ ℓ₁ R₀ R₁ j w γ) :
    ∃ v : Fin (j + 1) ⊕ Fin (w + 1) → F, v ≠ 0 ∧
      (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).mulVec v = 0 := by
  obtain ⟨h, Z, hZ0, hhd, hZd, hdvd⟩ := hsol
  set v : Fin (j + 1) ⊕ Fin (w + 1) → F :=
    Sum.elim (fun t => h.coeff t) (fun s => Z.coeff s) with hv
  have hrecH : recH (j := j) (w := w) v = h := by
    rw [recH]
    conv_rhs => rw [h.as_sum_range' (j + 1) (by omega)]
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun t _ => by
      rw [hv, Sum.elim_inl, C_mul_X_pow_eq_monomial]
  have hrecZ : recZ (j := j) (w := w) v = Z := by
    rw [recZ]
    conv_rhs => rw [Z.as_sum_range' (w + 1) (by omega)]
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun s _ => by
      rw [hv, Sum.elim_inr, C_mul_X_pow_eq_monomial]
  refine ⟨v, ?_, ?_⟩
  · intro hv0
    apply hZ0
    rw [← hrecZ, recZ]
    rw [hv0]
    simp
  · funext r
    rw [recMatrix_mulVec dom ℓ₀ ℓ₁ R₀ R₁ j w γ hmonic, hrecH, hrecZ]
    rw [(modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd]
    simp

/-- The determinant polynomial of a square row-selection of the reconstruction
pencil: a polynomial in the line scalar. -/
noncomputable def recDetPoly (j w : ℕ)
    (I : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)) : F[X] :=
  Matrix.det (fun a b => Sum.elim
    (fun t : Fin (j + 1) =>
      C ((((domZ dom * X ^ (t : ℕ))) %ₘ (ℓ₀ * ℓ₁)).coeff (I a)))
    (fun s : Fin (w + 1) =>
      -(C ((((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I a))
        + X * C ((((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I a)))) b)

/-- Evaluation: the determinant polynomial at `γ` is the determinant of the
selected square of the instantiated matrix. -/
theorem recDetPoly_eval (j w : ℕ) (hmonic : (ℓ₀ * ℓ₁).Monic)
    (I : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)) (γ : F) :
    (recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I).eval γ
      = ((recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix I id).det := by
  rw [recDetPoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  funext a b
  rcases b with t | s
  · show Polynomial.eval γ
        (C ((((domZ dom * X ^ (t : ℕ))) %ₘ (ℓ₀ * ℓ₁)).coeff (I a)))
      = (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix I id a (Sum.inl t)
    rw [eval_C]
    rfl
  · show Polynomial.eval γ
        (-(C ((((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I a))
          + X * C ((((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I a))))
      = (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix I id a (Sum.inr s)
    rw [eval_neg, eval_add, eval_C, eval_mul, eval_X, eval_C]
    show -((((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I a)
        + γ * (((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I a))
      = -((((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I a))
    have hlin : ((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)
        = ((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)
          + γ • (((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)) := by
      rw [← smul_modByMonic, ← add_modByMonic]
      congr 1
      rw [smul_eq_C_mul]
      ring
    rw [hlin, coeff_add, coeff_smul, smul_eq_mul]

/-- The determinant polynomial has degree at most `w + 1` (only the `Z`-block
columns carry the scalar). -/
theorem recDetPoly_natDegree_le (j w : ℕ)
    (I : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)) :
    (recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I).natDegree ≤ w + 1 := by
  classical
  have hentry : ∀ (a b : Fin (j + 1) ⊕ Fin (w + 1)),
      ((Sum.elim
        (fun t : Fin (j + 1) =>
          C ((((domZ dom * X ^ (t : ℕ))) %ₘ (ℓ₀ * ℓ₁)).coeff (I a)))
        (fun s : Fin (w + 1) =>
          -(C ((((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I a))
            + X * C ((((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I a)))) b : F[X])).natDegree
        ≤ Sum.elim (fun _ : Fin (j + 1) => 0) (fun _ : Fin (w + 1) => 1) b := by
    intro a b
    rcases b with t | s
    · simp only [Sum.elim_inl, natDegree_C, le_refl]
    · simp only [Sum.elim_inr, natDegree_neg]
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · rw [natDegree_C]
        omega
      · refine le_trans natDegree_mul_le ?_
        rw [natDegree_X, natDegree_C]
  rw [recDetPoly, Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  have hprod' : (∏ b : Fin (j + 1) ⊕ Fin (w + 1),
      (Sum.elim
        (fun t : Fin (j + 1) =>
          C ((((domZ dom * X ^ (t : ℕ))) %ₘ (ℓ₀ * ℓ₁)).coeff (I (σ b))))
        (fun s : Fin (w + 1) =>
          -(C ((((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I (σ b)))
            + X * C ((((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I (σ b))))) b : F[X])).natDegree ≤ w + 1 := by
    refine le_trans (natDegree_prod_le _ _) ?_
    calc ∑ b : Fin (j + 1) ⊕ Fin (w + 1), ((Sum.elim
          (fun t : Fin (j + 1) =>
            C ((((domZ dom * X ^ (t : ℕ))) %ₘ (ℓ₀ * ℓ₁)).coeff (I (σ b))))
          (fun s : Fin (w + 1) =>
            -(C ((((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I (σ b)))
              + X * C ((((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff (I (σ b))))) b : F[X])).natDegree
        ≤ ∑ b : Fin (j + 1) ⊕ Fin (w + 1),
            Sum.elim (fun _ : Fin (j + 1) => 0) (fun _ : Fin (w + 1) => 1) b :=
          Finset.sum_le_sum fun b _ => hentry (σ b) b
      _ = w + 1 := by
          rw [Fintype.sum_sum_type]
          simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsg | hsg
  · rw [hsg, one_smul]
    exact hprod'
  · rw [hsg]
    refine le_trans (le_of_eq ?_) hprod'
    rw [Units.neg_smul, one_smul, natDegree_neg]

open Classical in
/-- **BRANCH (i) OF THE WINDOW DICHOTOMY**: if some square row-selection of the
reconstruction pencil has a not-identically-zero determinant polynomial, then at
most `w + 1` scalars are reconstruction-solvable — hence at most `w + 1` are
mca-bad (via the bridge). -/
theorem recSolvable_card_le {j w : ℕ}
    (hw : 1 ≤ w) (hjw : j < 2 * w)
    (hmonic : (ℓ₀ * ℓ₁).Monic) (hdeg : (ℓ₀ * ℓ₁).natDegree = 2 * w)
    {I : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)}
    (hI : recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I ≠ 0) :
    (Finset.univ.filter (fun γ : F =>
      RecSolvable dom ℓ₀ ℓ₁ R₀ R₁ j w γ)).card ≤ w + 1 := by
  have hroot : ∀ γ : F, RecSolvable dom ℓ₀ ℓ₁ R₀ R₁ j w γ →
      (recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I).eval γ = 0 := by
    intro γ hsol
    obtain ⟨v, hv0, hker⟩ := recMatrix_kernel_of_recSolvable dom ℓ₀ ℓ₁ R₀ R₁
      hw hjw hmonic hdeg hsol
    rw [recDetPoly_eval dom ℓ₀ ℓ₁ R₀ R₁ j w hmonic]
    by_contra hdet
    apply hv0
    refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
    funext a
    have hsub : ((recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix I id).mulVec v a
        = (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).mulVec v (I a) := by
      rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
      rfl
    rw [hsub, hker]
    rfl
  calc (Finset.univ.filter (fun γ : F =>
        RecSolvable dom ℓ₀ ℓ₁ R₀ R₁ j w γ)).card
      ≤ (recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I).roots.toFinset.card := by
        refine Finset.card_le_card ?_
        intro γ hγ
        rw [Finset.mem_filter] at hγ
        rw [Multiset.mem_toFinset, mem_roots hI]
        exact hroot γ hγ.2
    _ ≤ (recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I).roots.card :=
        (recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I).roots.toFinset_card_le
    _ ≤ (recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I).natDegree :=
        (recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I).card_roots'
    _ ≤ w + 1 := recDetPoly_natDegree_le dom ℓ₀ ℓ₁ R₀ R₁ j w I

end RecPencil

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.recSolvable_of_mcaEvent
#print axioms ProximityGap.WBPencil.recMatrix_mulVec
#print axioms ProximityGap.WBPencil.recMatrix_kernel_of_recSolvable
#print axioms ProximityGap.WBPencil.recDetPoly_natDegree_le
#print axioms ProximityGap.WBPencil.recSolvable_card_le
