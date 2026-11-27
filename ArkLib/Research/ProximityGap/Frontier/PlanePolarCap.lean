/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.GeometricIrreducibilitySmoothPoint
import ArkLib.Research.ProximityGap.Frontier.PlaneCurveReflexivity

/-! # Polar intersection caps for geometrically irreducible plane curves

Combines L2a (`GeometricIrreducibilitySmoothPoint`), L2b (`PlaneBezoutWithMultiplicity`), and L2c
(`PlaneCurveReflexivity`) over an arbitrary field `L` to prove:

- `irreducible_homog_of_irreducible_biv`: homogenization preserves irreducibility.
- `gaussPullback_not_dvd_of_gt`: Pardini reflexivity descended from `AlgebraicClosure L` to `L`.
- `polar_affine_card_le`: any nonzero degree-`s` dual curve `Q(H, R, V)` with `s * (s - 1) < m`
  vanishes on at most `s * (m * (m - 1) - (m - b) * (m - b - 1))` distinct affine points of `f = 0`.
- `polar_affine_card_le_of_smooth`: direct wrapper discharging geometric irreducibility from a
  single smooth `L`-point via `irreducible_algebraicClosure_of_smooth`.
- `conic_five_column_polar_cap`: for an irreducible conic `m = 2` with `(2 : L) ≠ 0`, there is a
  degree-2 monomial `e₀ = (i, j)` with `i + j = 2` such that every nonzero quadratic `Q(H, R, V)`
  with vanishing `R^i V^j`-coefficient vanishes on at most `4` distinct affine points of `f = 0`.
-/

set_option autoImplicit false
noncomputable section

open Polynomial MvPolynomial Finset Module
open scoped Matrix
open ArkLib.ProximityGap.Frontier.GeometricIrreducibilitySmoothPoint
open ArkLib.ProximityGap.Frontier.PlaneBezoutWithMultiplicity
open ArkLib.ProximityGap.Frontier.PlaneCurveLinearAlgebra
open ArkLib.ProximityGap.Frontier.PlaneCurveFunctionField
open ArkLib.ProximityGap.Frontier.PlaneCurveReflexivity

namespace ArkLib.ProximityGap.Frontier.PlanePolarCap

section Helpers

variable {L K : Type*} [Field L] [Field K]

/-- `MvPolynomial.map` preserves homogeneity. -/
theorem map_isHomogeneous (φ : L →+* K) {F : MvPolynomial (Fin 3) L} {d : ℕ}
    (hF : F.IsHomogeneous d) : (MvPolynomial.map φ F).IsHomogeneous d := by
  intro e he
  rw [MvPolynomial.coeff_map] at he
  exact hF (fun h0 => he (by rw [h0, map_zero]))

/-- `MvPolynomial.map` commutes with partial derivatives. -/
theorem map_pderiv (φ : L →+* K) (i : Fin 3) (F : MvPolynomial (Fin 3) L) :
    MvPolynomial.map φ (pderiv i F) = pderiv i (MvPolynomial.map φ F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p j hp =>
    rw [pderiv_mul, map_add, map_mul, map_mul, hp, map_mul (MvPolynomial.map φ), MvPolynomial.map_X, pderiv_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [pderiv_X_of_ne (Ne.symm hij)]

/-- `MvPolynomial.map` commutes with `gaussPullback`. -/
theorem map_gaussPullback (φ : L →+* K) (F P : MvPolynomial (Fin 3) L) :
    MvPolynomial.map φ (gaussPullback F P) =
      gaussPullback (MvPolynomial.map φ F) (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [gaussPullback]
  | add p q hp hq => simp [gaussPullback, map_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p j hp =>
    simp only [gaussPullback] at hp ⊢
    rw [map_mul, map_mul, hp, map_mul, MvPolynomial.map_X, map_mul,
      MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    fin_cases j <;> simp [map_pderiv]

/-- `MvPolynomial.map` commutes with `substLin`. -/
theorem map_substLin (φ : L →+* K) (M : Matrix (Fin 3) (Fin 3) L) (P : MvPolynomial (Fin 3) L) :
    MvPolynomial.map φ (substLin M P) = substLin (M.map φ) (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, map_mul, MvPolynomial.map_X, map_mul,
      substLin_X, substLin_X, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.map_apply]

/-- `MvPolynomial.map` commutes with `mv2EquivBiv` and `mapBiv`. -/
theorem mapBiv_mv2EquivBiv (φ : L →+* K) (g : MvPolynomial (Fin 2) L) :
    mapBiv φ (mv2EquivBiv g) = mv2EquivBiv (MvPolynomial.map φ g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mapBiv]
  | add p q hp hq => simp [mapBiv, map_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, map_mul, MvPolynomial.map_X, map_mul]
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [mv2EquivBiv_X0, mv2EquivBiv_X0]; simp [mapBiv]
    · rw [mv2EquivBiv_X1, mv2EquivBiv_X1]; simp [mapBiv]

/-- `MvPolynomial.map` commutes with `homog` when the homomorphism is injective. -/
theorem map_homog (φ : L →+* K) (hφ : Function.Injective φ) (d : ℕ) (g : MvPolynomial (Fin 2) L) :
    MvPolynomial.map φ (homog d g) = homog d (MvPolynomial.map φ g) := by
  classical
  have hsupp : (MvPolynomial.map φ g).support = g.support := by
    ext e
    simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
    exact map_ne_zero_iff φ hφ
  unfold homog
  rw [map_sum, hsupp]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.coeff_map]

/-- Minimal homogenization preserves irreducibility of a bivariate polynomial. -/
theorem irreducible_homog_of_irreducible_biv {f : K[X][X]} {m : ℕ}
    (hf_irr : Irreducible f) (hm : (mv2EquivBiv.symm f).totalDegree = m) :
    Irreducible (homog m (mv2EquivBiv.symm f)) := by
  let fMv : MvPolynomial (Fin 2) K := mv2EquivBiv.symm f
  have hfMv_irr : Irreducible fMv :=
    (MulEquiv.irreducible_iff mv2EquivBiv.symm.toMulEquiv).mpr hf_irr
  let F : MvPolynomial (Fin 3) K := homog m fMv
  have hF_hom : F.IsHomogeneous m := homog_isHomogeneous m fMv (le_of_eq hm)
  have hF_dehom : dehom F = fMv := dehom_homog m fMv
  have hF_ne : F ≠ 0 := by
    intro h0
    have := congrArg dehom h0
    rw [hF_dehom, map_zero] at this
    exact hfMv_irr.ne_zero this
  have hX2_ndvd : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ F := by
    dsimp only [F]; rw [← hm]; exact X2_not_dvd_homog fMv hfMv_irr.ne_zero
  refine ⟨fun hu => hfMv_irr.not_isUnit (hF_dehom ▸ hu.map dehom.toRingHom), fun A B hAB => ?_⟩
  have hAB' : F = A * B := hAB
  have hA_ne : A ≠ 0 := by rintro rfl; simp at hAB'; exact hF_ne hAB'
  have hB_ne : B ≠ 0 := by rintro rfl; simp at hAB'; exact hF_ne hAB'
  obtain ⟨dA, hA_hom⟩ := isHomogeneous_of_dvd hF_hom hF_ne ⟨B, hAB'⟩
  obtain ⟨dB, hB_hom⟩ := isHomogeneous_of_dvd hF_hom hF_ne ⟨A, by rw [hAB', mul_comm]⟩
  have hdehom_mul : fMv = dehom A * dehom B := by rw [← hF_dehom, hAB', map_mul]
  rcases hfMv_irr.isUnit_or_isUnit hdehom_mul with huA | huB
  · left
    obtain ⟨c, hcU, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp huA
    have hA_eq : A = MvPolynomial.C c * MvPolynomial.X 2 ^ dA := by
      apply dehom_inj_on_homogeneous dA hA_hom
      · simpa using (MvPolynomial.isHomogeneous_C (Fin 3) c).mul
          ((MvPolynomial.isHomogeneous_X K (2 : Fin 3)).pow dA)
      · rw [hc, map_mul, map_pow, dehom]; simp
    have hdA0 : dA = 0 := by
      by_contra hpos
      have hX2A : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ A := by
        rw [hA_eq]; exact dvd_mul_of_dvd_right (dvd_pow_self _ hpos) _
      exact hX2_ndvd (hX2A.trans ⟨B, hAB'⟩)
    subst hdA0
    rw [hA_eq, pow_zero, mul_one]
    exact hcU.map MvPolynomial.C
  · right
    obtain ⟨c, hcU, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp huB
    have hB_eq : B = MvPolynomial.C c * MvPolynomial.X 2 ^ dB := by
      apply dehom_inj_on_homogeneous dB hB_hom
      · simpa using (MvPolynomial.isHomogeneous_C (Fin 3) c).mul
          ((MvPolynomial.isHomogeneous_X K (2 : Fin 3)).pow dB)
      · rw [hc, map_mul, map_pow, dehom]; simp
    have hdB0 : dB = 0 := by
      by_contra hpos
      have hX2B : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ B := by
        rw [hB_eq]; exact dvd_mul_of_dvd_right (dvd_pow_self _ hpos) _
      exact hX2_ndvd (hX2B.trans ⟨A, by rw [hAB', mul_comm]⟩)
    subst hdB0
    rw [hB_eq, pow_zero, mul_one]
    exact hcU.map MvPolynomial.C

/-- Homogeneous scaling of evaluation for a homogeneous 3-variable polynomial. -/
theorem eval_smul_homogeneous {P : MvPolynomial (Fin 3) L} {s : ℕ}
    (hP : P.IsHomogeneous s) (c a b d : L) :
    MvPolynomial.eval ![c * a, c * b, c * d] P = c ^ s * MvPolynomial.eval ![a, b, d] P := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hedeg : e 0 + e 1 + e 2 = s := by
    have h := hP (MvPolynomial.mem_support_iff.mp he)
    rwa [weight_one_eq_sum, m3_sum] at h
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, mul_pow]
  rw [← hedeg, pow_add, pow_add]
  ring

/-- The invertible coordinate-swap matrix sending `(H, R, V) = (X 0, X 1, X 2)` to
`(F_Y, -F_T, -F_Z)` inside `gaussPullback`. -/
def dualSwapMatrix (L : Type*) [Field L] : Matrix (Fin 3) (Fin 3) L :=
  Matrix.of ![![0, 1, 0], ![0, 0, -1], ![-1, 0, 0]]

/-- Inverse of `dualSwapMatrix`. -/
def dualSwapMatrixInv (L : Type*) [Field L] : Matrix (Fin 3) (Fin 3) L :=
  Matrix.of ![![0, 0, -1], ![1, 0, 0], ![0, -1, 0]]

theorem dualSwapMatrix_mul_inv :
    dualSwapMatrix L * dualSwapMatrixInv L = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [dualSwapMatrix, dualSwapMatrixInv]

theorem dualSwapMatrixInv_mul :
    dualSwapMatrixInv L * dualSwapMatrix L = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [dualSwapMatrix, dualSwapMatrixInv]

theorem eval_substLin_dualSwap (Q : MvPolynomial (Fin 3) L) (a b c : L) :
    MvPolynomial.eval ![a, b, c] (substLin (dualSwapMatrix L) Q) =
      MvPolynomial.eval ![b, -c, -a] Q := by
  have hcomp : (MvPolynomial.aeval (R := L) ![a, b, c]).comp (substLin (dualSwapMatrix L)) =
      MvPolynomial.aeval (R := L) ![b, -c, -a] := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, substLin_X, Fin.sum_univ_three]
    fin_cases i <;> simp [dualSwapMatrix]
  exact AlgHom.congr_fun hcomp Q

/-- `X 1`-degree upper bound for `pderiv i F`. -/
private theorem ydeg_pderiv_le {F : MvPolynomial (Fin 3) L} {b : ℕ}
    (hF : ∀ e ∈ F.support, e 1 ≤ b) (i : Fin 3) :
    ∀ e ∈ (pderiv i F).support, e 1 ≤ b := by
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at he
  have hne : F.coeff (e + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul he
  have hle := hF _ (MvPolynomial.mem_support_iff.mpr hne)
  have : e 1 ≤ (e + Finsupp.single i 1 : Fin 3 →₀ ℕ) 1 := by simp
  omega

/-- `X 1`-degree upper bound for `gaussPullback F P`. -/
private theorem ydeg_gaussPullback_le {F P : MvPolynomial (Fin 3) L} {b s : ℕ}
    (hF : ∀ e ∈ F.support, e 1 ≤ b) (hP : P.IsHomogeneous s) :
    ∀ e ∈ (gaussPullback F P).support, e 1 ≤ s * b := by
  classical
  have hmul : ∀ (A B : MvPolynomial (Fin 3) L) (k₁ k₂ : ℕ),
      (∀ e ∈ A.support, e 1 ≤ k₁) → (∀ e ∈ B.support, e 1 ≤ k₂) →
      ∀ e ∈ (A * B).support, e 1 ≤ k₁ + k₂ := by
    intro A B k₁ k₂ hA hB e he
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at he
    obtain ⟨⟨u, v⟩, huv, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    have hu := hA u (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne))
    have hv := hB v (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne))
    have heq : u + v = e := Finset.mem_antidiagonal.mp huv
    rw [← heq, Finsupp.add_apply]; omega
  have hpow : ∀ (A : MvPolynomial (Fin 3) L) (k n : ℕ),
      (∀ e ∈ A.support, e 1 ≤ k) → ∀ e ∈ (A ^ n).support, e 1 ≤ n * k := by
    intro A k n hA
    induction n with
    | zero =>
      intro e he
      rw [pow_zero, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at he
      split_ifs at he with h0
      · rw [← h0]; simp
      · exact absurd rfl he
    | succ n ih =>
      intro e he
      rw [pow_succ] at he
      have := hmul (A ^ n) A (n * k) k ih hA e he
      linarith
  have hpd (i : Fin 3) : ∀ e ∈ (pderiv i F).support, e 1 ≤ b := ydeg_pderiv_le hF i
  intro e he
  rw [P.as_sum, gaussPullback, map_sum, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at he
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have hmdeg : m 0 + m 1 + m 2 = s := by
    have h := hP (MvPolynomial.mem_support_iff.mp hm)
    rwa [weight_one_eq_sum, m3_sum] at h
  have hmon : MvPolynomial.monomial m (P.coeff m) =
      MvPolynomial.C (P.coeff m) * MvPolynomial.X 0 ^ m 0 *
        MvPolynomial.X 1 ^ m 1 * MvPolynomial.X 2 ^ m 2 := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.X,
      MvPolynomial.monomial_pow, MvPolynomial.monomial_pow, MvPolynomial.monomial_pow,
      MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial,
      MvPolynomial.monomial_mul_monomial]
    simp only [one_pow, mul_one, Finsupp.smul_single, smul_eq_mul]
    exact congrArg (fun d => MvPolynomial.monomial d (P.coeff m)) (by ext i; fin_cases i <;> simp)
  rw [hmon, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X] at hne
  have hC : ∀ t ∈ (MvPolynomial.C (P.coeff m) : MvPolynomial (Fin 3) L).support, t 1 ≤ 0 := by
    intro t ht
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at ht
    split_ifs at ht with h0
    · rw [← h0]; simp
    · exact absurd rfl ht
  have h0 := hmul _ _ 0 (m 0 * b) hC (hpow _ b (m 0) (hpd 0))
  have h1 := hmul _ _ (0 + m 0 * b) (m 1 * b) h0 (hpow _ b (m 1) (hpd 1))
  have h2 := hmul _ _ (0 + m 0 * b + m 1 * b) (m 2 * b) h1 (hpow _ b (m 2) (hpd 2))
  have hmem : e ∈ (MvPolynomial.C (P.coeff m) * pderiv 0 F ^ m 0 *
      pderiv 1 F ^ m 1 * pderiv 2 F ^ m 2).support :=
    MvPolynomial.mem_support_iff.mpr hne
  have hle := h2 e hmem
  have hsum : 0 + m 0 * b + m 1 * b + m 2 * b = s * b := by
    rw [zero_add, ← add_mul, ← add_mul, hmdeg]
  omega

/-- Evaluating `mv2EquivBiv (dehom (gaussPullback F (substLin dualSwapMatrix Q)))` at `(z, y)` on
the curve `f(z, y) = 0` vanishes whenever `Q(H, R, V) = 0` for the tangent `[H : R : V]`. -/
private theorem eval_polar_eq_zero_of_tangent {f : L[X][X]} {m s : ℕ}
    (hm_eq : (mv2EquivBiv.symm f).totalDegree = m)
    {Q : MvPolynomial (Fin 3) L} (hQ_hom : Q.IsHomogeneous s)
    {z y H R V : L}
    (hf : (f.map (evalRingHom z)).eval y = 0)
    (hH : H ≠ 0)
    (htan : H * MvPolynomial.eval ![z, y] (pderiv 0 (mv2EquivBiv.symm f)) +
        V * MvPolynomial.eval ![z, y] (pderiv 1 (mv2EquivBiv.symm f)) = 0)
    (hR : R = y * H - z * V)
    (hQvan : MvPolynomial.eval ![H, R, V] Q = 0) :
    let F := homog m (mv2EquivBiv.symm f)
    let P := substLin (dualSwapMatrix L) Q
    ((mv2EquivBiv (dehom (gaussPullback F P))).map (evalRingHom z)).eval y = 0 := by
  intro F P
  have hF_hom : F.IsHomogeneous m := homog_isHomogeneous m (mv2EquivBiv.symm f) (le_of_eq hm_eq)
  have hF_dehom : dehom F = mv2EquivBiv.symm f := dehom_homog m (mv2EquivBiv.symm f)
  have hev_dehom (G : MvPolynomial (Fin 3) L) :
      MvPolynomial.eval ![z, y] (dehom G) = MvPolynomial.eval ![z, y, 1] G := by
    have hc : (MvPolynomial.aeval (R := L) ![z, y]).comp dehom =
        MvPolynomial.aeval (R := L) ![z, y, 1] := by
      apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp [dehom]
    exact AlgHom.congr_fun hc G
  rw [eval_mv2EquivBiv_K, hev_dehom]
  have hgp : MvPolynomial.eval ![z, y, 1] (gaussPullback F P) =
      MvPolynomial.eval ![MvPolynomial.eval ![z, y, 1] (pderiv 0 F),
        MvPolynomial.eval ![z, y, 1] (pderiv 1 F),
        MvPolynomial.eval ![z, y, 1] (pderiv 2 F)] P := by
    have hc : (MvPolynomial.aeval (R := L) ![z, y, 1]).comp
          (MvPolynomial.aeval ![pderiv 0 F, pderiv 1 F, pderiv 2 F]) =
        MvPolynomial.aeval (R := L) ![MvPolynomial.eval ![z, y, 1] (pderiv 0 F),
          MvPolynomial.eval ![z, y, 1] (pderiv 1 F),
          MvPolynomial.eval ![z, y, 1] (pderiv 2 F)] := by
      apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp
    exact AlgHom.congr_fun hc P
  rw [hgp]
  dsimp only [P]
  rw [eval_substLin_dualSwap]
  let fZ := MvPolynomial.eval ![z, y, 1] (pderiv 0 F)
  let fY := MvPolynomial.eval ![z, y, 1] (pderiv 1 F)
  let fT := MvPolynomial.eval ![z, y, 1] (pderiv 2 F)
  have hfZ_eq : fZ = MvPolynomial.eval ![z, y] (pderiv 0 (mv2EquivBiv.symm f)) := by
    dsimp only [fZ]; rw [← hev_dehom]
    change MvPolynomial.eval ![z, y] (dehom (pderiv (Fin.castSucc 0) F)) = _
    rw [← pderiv_dehom F 0, hF_dehom]
  have hfY_eq : fY = MvPolynomial.eval ![z, y] (pderiv 1 (mv2EquivBiv.symm f)) := by
    dsimp only [fY]; rw [← hev_dehom]
    change MvPolynomial.eval ![z, y] (dehom (pderiv (Fin.castSucc 1) F)) = _
    rw [← pderiv_dehom F 1, hF_dehom]
  have heuler : z * fZ + y * fY + fT = 0 := by
    have h1 := congrArg (MvPolynomial.eval ![z, y, 1]) (IsHomogeneous.sum_X_mul_pderiv hF_hom)
    rw [Fin.sum_univ_three] at h1
    simp only [map_add, map_mul, map_nsmul, MvPolynomial.eval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, one_mul] at h1
    have hF0 : MvPolynomial.eval ![z, y, 1] F = 0 := by
      rw [← hev_dehom, hF_dehom, ← eval_mv2EquivBiv_K, RingEquiv.apply_symm_apply]
      exact hf
    rw [hF0, nsmul_zero] at h1
    exact h1
  let c : L := fY / H
  have hcY : fY = c * H := (div_mul_cancel₀ fY hH).symm
  have hcZ : -fZ = c * V := by
    dsimp only [c]
    rw [div_mul_eq_mul_div, eq_div_iff hH]
    rw [← hfZ_eq, ← hfY_eq] at htan
    linear_combination -htan
  have hcT : -fT = c * R := by
    rw [hR]
    linear_combination -heuler + y * hcY - z * hcZ
  change MvPolynomial.eval ![fY, -fT, -fZ] Q = 0
  rw [hcY, hcT, hcZ, eval_smul_homogeneous hQ_hom c H R V, hQvan, mul_zero]

/-- Irreducibility descends along an injective base field extension `mapBiv φ`. -/
private theorem irreducible_of_mapBiv_irreducible (φ : L →+* K) (hφ : Function.Injective φ)
    {f : L[X][X]} (hf_irr : Irreducible (mapBiv φ f)) : Irreducible f := by
  have hisUnit : ∀ a : L[X][X], IsUnit (mapBiv φ a) → IsUnit a := by
    intro a hua
    obtain ⟨u, hu⟩ := hua
    have h1 : mapBiv φ a * u.inv = 1 := hu ▸ u.val_inv
    have hne1 : mapBiv φ a ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
    have hne2 : u.inv ≠ 0 := fun h => by rw [h, mul_zero] at h1; exact zero_ne_one h1
    have hdeg0 : (mapBiv φ a).natDegree = 0 := by
      have h := Polynomial.natDegree_mul hne1 hne2
      rw [h1, Polynomial.natDegree_one] at h; omega
    have ha_deg0 : a.natDegree = 0 := by
      have h := Polynomial.natDegree_map_eq_of_injective
        (show Function.Injective (Polynomial.mapRingHom φ) from Polynomial.map_injective φ hφ) a
      change (mapBiv φ a).natDegree = a.natDegree at h
      omega
    have haC : a = Polynomial.C (a.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero ha_deg0
    have hc0_map : IsUnit ((a.coeff 0).map φ) := by
      have hmapC : mapBiv φ (Polynomial.C (a.coeff 0)) = Polynomial.C ((a.coeff 0).map φ) := by
        simp [mapBiv]
      rw [haC, hmapC] at hu
      exact Polynomial.isUnit_C.mp ⟨u, hu⟩
    have hcd0 : (a.coeff 0).natDegree = 0 := by
      have h := Polynomial.natDegree_eq_zero_of_isUnit hc0_map
      rwa [Polynomial.natDegree_map_eq_of_injective hφ] at h
    have hc0_ne : a.coeff 0 ≠ 0 := fun h0 => by
      rw [h0, map_zero] at haC
      exact hne1 (by rw [haC, map_zero])
    have hcc_ne : (a.coeff 0).coeff 0 ≠ 0 := fun h0 => by
      apply hc0_ne
      rw [Polynomial.eq_C_of_natDegree_eq_zero hcd0, h0, map_zero]
    rw [haC, Polynomial.eq_C_of_natDegree_eq_zero hcd0]
    exact (hcc_ne.isUnit.map Polynomial.C).map Polynomial.C
  refine ⟨fun hu => hf_irr.not_isUnit (hu.map (mapBiv φ)), fun a b hab => ?_⟩
  have hmap_ab : mapBiv φ f = mapBiv φ a * mapBiv φ b := by rw [hab, map_mul]
  rcases hf_irr.isUnit_or_isUnit hmap_ab with hua | hub
  · exact Or.inl (hisUnit a hua)
  · exact Or.inr (hisUnit b hub)

end Helpers

section MainTheorems

variable {L : Type*} [Field L]

/-- **Pardini Reflexivity over an arbitrary field `L`**: if `F` is geometrically irreducible of
degree `m ≥ 2` and `P ≠ 0` is homogeneous of degree `s` with `s * (s - 1) < m` (and
`char L = 0 ∨ m * (m - 1) < char L`), then `¬ F ∣ gaussPullback F P`. -/
theorem gaussPullback_not_dvd_of_gt {F P : MvPolynomial (Fin 3) L} {m s : ℕ}
    (hF_geom : Irreducible (MvPolynomial.map (algebraMap L (AlgebraicClosure L)) F))
    (hF_hom : F.IsHomogeneous m) (hm : 2 ≤ m)
    (hP_hom : P.IsHomogeneous s) (hP_ne : P ≠ 0)
    (hms : s * (s - 1) < m)
    (hchar : ∀ k : ℕ, 0 < k → k ≤ m * (m - 1) → (k : L) ≠ 0) :
    ¬ F ∣ gaussPullback F P := by
  intro hdvd
  let ι := algebraMap L (AlgebraicClosure L)
  have hP_bar_ne : MvPolynomial.map ι P ≠ 0 := by
    intro h0
    exact hP_ne (MvPolynomial.map_injective ι ι.injective (by rw [h0, map_zero]))
  have hchar_bar : ∀ k : ℕ, 0 < k → k ≤ m * (m - 1) → (k : AlgebraicClosure L) ≠ 0 := by
    intro k hk1 hk2 h0
    apply hchar k hk1 hk2
    apply ι.injective
    simpa [map_natCast] using h0
  have hdvd_bar : MvPolynomial.map ι F ∣ gaussPullback (MvPolynomial.map ι F) (MvPolynomial.map ι P) := by
    rw [← map_gaussPullback]
    exact map_dvd (MvPolynomial.map ι) hdvd
  have hle := (pardini_reflexivity hF_geom (map_isHomogeneous ι hF_hom) hm hchar_bar
    s (MvPolynomial.map ι P) (map_isHomogeneous ι hP_hom) hP_bar_ne hdvd_bar).2
  omega

/-- **Polar Affine Intersection Cap (L2a + L2b + L2c)**:
For a geometrically irreducible affine plane curve `f : L[X][X]` of exact total degree `m ≥ 2` and
`Y`-degree `≤ b ≤ m`, any nonzero homogeneous degree-`s` dual curve `Q(H, R, V)` with
`s * (s - 1) < m` (and `char L = 0 ∨ m * (m - 1) < char L`) vanishes on the projective tangents of
at most `s * (m * (m - 1) - (m - b) * (m - b - 1))` distinct affine points of `f = 0`. -/
theorem polar_affine_card_le (f : L[X][X]) {m b s : ℕ}
    (hm_eq : (mv2EquivBiv.symm f).totalDegree = m) (hm : 2 ≤ m)
    (hb : f.natDegree ≤ b) (hbm : b ≤ m)
    (hf_geom : Irreducible (mapBiv (algebraMap L (AlgebraicClosure L)) f))
    (hchar : ∀ k : ℕ, 0 < k → k ≤ m * (m - 1) → (k : L) ≠ 0)
    (Q : MvPolynomial (Fin 3) L) (hQ_hom : Q.IsHomogeneous s) (hQ_ne : Q ≠ 0)
    (hms : s * (s - 1) < m)
    (S : Finset (L × L))
    (hfS : ∀ p ∈ S, (f.map (evalRingHom p.1)).eval p.2 = 0)
    (H R V : L × L → L)
    (hH : ∀ p ∈ S, H p ≠ 0)
    (htan : ∀ p ∈ S, H p * MvPolynomial.eval ![p.1, p.2] (pderiv 0 (mv2EquivBiv.symm f)) +
        V p * MvPolynomial.eval ![p.1, p.2] (pderiv 1 (mv2EquivBiv.symm f)) = 0)
    (hR : ∀ p ∈ S, R p = p.2 * H p - p.1 * V p)
    (hQvan : ∀ p ∈ S, MvPolynomial.eval ![H p, R p, V p] Q = 0) :
    S.card ≤ s * (m * (m - 1) - (m - b) * (m - b - 1)) := by
  classical
  let ι := algebraMap L (AlgebraicClosure L)
  let fMv : MvPolynomial (Fin 2) L := mv2EquivBiv.symm f
  let F : MvPolynomial (Fin 3) L := homog m fMv
  have hF_hom : F.IsHomogeneous m := homog_isHomogeneous m fMv (le_of_eq hm_eq)
  have hF_dehom : dehom F = fMv := dehom_homog m fMv
  -- Show `F` is geometrically irreducible via `irreducible_homog_of_irreducible_biv`.
  have hF_geom : Irreducible (MvPolynomial.map ι F) := by
    have hmap : MvPolynomial.map ι F = homog m (mv2EquivBiv.symm (mapBiv ι f)) := by
      dsimp only [F]
      rw [map_homog ι ι.injective m fMv]
      congr 1
      apply mv2EquivBiv.injective
      rw [RingEquiv.apply_symm_apply, ← mapBiv_mv2EquivBiv, RingEquiv.apply_symm_apply]
    have hdeg_bar : (mv2EquivBiv.symm (mapBiv ι f)).totalDegree = m := by
      have heq : mv2EquivBiv.symm (mapBiv ι f) = MvPolynomial.map ι fMv := by
        apply mv2EquivBiv.injective
        rw [RingEquiv.apply_symm_apply, ← mapBiv_mv2EquivBiv, RingEquiv.apply_symm_apply]
      rw [heq]
      apply le_antisymm ((totalDegree_map_le' ι fMv).trans (le_of_eq hm_eq))
      calc m = fMv.totalDegree := hm_eq.symm
        _ ≤ (MvPolynomial.map ι fMv).totalDegree := by
            refine totalDegree_le_of_forall_mem_support fun e he => ?_
            have he' : (MvPolynomial.map ι fMv).coeff e ≠ 0 := by
              rw [MvPolynomial.coeff_map]
              exact (map_ne_zero_iff ι ι.injective).mpr (MvPolynomial.mem_support_iff.mp he)
            exact Finset.le_sup (f := fun t : Fin 2 →₀ ℕ => t.sum fun _ v => v)
              (MvPolynomial.mem_support_iff.mpr he')
    rw [hmap]
    exact irreducible_homog_of_irreducible_biv hf_geom hdeg_bar
  -- Also `f` itself is irreducible over `L`.
  have hf_irr : Irreducible f := irreducible_of_mapBiv_irreducible ι ι.injective hf_geom
  -- Build `P = substLin dualSwapMatrix Q` and polar `g = mv2EquivBiv (dehom (gaussPullback F P))`.
  let P : MvPolynomial (Fin 3) L := substLin (dualSwapMatrix L) Q
  have hP_hom : P.IsHomogeneous s := substLin_isHomogeneous (dualSwapMatrix L) hQ_hom
  have hP_ne : P ≠ 0 := by
    intro h0
    have := congrArg (substLin (dualSwapMatrixInv L)) h0
    rw [← AlgHom.comp_apply, substLin_comp, dualSwapMatrix_mul_inv, substLin_one,
      AlgHom.id_apply, map_zero] at this
    exact hQ_ne this
  have hndvd_F : ¬ F ∣ gaussPullback F P :=
    gaussPullback_not_dvd_of_gt hF_geom hF_hom hm hP_hom hP_ne hms hchar
  let G : MvPolynomial (Fin 3) L := gaussPullback F P
  have hG_hom : G.IsHomogeneous (s * (m - 1)) := gaussPullback_isHomogeneous hF_hom hP_hom
  let g : L[X][X] := mv2EquivBiv (dehom G)
  have hf_ndvd_g : ¬ f ∣ g := by
    intro ⟨q, hq⟩
    have hdehom_dvd : dehom F ∣ dehom G := by
      refine ⟨mv2EquivBiv.symm q, ?_⟩
      rw [hF_dehom]
      apply mv2EquivBiv.injective
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact hq
    have hX2 : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) L) ∣ F := by
      dsimp only [F]; rw [← hm_eq]
      exact X2_not_dvd_homog fMv (fun h0 => hf_irr.ne_zero (by
        have := congrArg mv2EquivBiv h0; simpa [fMv] using this))
    exact hndvd_F (dvd_of_dehom_dvd hF_hom hX2 hG_hom hdehom_dvd)
  -- Degree bounds on `f` and `g`.
  have hf_tot : WeightedSylvesterDegree.TotalDegreeLe f m := by
    rw [show f = mv2EquivBiv fMv from (RingEquiv.apply_symm_apply mv2EquivBiv f).symm,
      totalDegreeLe_mv2EquivBiv_iff]
    exact le_of_eq hm_eq
  have hg_tot : WeightedSylvesterDegree.TotalDegreeLe g (s * (m - 1)) := by
    rw [totalDegreeLe_mv2EquivBiv_iff]
    exact totalDegree_dehom_le hG_hom
  have hF_ydeg : ∀ e ∈ F.support, e 1 ≤ b := by
    intro e he
    dsimp only [F, homog] at he
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at he
    obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    rw [MvPolynomial.coeff_monomial] at hne
    split_ifs at hne with heq
    · rw [← heq]
      simp only [ext3_apply_1]
      have hfn : (f.coeff (n 1)).coeff (n 0) ≠ 0 := by
        have h1 := coeff_mv2EquivBiv fMv (n 1) (n 0)
        rw [RingEquiv.apply_symm_apply] at h1
        have hn_eq : Finsupp.single (0 : Fin 2) (n 0) + Finsupp.single 1 (n 1) = n := by
          ext t; fin_cases t <;> simp
        rw [h1, hn_eq]
        exact MvPolynomial.mem_support_iff.mp hn
      have hcn : f.coeff (n 1) ≠ 0 := by intro h0; rw [h0, Polynomial.coeff_zero] at hfn; exact hfn rfl
      exact (Polynomial.le_natDegree_of_ne_zero hcn).trans hb
    · exact absurd rfl hne
  have hG_ydeg : ∀ e ∈ G.support, e 1 ≤ s * b := ydeg_gaussPullback_le hF_ydeg hP_hom
  have hg_deg_sb : g.natDegree ≤ s * b := by
    refine natDegree_mv2EquivBiv_le (dehom G) (s * b) fun e he => ?_
    rw [G.as_sum, map_sum, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at he
    obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    rw [dehom_monomial, MvPolynomial.coeff_monomial] at hne
    split_ifs at hne with heq
    · rw [← heq, proj2_apply_1]; exact hG_ydeg n hn
    · exact absurd rfl hne
  have hg_deg_d' : g.natDegree ≤ s * (m - 1) := by
    refine natDegree_mv2EquivBiv_le (dehom G) (s * (m - 1)) fun e he => ?_
    have h1 := (Finset.le_sup (f := fun t : Fin 2 →₀ ℕ => t.sum fun _ v => v) he).trans
      (totalDegree_dehom_le hG_hom)
    rw [m2_sum] at h1; omega
  let b' : ℕ := min (s * b) (s * (m - 1))
  have hg_deg : g.natDegree ≤ b' := le_min hg_deg_sb hg_deg_d'
  have hb'_le : b' ≤ s * (m - 1) := min_le_right _ _
  have hgS : ∀ p ∈ S, (g.map (evalRingHom p.1)).eval p.2 = 0 := fun p hp =>
    eval_polar_eq_zero_of_tangent hm_eq hQ_hom (hfS p hp) (hH p hp) (htan p hp) (hR p hp) (hQvan p hp)
  have hbez := plane_bezout_irreducible_with_multiplicity f g
    hf_irr hf_ndvd_g hf_tot hg_tot hb hbm hg_deg hb'_le S (fun p hp => ⟨hfS p hp, hgS p hp⟩)
  -- Simplify `m * (s * (m - 1)) - (m - b) * (s * (m - 1) - min (s * b) (s * (m - 1)))`.
  have hsimp : m * (s * (m - 1)) - (m - b) * (s * (m - 1) - b') =
      s * (m * (m - 1) - (m - b) * (m - b - 1)) := by
    by_cases hbm_eq : b = m
    · subst hbm_eq
      simp only [Nat.sub_self, zero_mul, Nat.sub_zero]
      ring
    · have hb_lt : b ≤ m - 1 := by omega
      have hmin : b' = s * b := min_eq_left (Nat.mul_le_mul_left s hb_lt)
      rw [hmin, ← Nat.mul_sub_left_distrib, show m - 1 - b = m - b - 1 by omega]
      have hle1 : (m - b) * (s * (m - b - 1)) = s * ((m - b) * (m - b - 1)) := by ring
      have hle2 : m * (s * (m - 1)) = s * (m * (m - 1)) := by ring
      rw [hle1, hle2, ← Nat.mul_sub_left_distrib]
  exact hsimp ▸ hbez

/-- **Smooth-Point Polar Cap**: discharges geometric irreducibility automatically via L2a
(`irreducible_algebraicClosure_of_smooth`) from a single smooth `L`-point `(z₀, y₀)` of `f = 0`. -/
theorem polar_affine_card_le_of_smooth (f : L[X][X]) {m b s : ℕ}
    (hf_irr : Irreducible f)
    (hm_eq : (mv2EquivBiv.symm f).totalDegree = m) (hm : 2 ≤ m)
    (hb : f.natDegree ≤ b) (hbm : b ≤ m)
    (z₀ y₀ : L)
    (hroot : (f.map (evalRingHom z₀)).eval y₀ = 0)
    (hsmooth : (f.derivative.map (evalRingHom z₀)).eval y₀ ≠ 0 ∨
      ((f.map (evalRingHom z₀)).eval y₀ = 0 ∧
        MvPolynomial.eval ![z₀, y₀] (pderiv 0 (mv2EquivBiv.symm f)) ≠ 0))
    (hchar : ∀ k : ℕ, 0 < k → k ≤ m * (m - 1) → (k : L) ≠ 0)
    (Q : MvPolynomial (Fin 3) L) (hQ_hom : Q.IsHomogeneous s) (hQ_ne : Q ≠ 0)
    (hms : s * (s - 1) < m)
    (S : Finset (L × L))
    (hfS : ∀ p ∈ S, (f.map (evalRingHom p.1)).eval p.2 = 0)
    (H R V : L × L → L)
    (hH : ∀ p ∈ S, H p ≠ 0)
    (htan : ∀ p ∈ S, H p * MvPolynomial.eval ![p.1, p.2] (pderiv 0 (mv2EquivBiv.symm f)) +
        V p * MvPolynomial.eval ![p.1, p.2] (pderiv 1 (mv2EquivBiv.symm f)) = 0)
    (hR : ∀ p ∈ S, R p = p.2 * H p - p.1 * V p)
    (hQvan : ∀ p ∈ S, MvPolynomial.eval ![H p, R p, V p] Q = 0) :
    S.card ≤ s * (m * (m - 1) - (m - b) * (m - b - 1)) := by
  have hf_geom : Irreducible (mapBiv (algebraMap L (AlgebraicClosure L)) f) := by
    rcases hsmooth with hy | ⟨_, hz⟩
    · exact irreducible_algebraicClosure_of_smooth_y f hf_irr z₀ y₀ hroot hy
    · -- Swap `(Z, Y)` via `Bivariate.swap` and use `irreducible_algebraicClosure_of_smooth`.
      refine irreducible_algebraicClosure_of_smooth f hf_irr z₀ y₀ hroot (Or.inr ?_)
      have hswap_C_X : Bivariate.swap (Polynomial.C (Polynomial.X : L[X])) = (Polynomial.X : L[X][X]) := by
        simp [Bivariate.swap]
      have hswap_X : Bivariate.swap (Polynomial.X : L[X][X]) = Polynomial.C (Polynomial.X : L[X]) := by
        simp [Bivariate.swap]
      have heval_swap (a : MvPolynomial (Fin 2) L) :
          ((Bivariate.swap (mv2EquivBiv a)).map (evalRingHom y₀)).eval z₀ =
            MvPolynomial.eval ![z₀, y₀] a := by
        induction a using MvPolynomial.induction_on with
        | C c => simp [Bivariate.swap]
        | add p q hp hq =>
          rw [map_add, map_add, Polynomial.map_add, Polynomial.eval_add, map_add, hp, hq]
        | mul_X p i hp =>
          rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
          · rw [map_mul, mv2EquivBiv_X0, map_mul, hswap_C_X, Polynomial.map_mul, Polynomial.map_X,
              Polynomial.eval_mul, Polynomial.eval_X, hp, map_mul, MvPolynomial.eval_X,
              Matrix.cons_val_zero]
          · rw [map_mul, mv2EquivBiv_X1, map_mul, hswap_X, Polynomial.map_mul, Polynomial.map_C,
              Polynomial.eval_mul, Polynomial.eval_C, Polynomial.coe_evalRingHom, Polynomial.eval_X, hp,
              map_mul, MvPolynomial.eval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
      have hswap_der : ((Bivariate.swap f).derivative.map (evalRingHom y₀)).eval z₀ =
          MvPolynomial.eval ![z₀, y₀] (pderiv 0 (mv2EquivBiv.symm f)) := by
        let g := mv2EquivBiv.symm f
        have hg : f = mv2EquivBiv g := (RingEquiv.apply_symm_apply mv2EquivBiv f).symm
        rw [hg, RingEquiv.symm_apply_apply]
        clear hg hf_irr hm_eq hb hroot hz htan hfS
        induction g using MvPolynomial.induction_on with
        | C c => simp [Bivariate.swap]
        | add a b ha hb =>
          rw [map_add, map_add, Polynomial.derivative_add, Polynomial.map_add,
            Polynomial.eval_add, map_add, map_add, ha, hb]
        | mul_X a i ha =>
          rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
          · have hsw : Bivariate.swap (mv2EquivBiv (a * MvPolynomial.X 0)) =
                Bivariate.swap (mv2EquivBiv a) * Polynomial.X := by
              rw [map_mul, mv2EquivBiv_X0, map_mul, hswap_C_X]
            rw [hsw, Polynomial.derivative_mul, Polynomial.derivative_X, mul_one,
              Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
              Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, ha,
              pderiv_mul, pderiv_X_self, mul_one, map_add, map_mul, MvPolynomial.eval_X,
              Matrix.cons_val_zero, heval_swap a]
          · have hsw : Bivariate.swap (mv2EquivBiv (a * MvPolynomial.X 1)) =
                Bivariate.swap (mv2EquivBiv a) * Polynomial.C Polynomial.X := by
              rw [map_mul, mv2EquivBiv_X1, map_mul, hswap_X]
            rw [hsw, Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero, add_zero,
              Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.coe_evalRingHom, Polynomial.eval_X, ha,
              pderiv_mul, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero, add_zero,
              map_mul, MvPolynomial.eval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
      rwa [hswap_der]
  exact polar_affine_card_le f hm_eq hm hb hbm hf_geom hchar Q hQ_hom hQ_ne hms S hfS H R V hH htan hR hQvan

/-- **Beyond-Johnson Conic 5-Column Polar Cap (`m = 2`)**:
For any geometrically irreducible conic `f : L[X][X]` of exact total degree `2` over a field `L`
with `(2 : L) ≠ 0`, there is a degree-2 monomial `e₀ = (i, j)` (`i + j = 2`) such that EVERY
nonzero quadratic `Q(H, R, V)` with vanishing `R^i V^j`-coefficient gives a polar pullback
vanishing on at most `4` distinct affine points of `f = 0`. -/
theorem conic_five_column_polar_cap (f : L[X][X])
    (hm_eq : (mv2EquivBiv.symm f).totalDegree = 2)
    (hf_geom : Irreducible (mapBiv (algebraMap L (AlgebraicClosure L)) f))
    (hchar2 : (2 : L) ≠ 0) :
    ∃ e₀ : ℕ × ℕ, e₀.1 + e₀.2 = 2 ∧
      ∀ (Q : MvPolynomial (Fin 3) L), Q.IsHomogeneous 2 → Q ≠ 0 →
        Q.coeff (Finsupp.single 1 e₀.1 + Finsupp.single 2 e₀.2) = 0 →
        ∀ (S : Finset (L × L)),
          (∀ p ∈ S, (f.map (evalRingHom p.1)).eval p.2 = 0) →
          ∀ (H R V : L × L → L),
            (∀ p ∈ S, H p ≠ 0) →
            (∀ p ∈ S, H p * MvPolynomial.eval ![p.1, p.2] (pderiv 0 (mv2EquivBiv.symm f)) +
              V p * MvPolynomial.eval ![p.1, p.2] (pderiv 1 (mv2EquivBiv.symm f)) = 0) →
            (∀ p ∈ S, R p = p.2 * H p - p.1 * V p) →
            (∀ p ∈ S, MvPolynomial.eval ![H p, R p, V p] Q = 0) →
            S.card ≤ 4 := by
  classical
  let ι := algebraMap L (AlgebraicClosure L)
  let fMv : MvPolynomial (Fin 2) L := mv2EquivBiv.symm f
  let F : MvPolynomial (Fin 3) L := homog 2 fMv
  have hF_hom : F.IsHomogeneous 2 := homog_isHomogeneous 2 fMv (le_of_eq hm_eq)
  have hF_dehom : dehom F = fMv := dehom_homog 2 fMv
  have hF_geom : Irreducible (MvPolynomial.map ι F) := by
    have hmap : MvPolynomial.map ι F = homog 2 (mv2EquivBiv.symm (mapBiv ι f)) := by
      dsimp only [F]
      rw [map_homog ι ι.injective 2 fMv]
      congr 1
      apply mv2EquivBiv.injective
      rw [RingEquiv.apply_symm_apply, ← mapBiv_mv2EquivBiv, RingEquiv.apply_symm_apply]
    have hdeg_bar : (mv2EquivBiv.symm (mapBiv ι f)).totalDegree = 2 := by
      have heq : mv2EquivBiv.symm (mapBiv ι f) = MvPolynomial.map ι fMv := by
        apply mv2EquivBiv.injective
        rw [RingEquiv.apply_symm_apply, ← mapBiv_mv2EquivBiv, RingEquiv.apply_symm_apply]
      rw [heq]
      apply le_antisymm ((totalDegree_map_le' ι fMv).trans (le_of_eq hm_eq))
      calc 2 = fMv.totalDegree := hm_eq.symm
        _ ≤ (MvPolynomial.map ι fMv).totalDegree := by
            refine totalDegree_le_of_forall_mem_support fun e he => ?_
            have he' : (MvPolynomial.map ι fMv).coeff e ≠ 0 := by
              rw [MvPolynomial.coeff_map]
              exact (map_ne_zero_iff ι ι.injective).mpr (MvPolynomial.mem_support_iff.mp he)
            exact Finset.le_sup (f := fun t : Fin 2 →₀ ℕ => t.sum fun _ v => v)
              (MvPolynomial.mem_support_iff.mpr he')
    rw [hmap]
    exact irreducible_homog_of_irreducible_biv hf_geom hdeg_bar
  -- The gradient of a degree-2 homogeneous polynomial `F` is linear: `pderiv i F = ∑ j, C (A i j) * X j`.
  let A : Matrix (Fin 3) (Fin 3) L := Matrix.of fun i j => (pderiv i F).coeff (Finsupp.single j 1)
  have hpd_lin (i : Fin 3) : pderiv i F = ∑ j : Fin 3, MvPolynomial.C (A i j) * MvPolynomial.X j := by
    have hhom : (pderiv i F).IsHomogeneous 1 := hF_hom.pderiv
    have hsub : (pderiv i F).support ⊆ {Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 2 1} := by
      intro e he
      have hdeg := hhom (MvPolynomial.mem_support_iff.mp he)
      rw [weight_one_eq_sum, m3_sum] at hdeg
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h0 : e 0 = 1
      · left; ext k; fin_cases k <;> simp <;> omega
      · by_cases h1 : e 1 = 1
        · right; left; ext k; fin_cases k <;> simp <;> omega
        · right; right; ext k; fin_cases k <;> simp <;> omega
    have hsum : pderiv i F = ∑ e ∈ ({Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 2 1} :
        Finset (Fin 3 →₀ ℕ)), MvPolynomial.monomial e ((pderiv i F).coeff e) := by
      conv_lhs => rw [(pderiv i F).as_sum]
      exact Finset.sum_subset hsub fun e _ he => by
        rw [MvPolynomial.notMem_support_iff.mp he, map_zero]
    rw [hsum]
    have h01 : Finsupp.single (0 : Fin 3) 1 ≠ Finsupp.single 1 1 := by
      intro h; have := congrArg (fun g : Fin 3 →₀ ℕ => g 0) h; simp at this
    have h02 : Finsupp.single (0 : Fin 3) 1 ≠ Finsupp.single 2 1 := by
      intro h; have := congrArg (fun g : Fin 3 →₀ ℕ => g 0) h; simp at this
    have h12 : Finsupp.single (1 : Fin 3) 1 ≠ Finsupp.single 2 1 := by
      intro h; have := congrArg (fun g : Fin 3 →₀ ℕ => g 1) h; simp at this
    rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
      Finset.sum_singleton, Fin.sum_univ_three]
    simp [A, MvPolynomial.X, MvPolynomial.C_mul_monomial, add_assoc]
  have hgp_eq_subst (P : MvPolynomial (Fin 3) L) : gaussPullback F P = substLin A P := by
    have hcomp : MvPolynomial.aeval ![pderiv 0 F, pderiv 1 F, pderiv 2 F] = substLin A := by
      apply MvPolynomial.algHom_ext; intro i
      rw [MvPolynomial.aeval_X, substLin_X]
      fin_cases i <;> simp [hpd_lin]
    exact AlgHom.congr_fun hcomp P
  -- By `linear_polar_not_dvd` over `AlgebraicClosure L`, the rows of `A` are linearly independent, so `A` is invertible!
  have hA_det : A.det ≠ 0 := by
    intro hdet0
    -- `Aᵀ.det = 0`, so there exists nonzero `a : Fin 3 → L` with `Aᵀ.mulVec a = 0`, i.e., `∑ i, a i * A i j = 0`.
    have hAT_det : Aᵀ.det = 0 := by rw [Matrix.det_transpose, hdet0]
    obtain ⟨a, ha_ne, ha_mul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hAT_det
    have hlin0 : ∑ i : Fin 3, MvPolynomial.C (a i) * pderiv i F = 0 := by
      simp_rw [hpd_lin, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro j _
      have hj : ∑ i : Fin 3, a i * A i j = 0 := by
        have := congrFun ha_mul j
        simpa [Matrix.mulVec, dotProduct, mul_comm] using this
      calc ∑ i : Fin 3, MvPolynomial.C (a i) * (MvPolynomial.C (A i j) * MvPolynomial.X j)
          = MvPolynomial.C (∑ i : Fin 3, a i * A i j) * MvPolynomial.X j := by
            rw [map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul]; ring
        _ = 0 := by rw [hj, map_zero, zero_mul]
    have hchar_bar : ∀ k : ℕ, 0 < k → k ≤ 2 → (k : AlgebraicClosure L) ≠ 0 := by
      intro k hk1 hk2 h0
      have hk_cases : k = 1 ∨ k = 2 := by omega
      rcases hk_cases with rfl | rfl
      · simp at h0
      · apply hchar2; apply ι.injective; simpa [map_ofNat] using h0
    let a_bar : Fin 3 → AlgebraicClosure L := fun i => ι (a i)
    have ha_bar_ne : a_bar ≠ 0 := by
      intro h0; apply ha_ne; ext i; exact ι.injective (by simpa [a_bar] using congrFun h0 i)
    have hlin_bar : ∑ i : Fin 3, MvPolynomial.C (a_bar i) * pderiv i (MvPolynomial.map ι F) = 0 := by
      have h := congrArg (MvPolynomial.map ι) hlin0
      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, MvPolynomial.map_C, map_pderiv]
    exact linear_polar_not_dvd hF_geom (map_isHomogeneous ι hF_hom) le_rfl hchar_bar a_bar ha_bar_ne
      (by rw [hlin_bar]; exact dvd_zero _)
  let B : Matrix (Fin 3) (Fin 3) L := A⁻¹
  have hAB : A * B = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA_det)
  have hBA : B * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA_det)
  -- The unique dual conic in `(H, R, V)` coordinates is `Q_dual := substLin (B * dualSwapMatrixInv L) F`!
  let M_dual : Matrix (Fin 3) (Fin 3) L := B * dualSwapMatrixInv L
  let N_dual : Matrix (Fin 3) (Fin 3) L := dualSwapMatrix L * A
  have hMN_dual : M_dual * N_dual = 1 := by
    dsimp only [M_dual, N_dual]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dualSwapMatrixInv L) (dualSwapMatrix L),
      dualSwapMatrixInv_mul, Matrix.one_mul, hBA]
  have hNM_dual : N_dual * M_dual = 1 := by
    dsimp only [M_dual, N_dual]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A B, hAB, Matrix.one_mul, dualSwapMatrix_mul_inv]
  let Q_dual : MvPolynomial (Fin 3) L := substLin M_dual F
  have hQ_dual_hom : Q_dual.IsHomogeneous 2 := substLin_isHomogeneous M_dual hF_hom
  have hQ_dual_bar_irr : Irreducible (MvPolynomial.map ι Q_dual) := by
    have hmap : MvPolynomial.map ι Q_dual = substLin (M_dual.map ι) (MvPolynomial.map ι F) :=
      map_substLin ι M_dual F
    have hMN_bar : M_dual.map ι * N_dual.map ι = 1 := by
      rw [← Matrix.map_mul, hMN_dual, Matrix.map_one ι (map_zero ι) (map_one ι)]
    have hNM_bar : N_dual.map ι * M_dual.map ι = 1 := by
      rw [← Matrix.map_mul, hNM_dual, Matrix.map_one ι (map_zero ι) (map_one ι)]
    rw [hmap]
    exact (MulEquiv.irreducible_iff
      (substLinEquiv (M_dual.map ι) (N_dual.map ι) hMN_bar hNM_bar).toMulEquiv).mpr hF_geom
  -- `X 0` cannot divide `Q_dual` (else it divides `map ι Q_dual`, contradicting irreducibility of degree 2).
  have hX0_ndvd : ¬ (MvPolynomial.X 0 : MvPolynomial (Fin 3) L) ∣ Q_dual := by
    intro ⟨W, hW⟩
    have hW_bar : MvPolynomial.map ι Q_dual = MvPolynomial.X 0 * MvPolynomial.map ι W := by
      rw [hW, map_mul, MvPolynomial.map_X]
    rcases hQ_dual_bar_irr.isUnit_or_isUnit hW_bar with hu | hWu
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
      have h := congrArg (fun p : MvPolynomial (Fin 3) (AlgebraicClosure L) =>
        p.coeff (Finsupp.single 0 1)) hc
      have hne : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 0 1 :=
        Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
      simp [MvPolynomial.coeff_X, MvPolynomial.coeff_C, hne] at h
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hWu
      have hdeg1 : (MvPolynomial.map ι Q_dual).IsHomogeneous 1 := by
        rw [hW_bar, hc]
        simpa using (MvPolynomial.isHomogeneous_X (AlgebraicClosure L) (0 : Fin 3)).mul
          (MvPolynomial.isHomogeneous_C (Fin 3) c)
      obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hQ_dual_bar_irr.ne_zero
      have h1 := (map_isHomogeneous ι hQ_dual_hom) (MvPolynomial.mem_support_iff.mp he)
      have h2 := hdeg1 (MvPolynomial.mem_support_iff.mp he)
      omega
  -- Therefore `Q_dual` has a monomial `e` with `e 0 = 0` and `e 1 + e 2 = 2`!
  have hex_mon : ∃ e ∈ Q_dual.support, e 0 = 0 := by
    by_contra hall
    push Not at hall
    apply hX0_ndvd
    refine ⟨∑ e ∈ Q_dual.support, MvPolynomial.monomial (e - Finsupp.single 0 1) (Q_dual.coeff e), ?_⟩
    rw [Finset.mul_sum]; conv_lhs => rw [Q_dual.as_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have he0 : 1 ≤ e 0 := Nat.pos_of_ne_zero (hall e he)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
    exact congrArg (fun d => MvPolynomial.monomial d (Q_dual.coeff e))
      (by ext i; fin_cases i <;> simp; omega)
  obtain ⟨e, he_supp, he0⟩ := hex_mon
  have he12 : e 1 + e 2 = 2 := by
    have h := hQ_dual_hom (MvPolynomial.mem_support_iff.mp he_supp)
    rw [weight_one_eq_sum, m3_sum, he0, zero_add] at h
    exact h
  have he_eq : e = Finsupp.single 1 (e 1) + Finsupp.single 2 (e 2) := by
    ext i; fin_cases i <;> simp [he0]
  refine ⟨(e 1, e 2), he12, ?_⟩
  intro Q hQ_hom hQ_ne hQ_zero S hfS H R V hH htan hR hQvan
  -- First note `f` is irreducible over `L`.
  have hf_irr : Irreducible f := irreducible_of_mapBiv_irreducible ι ι.injective hf_geom
  -- Show `¬ F ∣ gaussPullback F (substLin dualSwapMatrix Q)`.
  let P := substLin (dualSwapMatrix L) Q
  have hP_hom : P.IsHomogeneous 2 := substLin_isHomogeneous (dualSwapMatrix L) hQ_hom
  let G := gaussPullback F P
  have hG_hom : G.IsHomogeneous 2 := by simpa using gaussPullback_isHomogeneous hF_hom hP_hom
  have hndvd_F : ¬ F ∣ G := by
    intro ⟨W, hW⟩
    have hG_eq : G = substLin A (substLin (dualSwapMatrix L) Q) := hgp_eq_subst P
    have hBG_eq : substLin B G = substLin (dualSwapMatrix L) Q := by
      rw [hG_eq, ← AlgHom.comp_apply, substLin_comp, hAB, substLin_one, AlgHom.id_apply]
    have hQ_eq : Q = substLin (dualSwapMatrixInv L) (substLin B G) := by
      rw [hBG_eq, ← AlgHom.comp_apply, substLin_comp, dualSwapMatrix_mul_inv, substLin_one,
        AlgHom.id_apply]
    have hQ_dual_eq : substLin (dualSwapMatrixInv L) (substLin B F) = Q_dual := by
      dsimp only [Q_dual, M_dual]
      rw [← AlgHom.comp_apply, substLin_comp]
    have hQ_dvd : Q_dual ∣ Q := by
      rw [hQ_eq, hW, map_mul, map_mul, hQ_dual_eq]
      exact dvd_mul_right _ _
    obtain ⟨U, hU⟩ := hQ_dvd
    have hU_ne : U ≠ 0 := by rintro rfl; rw [mul_zero] at hU; exact hQ_ne hU
    obtain ⟨dU, hU_hom⟩ := isHomogeneous_of_dvd hQ_hom hQ_ne ⟨Q_dual, by rw [hU, mul_comm]⟩
    have hdU0 : dU = 0 := by
      have hprod := hQ_dual_hom.mul hU_hom; rw [← hU] at hprod
      obtain ⟨t, ht⟩ := MvPolynomial.support_nonempty.mpr hQ_ne
      have h1 := hQ_hom (MvPolynomial.mem_support_iff.mp ht)
      have h2 := hprod (MvPolynomial.mem_support_iff.mp ht)
      omega
    subst hdU0
    have hc : U = MvPolynomial.C (U.coeff 0) := isHomogeneous_zero_eq_C hU_hom
    have hc_ne : U.coeff 0 ≠ 0 := by intro h0; rw [h0, map_zero] at hc; exact hU_ne hc
    have hcoeff_e := congrArg (fun p : MvPolynomial (Fin 3) L => p.coeff e) hU
    rw [hc, mul_comm, MvPolynomial.coeff_C_mul, he_eq, hQ_zero, ← he_eq] at hcoeff_e
    exact mul_ne_zero hc_ne (MvPolynomial.mem_support_iff.mp he_supp) hcoeff_e.symm
  let g : L[X][X] := mv2EquivBiv (dehom G)
  have hf_ndvd_g : ¬ f ∣ g := by
    intro ⟨q, hq⟩
    have hdehom_dvd : dehom F ∣ dehom G := by
      refine ⟨mv2EquivBiv.symm q, ?_⟩
      rw [hF_dehom]
      apply mv2EquivBiv.injective
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact hq
    have hX2 : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) L) ∣ F := by
      have hF_eq : F = homog fMv.totalDegree fMv := by dsimp only [F]; rw [hm_eq]
      rw [hF_eq]
      exact X2_not_dvd_homog fMv (fun h0 => hf_irr.ne_zero (by
        have := congrArg mv2EquivBiv h0; simpa [fMv] using this))
    exact hndvd_F (dvd_of_dehom_dvd hF_hom hX2 hG_hom hdehom_dvd)
  have hf_tot : WeightedSylvesterDegree.TotalDegreeLe f 2 := by
    rw [show f = mv2EquivBiv fMv from (RingEquiv.apply_symm_apply mv2EquivBiv f).symm,
      totalDegreeLe_mv2EquivBiv_iff]
    exact le_of_eq hm_eq
  have hg_tot : WeightedSylvesterDegree.TotalDegreeLe g 2 := by
    rw [totalDegreeLe_mv2EquivBiv_iff]
    exact totalDegree_dehom_le hG_hom
  have hf_deg : f.natDegree ≤ 2 := by
    rw [show f = mv2EquivBiv fMv from (RingEquiv.apply_symm_apply mv2EquivBiv f).symm]
    refine natDegree_mv2EquivBiv_le fMv 2 fun t ht => ?_
    have h1 := (Finset.le_sup (f := fun u : Fin 2 →₀ ℕ => u.sum fun _ v => v) ht).trans (le_of_eq hm_eq)
    rw [m2_sum] at h1; omega
  have hg_deg : g.natDegree ≤ 2 := by
    refine natDegree_mv2EquivBiv_le (dehom G) 2 fun t ht => ?_
    have h1 := (Finset.le_sup (f := fun u : Fin 2 →₀ ℕ => u.sum fun _ v => v) ht).trans
      (totalDegree_dehom_le hG_hom)
    rw [m2_sum] at h1; omega
  have hgS : ∀ p ∈ S, (g.map (evalRingHom p.1)).eval p.2 = 0 := fun p hp =>
    eval_polar_eq_zero_of_tangent hm_eq hQ_hom (hfS p hp) (hH p hp) (htan p hp) (hR p hp) (hQvan p hp)
  have hbez := plane_bezout_irreducible_with_multiplicity f g
    hf_irr hf_ndvd_g hf_tot hg_tot hf_deg le_rfl hg_deg le_rfl S (fun p hp => ⟨hfS p hp, hgS p hp⟩)
  simpa using hbez

end MainTheorems

#print axioms irreducible_homog_of_irreducible_biv
#print axioms gaussPullback_not_dvd_of_gt
#print axioms polar_affine_card_le
#print axioms polar_affine_card_le_of_smooth
#print axioms conic_five_column_polar_cap

end ArkLib.ProximityGap.Frontier.PlanePolarCap
