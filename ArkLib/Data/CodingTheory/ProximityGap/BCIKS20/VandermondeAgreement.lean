/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.ZLinearClosureAudit
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Claim 5.9 by Vandermonde globalization — the heavy-branch curve collapse (#302 hlin, B2)

The geometric half of [BCIKS20] §5.2.7: if the genuine Hensel branch `γ = gammaGenuine` has
vanishing coefficient tail (`αGenuine t = 0` for `t ≥ n`, Claim 5.8′) and its `n` coefficient
sums `∑_s (xⱼ)^s·α_s` take **ground-line affine values** `lift (C (u₀ j) + Z·C (u₁ j))` at
`n` distinct points `x₀…x_{n−1} ∈ F` (the Claim 5.10 per-point output, supplied at the
Claim 5.11 heavy points), then **every** coefficient `αGenuine t` lies on the ground
`F[Z]`-line with `Z`-degree ≤ 1 — the faithful paper rendering `gammaGenuine_paperZ_linear`
of Claim 5.9.  Combined with the proven collapse
`natDegree_eq_one_of_gammaGenuine_paperZ_linear` (`ZLinearClosureAudit`), this yields **the
hlin kill**: a branch with such values at enough points has `d_H = H.natDegree = 1` — no
per-`z` decoded root can live on a `Y`-degree ≥ 2 factor.

Route (eval-free, field-instance-free linear algebra): the value family is the linear system
`W ⬝ α = g` over `𝕃 H` with the **`F`-rational Vandermonde** matrix `W j s = (x j)^s`;
distinct nodes make `det W ≠ 0` over `F`, and inverting **over `F`** expresses every `α_t`
as an `F`-combination of the ground-affine values `g j` — hence ground-affine itself.  Only
the (cheap) ring structure of `𝕃 H` is used; the noncomputable field instance never enters
the algebra.

## Main results

* `liftConst` — the constant-line embedding `F →+* 𝕃 H`.
* `alphaGenuine_tail_zero_of_trunc` — bridge from the Claim 5.8′ truncation identity to the
  coefficient-tail hypothesis.
* `gammaGenuine_paperZ_linear_of_vandermonde_values` — **the globalization**: coefficient
  tail + `n` distinct ground-affine coefficient-sum values ⟹ `gammaGenuine_paperZ_linear`.
* `natDegree_eq_one_of_vandermonde_values` — **the hlin kill**: same data ⟹
  `H.natDegree = 1`.
* `false_of_vandermonde_values_of_two_le` — the contradiction form at `d_H ≥ 2`.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654 — §5.2.7 (Claims 5.9–5.11).
* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110 — Claim 1.
-/

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator
open BCIKS20.ZLinearClosureAudit

set_option linter.unusedSectionVars false

namespace BCIKS20.Claim59Lagrange

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The constant-line embedding `F → 𝕃 H`, `a ↦ lift (C a)`. -/
noncomputable def liftConst : F →+* 𝕃 H :=
  (liftToFunctionField (H := H)).comp (Polynomial.C : F →+* F[X])

@[simp]
theorem liftConst_apply (a : F) :
    liftConst H a = liftToFunctionField (H := H) (Polynomial.C a) := rfl

/-- Bridge: the Claim 5.8′ truncation identity yields the coefficient-tail hypothesis. -/
theorem alphaGenuine_tail_zero_of_trunc
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H) {n : ℕ}
    (htrunc : gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc n (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H))) :
    ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0 := by
  intro t ht
  have h1 : PowerSeries.coeff t (gammaGenuine x₀ R H hHyp)
      = αGenuine H x₀ R hHyp t := rfl
  rw [← h1, htrunc, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_neg (not_lt.mpr ht)]

/-- **Claim 5.9 by Vandermonde globalization.**  If the genuine branch has vanishing
coefficient tail past `n` (Claim 5.8′) and its coefficient sums take ground-line affine
values at `n` distinct points of `F` (the Claim 5.10 per-point output at the Claim 5.11
heavy points), then the faithful paper rendering `gammaGenuine_paperZ_linear` holds: every
coefficient `αGenuine t` is on the ground `F[Z]`-line with `Z`-degree ≤ 1. -/
theorem gammaGenuine_paperZ_linear_of_vandermonde_values
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (x : Fin n → F) (hx : Function.Injective x) (u₀ u₁ : Fin n → F)
    (hvals : ∀ j : Fin n,
      ∑ s : Fin n, liftConst H ((x j) ^ (s : ℕ)) * αGenuine H x₀ R hHyp (s : ℕ)
        = liftToFunctionField (H := H)
            (Polynomial.C (u₀ j) + Polynomial.X * Polynomial.C (u₁ j))) :
    gammaGenuine_paperZ_linear H x₀ R hHyp := by
  classical
  set W : Matrix (Fin n) (Fin n) F := Matrix.vandermonde x with hW
  have hWdet : W.det ≠ 0 := by
    rw [hW, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    rw [Finset.mem_Ioi] at hj
    exact sub_ne_zero.mpr fun h => ne_of_gt hj (hx h)
  have hinv : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W (isUnit_iff_ne_zero.mpr hWdet)
  refine ⟨fun t => if h : t < n then ∑ j, W⁻¹ ⟨t, h⟩ j * u₀ j else 0,
          fun t => if h : t < n then ∑ j, W⁻¹ ⟨t, h⟩ j * u₁ j else 0,
          fun t => ?_⟩
  by_cases ht : t < n
  swap
  · simp only [dif_neg ht]
    rw [htail t (not_lt.mp ht)]
    simp
  simp only [dif_pos ht]
  set t' : Fin n := ⟨t, ht⟩ with ht'
  have htt' : t = (t' : ℕ) := rfl
  calc αGenuine H x₀ R hHyp t
      = ∑ s : Fin n, liftConst H ((1 : Matrix (Fin n) (Fin n) F) t' s)
          * αGenuine H x₀ R hHyp (s : ℕ) := by
        rw [Finset.sum_eq_single t']
        · rw [Matrix.one_apply_eq, map_one, one_mul, htt']
        · intro b _ hb
          rw [Matrix.one_apply_ne (Ne.symm hb), map_zero, zero_mul]
        · intro habs
          exact absurd (Finset.mem_univ t') habs
    _ = ∑ s : Fin n, ∑ j : Fin n,
          liftConst H (W⁻¹ t' j) * (liftConst H (W j s)
            * αGenuine H x₀ R hHyp (s : ℕ)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← hinv, Matrix.mul_apply, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, mul_assoc]
    _ = ∑ j : Fin n, liftConst H (W⁻¹ t' j)
          * (∑ s : Fin n, liftConst H (W j s) * αGenuine H x₀ R hHyp (s : ℕ)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ j : Fin n, liftConst H (W⁻¹ t' j)
          * liftToFunctionField (H := H)
              (Polynomial.C (u₀ j) + Polynomial.X * Polynomial.C (u₁ j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [← hvals j]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hW, Matrix.vandermonde_apply]
    _ = liftToFunctionField (H := H)
          (∑ j : Fin n, Polynomial.C (W⁻¹ t' j)
            * (Polynomial.C (u₀ j) + Polynomial.X * Polynomial.C (u₁ j))) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, liftConst_apply]
    _ = liftToFunctionField (H := H)
          (Polynomial.C (∑ j, W⁻¹ t' j * u₀ j)
            + Polynomial.X * Polynomial.C (∑ j, W⁻¹ t' j * u₁ j)) := by
        congr 1
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Polynomial.C_mul, Polynomial.C_mul]
        ring

/-- **The hlin kill (collapse form).**  Coefficient tail + `n` distinct ground-affine
coefficient-sum values force `H.natDegree = 1`: the heavy branch is `Y`-linear.  This is
[BCIKS20] Claim 5.9 read as the curve collapse
(`ZLinearClosureAudit.natDegree_eq_one_of_gammaGenuine_paperZ_linear`). -/
theorem natDegree_eq_one_of_vandermonde_values
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (x : Fin n → F) (hx : Function.Injective x) (u₀ u₁ : Fin n → F)
    (hvals : ∀ j : Fin n,
      ∑ s : Fin n, liftConst H ((x j) ^ (s : ℕ)) * αGenuine H x₀ R hHyp (s : ℕ)
        = liftToFunctionField (H := H)
            (Polynomial.C (u₀ j) + Polynomial.X * Polynomial.C (u₁ j))) :
    H.natDegree = 1 :=
  natDegree_eq_one_of_gammaGenuine_paperZ_linear H hHyp
    (gammaGenuine_paperZ_linear_of_vandermonde_values H hHyp htail x hx u₀ u₁ hvals)

/-- **The contradiction form at `d_H ≥ 2`.**  No branch of `Y`-degree ≥ 2 admits the heavy
data: coefficient tail + `n` distinct ground-affine coefficient-sum values are impossible.
Heavy branches are `Y`-linear, period — this is `hlin`. -/
theorem false_of_vandermonde_values_of_two_le
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hdeg : 2 ≤ H.natDegree)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (x : Fin n → F) (hx : Function.Injective x) (u₀ u₁ : Fin n → F)
    (hvals : ∀ j : Fin n,
      ∑ s : Fin n, liftConst H ((x j) ^ (s : ℕ)) * αGenuine H x₀ R hHyp (s : ℕ)
        = liftToFunctionField (H := H)
            (Polynomial.C (u₀ j) + Polynomial.X * Polynomial.C (u₁ j))) :
    False := by
  have h1 := natDegree_eq_one_of_vandermonde_values H hHyp htail x hx u₀ u₁ hvals
  omega

end BCIKS20.Claim59Lagrange

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim59Lagrange.alphaGenuine_tail_zero_of_trunc
#print axioms BCIKS20.Claim59Lagrange.gammaGenuine_paperZ_linear_of_vandermonde_values
#print axioms BCIKS20.Claim59Lagrange.natDegree_eq_one_of_vandermonde_values
#print axioms BCIKS20.Claim59Lagrange.false_of_vandermonde_values_of_two_le
