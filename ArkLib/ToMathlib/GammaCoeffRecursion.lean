/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CurveFamilyZLinear

/-!
# Issue #304 — coefficient extraction from the PROVEN root identity `Q(γ) = 0`

`GammaGenuine.lean` proves the genuine relation `Polynomial.eval (gammaGenuine …) (Q x₀ R H) = 0`
(`gammaGenuine_root`), with coefficient form `coeff_gammaGenuine_root`.  This file extracts from
that identity the **order-`t` linear equations** that pin each genuine Hensel coefficient
`αGenuine (t+1)` against the strictly lower-order window — the ANALYTIC-side relation from which
the (A.1) `βHensel` recursion was derived in [BCIKS20] App. A.4.

## The mechanism

For any root `γ` of a series-coefficient polynomial `Q : Polynomial R⟦X⟧` and any series `γ'`
agreeing with `γ` below order `t` with `coeff t γ' = 0`, the generalized Hensel linearization
`HenselSeriesCoeff.coeff_eval_sub_at` collapses the convolution difference to the `(0, t)` corner:

  `eval (constantCoeff γ) (derivative Q₀) · coeff t γ = − coeff t (eval γ' Q)`.

Specializing `γ := gammaGenuine` (so the linear response is exactly `ζ R x₀ H` by
`eval_α₀_derivative_Q₀`) and `γ' := gammaTruncGenuine … t` (the `≤ t` coefficient window of the
genuine root, an explicit `PowerSeries.mk` over `αGenuine 0, …, αGenuine t` — the mirror of
`βHenselTrunc` on the genuine side) yields the **named identity family**

  `ζ · αGenuine (t+1) = − coeff (t+1) (eval (gammaTruncGenuine … t) (Q x₀ R H))`,

a `ζ`-led linear relation pinning each coefficient by the lower orders through the explicit
polynomial data of `R` — no `choose` opacity left on the equation's right-hand side beyond the
finitely many lower-order coefficients themselves.

## Main results

* `derivQ₀_mul_coeff_root_eq` — the generic extraction engine (mathlib-only, any `CommRing`).
* `gammaTruncGenuine` — the explicit `≤ t` window of the genuine root (mirror of `βHenselTrunc`);
  `gammaTruncGenuine_eq_coe_trunc` identifies it with `PowerSeries.trunc (t+1)` of the root.
* `ζ_mul_αGenuine_succ_eq_neg_coeff_eval_trunc`, `αGenuine_succ_eq_neg_coeff_eval_trunc_div_ζ`,
  `genuine_trunc_defect_cancel` — the order-`(t+1)` recursion equations (the third is the exact
  genuine-side mirror of the `hcancel` hypothesis of
  `assembledSeries_isRoot_of_trunc_defect_cancel`).
* `coeff_eval_Q_expand`, `ζ_mul_αGenuine_succ_explicit` — the fully explicit convolution form:
  all `Q`-side data rendered as `evalX (C x₀) ∘ hasseDerivX` slices of `R` (the canonical
  Appendix-A Hasse data), via `coeff_Q_coeff_eq_evalX_hasseDerivX_coeff`.
* `ζ_mul_αGenuine_one_eq`, `αGenuine_one_eq` — **the explicit order-1 equation**:
  `αGenuine 1 = − (∂_X R)(x₀, α₀) / ζ` with `(∂_X R)(x₀, ·) = evalX (C x₀) (hasseDerivX 1 R)`,
  machine-checked (Newton's first step).  `eval₂_slice_zero_eq_zero` is the order-0 face.
* `trunc_defect_cancel_iff_coeff_eq_of_agree` — cross-lane bridge: under coefficient agreement
  up to `t`, the hypothesized `βHenselTrunc` defect-cancel at `t+1` is EXACTLY coefficient
  agreement at `t+1` (the analytic recursion admits no slack).
* `zLinear_succ_iff_explicit`, `zLinear_one_iff_explicit`,
  `gammaGenuine_eq_curve_sum_two_series_of_explicit_window_of_monic`,
  `gammaGenuine_eq_curve_sum_two_series_of_orderOne_explicit_of_monic` — the windowed Claim-5.9
  successor residual restated over the explicit recursion data, with the two-series consumers of
  `CurveFamilyZLinear` discharged from the explicit forms.

## Honesty

The order-`t` `Z`-linearity (`Z`-degree-`≤ 1` with `F[X]` coordinates) of `αGenuine t` is NOT
derivable from the recursion alone: the explicit order-1 value `−(∂_X R)(x₀, α₀)/ζ` is a priori a
polynomial of degree `< natDegree H` in `T` with `F(X)`-coordinates (both the `T`-power reduction
mod `H` and the division by `ζ` leave the `T`-degree-`≤ 1`/integrality claim to the geometric
§5.2.7 interpolation input).  This file therefore proves the *equivalence* of the residual with
the explicit-data statement and the consumers, never the residual itself.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  App. A.4 (Claim A.2), §5.2.7 (Claim 5.9).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator

namespace ArkLib.GammaCoeffRecursion

/-! ## Part 0 — the generic extraction engine (mathlib + `HenselSeriesCoeff` only) -/

section Generic

variable {A : Type*} [CommRing A]

/-- **The generic order-`t` extraction.**  For a root `γ` of `Q : Polynomial A⟦X⟧` and any
comparison series `γ'` that agrees with `γ` below order `t` and has `coeff t γ' = 0`, the
generalized Hensel linearization collapses to the `ζ`-led linear equation

  `eval (constantCoeff γ) (derivative Q₀) · coeff t γ = − coeff t (eval γ' Q)`.

This is `HenselSeriesCoeff.coeff_eval_sub_at` read at a root: the order-`t` coefficient of the
root is pinned (linearly, with the Newton response as the coefficient) by the evaluation of `Q`
at any zero-padded lower-order window. -/
theorem derivQ₀_mul_coeff_root_eq (Q : Polynomial (PowerSeries A)) {γ γ' : PowerSeries A}
    (hroot : Polynomial.eval γ Q = 0) {t : ℕ} (ht : 0 < t)
    (hagree : ∀ j < t, PowerSeries.coeff j γ = PowerSeries.coeff j γ')
    (htop : PowerSeries.coeff t γ' = 0) :
    Polynomial.eval (PowerSeries.constantCoeff γ)
        (Polynomial.derivative (ProximityPrize.HenselSeriesCoeff.Q₀ Q))
      * PowerSeries.coeff t γ
      = - PowerSeries.coeff t (Polynomial.eval γ' Q) := by
  have hlin := ProximityPrize.HenselSeriesCoeff.coeff_eval_sub_at Q ht hagree
  rw [hroot, map_zero, zero_sub, htop, sub_zero] at hlin
  exact hlin.symm

end Generic

/-! ## Part 1 — the genuine window and the order-`(t+1)` recursion equations -/

section Recursion

variable {F : Type} [Field F] {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The `≤ t` coefficient window of the genuine root** (the genuine-side mirror of
`βHenselTrunc`): the explicit power series whose coefficients are `αGenuine 0, …, αGenuine t`
and `0` above.  This is the "lower-order data" each recursion equation evaluates `Q` at. -/
noncomputable def gammaTruncGenuine (H : F[X][Y]) [Fact (Irreducible H)]
    [Fact (0 < H.natDegree)] (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries (𝕃 H) :=
  PowerSeries.mk (fun j => if j ≤ t then αGenuine H x₀ R hHyp j else 0)

/-- Window coefficients at orders `≤ t` are the genuine coefficients. -/
theorem coeff_gammaTruncGenuine_of_le {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    {t j : ℕ} (hj : j ≤ t) :
    PowerSeries.coeff j (gammaTruncGenuine H x₀ R hHyp t) = αGenuine H x₀ R hHyp j := by
  rw [gammaTruncGenuine, PowerSeries.coeff_mk, if_pos hj]

/-- Window coefficients above order `t` vanish. -/
theorem coeff_gammaTruncGenuine_of_gt {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    {t j : ℕ} (hj : t < j) :
    PowerSeries.coeff j (gammaTruncGenuine H x₀ R hHyp t) = 0 := by
  rw [gammaTruncGenuine, PowerSeries.coeff_mk, if_neg (by omega)]

/-- The window is literally the `(t+1)`-truncation of the genuine root, coerced back to a
series: no data beyond the polynomial truncation hides in the `mk`. -/
theorem gammaTruncGenuine_eq_coe_trunc {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (t : ℕ) :
    gammaTruncGenuine H x₀ R hHyp t
      = ((PowerSeries.trunc (t + 1) (gammaGenuine x₀ R H hHyp) : Polynomial (𝕃 H))
          : PowerSeries (𝕃 H)) := by
  ext j
  rw [gammaTruncGenuine, PowerSeries.coeff_mk, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hj : j ≤ t
  · rw [if_pos hj, if_pos (Nat.lt_succ_of_le hj)]
    rfl
  · rw [if_neg hj, if_neg (by omega)]

/-- **THE recursion equation (the named identity family).**  Extracted from the PROVEN root
identity `gammaGenuine_root` at order `t + 1`:

  `ζ · αGenuine (t+1) = − coeff (t+1) (eval (gammaTruncGenuine … t) (Q x₀ R H))`.

The `ζ`-led linear relation pinning each genuine coefficient against the strictly lower-order
window — the analytic side of the (A.1) recursion. -/
theorem ζ_mul_αGenuine_succ_eq_neg_coeff_eval_trunc {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    ClaimA2.ζ R x₀ H * αGenuine H x₀ R hHyp (t + 1)
      = - PowerSeries.coeff (t + 1)
            (Polynomial.eval (gammaTruncGenuine H x₀ R hHyp t) (Q x₀ R H)) := by
  have hagree : ∀ j < t + 1,
      PowerSeries.coeff j (gammaGenuine x₀ R H hHyp)
        = PowerSeries.coeff j (gammaTruncGenuine H x₀ R hHyp t) := by
    intro j hj
    rw [coeff_gammaTruncGenuine_of_le hHyp (Nat.lt_succ_iff.mp hj)]
    rfl
  have htop : PowerSeries.coeff (t + 1) (gammaTruncGenuine H x₀ R hHyp t) = 0 :=
    coeff_gammaTruncGenuine_of_gt hHyp (Nat.lt_succ_self t)
  have h := derivQ₀_mul_coeff_root_eq (Q x₀ R H) (gammaGenuine_root hHyp)
    (Nat.succ_pos t) hagree htop
  rw [gammaGenuine_constantCoeff hHyp, eval_α₀_derivative_Q₀] at h
  exact h

/-- The division form: `αGenuine (t+1) = − coeff (t+1) (eval window Q) / ζ` (using `ζ ≠ 0`,
the genuine separability datum). -/
theorem αGenuine_succ_eq_neg_coeff_eval_trunc_div_ζ {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    αGenuine H x₀ R hHyp (t + 1)
      = - PowerSeries.coeff (t + 1)
            (Polynomial.eval (gammaTruncGenuine H x₀ R hHyp t) (Q x₀ R H))
          / ClaimA2.ζ R x₀ H := by
  rw [eq_div_iff (ζ_ne_zero H x₀ R hHyp), mul_comm]
  exact ζ_mul_αGenuine_succ_eq_neg_coeff_eval_trunc hHyp t

/-- **The genuine root satisfies the trunc-defect-cancel equation** — the exact genuine-side
mirror of the `hcancel` hypothesis consumed by `assembledSeries_isRoot_of_trunc_defect_cancel`
(there stated for the candidate `βHenselTrunc`/`βHenselAssembled` pair; here PROVEN for the
genuine pair `gammaTruncGenuine`/`gammaGenuine`). -/
theorem genuine_trunc_defect_cancel {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (gammaTruncGenuine H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * αGenuine H x₀ R hHyp (t + 1) = 0 := by
  rw [ζ_mul_αGenuine_succ_eq_neg_coeff_eval_trunc hHyp t, add_neg_cancel]

end Recursion

/-! ## Part 2 — the fully explicit convolution form (the `Q`-data as Hasse slices of `R`) -/

section Explicit

variable {F : Type} [Field F] {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- `natDegree (Q x₀ R H) < natDegree R + 1`: the recentered `Y`-polynomial is covered by the
index range of `R` (mapping by the coefficient ring hom never raises the `Y`-degree). -/
theorem natDegree_Q_lt (x₀ : F) (R : F[X][X][Y]) :
    (Q x₀ R H).natDegree < R.natDegree + 1 := by
  show (R.map (coeffHom x₀ H)).natDegree < R.natDegree + 1
  exact Nat.lt_succ_of_le Polynomial.natDegree_map_le

/-- **The explicit convolution expansion.**  The order-`s` coefficient of `eval γ' Q` for ANY
series `γ'` is the double sum over the `Y`-index of `R` and the antidiagonal of `s`, with all
`Q`-side data rendered as the canonical Appendix-A Hasse slices
`evalX (C x₀) (hasseDerivX a R)` (via `coeff_Q_coeff_eq_evalX_hasseDerivX_coeff`). -/
theorem coeff_eval_Q_expand (x₀ : F) (R : F[X][X][Y]) (γ' : PowerSeries (𝕃 H)) (s : ℕ) :
    PowerSeries.coeff s (Polynomial.eval γ' (Q x₀ R H))
      = ∑ i ∈ Finset.range (R.natDegree + 1), ∑ ab ∈ Finset.antidiagonal s,
          liftToFunctionField (H := H)
              ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i)
            * PowerSeries.coeff ab.2 (γ' ^ i) := by
  rw [Polynomial.eval_eq_sum_range' (natDegree_Q_lt x₀ R) γ', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [coeff_Q_coeff_eq_evalX_hasseDerivX_coeff H x₀ R i ab.1]

/-- **The recursion equation, fully explicit.**  The right-hand side carries only (i) the lifted
Hasse–Taylor slices of `R` at `x₀` (explicit polynomial data) and (ii) powers of the explicit
lower-order window — the window residual is now a statement about explicit polynomial data, not
about the opaque Hensel `choose`. -/
theorem ζ_mul_αGenuine_succ_explicit {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    ClaimA2.ζ R x₀ H * αGenuine H x₀ R hHyp (t + 1)
      = - ∑ i ∈ Finset.range (R.natDegree + 1), ∑ ab ∈ Finset.antidiagonal (t + 1),
          liftToFunctionField (H := H)
              ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i)
            * PowerSeries.coeff ab.2 ((gammaTruncGenuine H x₀ R hHyp t) ^ i) := by
  rw [ζ_mul_αGenuine_succ_eq_neg_coeff_eval_trunc hHyp t, coeff_eval_Q_expand]

end Explicit

/-! ## Part 3 — the explicit order-1 equation (Newton's first step, machine-checked) -/

section OrderOne

variable {F : Type} [Field F] {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The `Y`-degree of every Hasse slice `evalX (C x₀) (hasseDerivX s R)` is covered by the
index range of `R`. -/
theorem natDegree_evalX_hasseDerivX_lt (x₀ : F) (R : F[X][X][Y]) (s : ℕ) :
    (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX s R)).natDegree < R.natDegree + 1 := by
  rw [Nat.lt_succ_iff, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [evalX_C_coeff, hasseDerivX_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hm,
    map_zero, Polynomial.eval_zero]

/-- Evaluating `Q` at a constant series and reading order `s` is `eval₂` of the `s`-th Hasse
slice of `R` at the constant: the slice-evaluation form of the coefficient expansion. -/
theorem coeff_eval_C_eq_eval₂_slice (x₀ : F) (R : F[X][X][Y]) (a : 𝕃 H) (s : ℕ) :
    PowerSeries.coeff s (Polynomial.eval (PowerSeries.C a) (Q x₀ R H))
      = Polynomial.eval₂ (liftToFunctionField (H := H)) a
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX s R)) := by
  rw [Polynomial.eval_eq_sum_range' (natDegree_Q_lt x₀ R) (PowerSeries.C a), map_sum,
    Polynomial.eval₂_eq_sum_range' (liftToFunctionField (H := H))
      (natDegree_evalX_hasseDerivX_lt x₀ R s) a]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow, PowerSeries.coeff_mul_C, coeff_Q_coeff_eq_evalX_hasseDerivX_coeff H x₀ R i s]

/-- The order-0 window is the constant series at the base root `α₀ = T/W`. -/
theorem gammaTruncGenuine_zero_eq {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    gammaTruncGenuine H x₀ R hHyp 0 = PowerSeries.C (α₀ H) := by
  ext j
  rw [gammaTruncGenuine, PowerSeries.coeff_mk, PowerSeries.coeff_C]
  by_cases hj : j = 0
  · subst hj
    rw [if_pos (le_refl 0), if_pos rfl, αGenuine_zero]
  · rw [if_neg (by omega), if_neg hj]

/-- **The explicit order-1 equation (product form).**
`ζ · αGenuine 1 = − (∂_X R)(x₀, α₀)`, with the `X`-layer Hasse derivative slice
`(∂_X R)(x₀, ·) = evalX (C x₀) (hasseDerivX 1 R)` evaluated at the base root via `eval₂`. -/
theorem ζ_mul_αGenuine_one_eq {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    ClaimA2.ζ R x₀ H * αGenuine H x₀ R hHyp 1
      = - Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)) := by
  have h := ζ_mul_αGenuine_succ_eq_neg_coeff_eval_trunc hHyp 0
  rw [gammaTruncGenuine_zero_eq hHyp, coeff_eval_C_eq_eval₂_slice] at h
  exact h

/-- **The explicit order-1 value (division form): `αGenuine 1 = − (∂_X R)(x₀, α₀) / ζ`** —
Newton's first step for the genuine Hensel lift, machine-checked. -/
theorem αGenuine_one_eq {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    αGenuine H x₀ R hHyp 1
      = - Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R))
        / ClaimA2.ζ R x₀ H := by
  rw [eq_div_iff (ζ_ne_zero H x₀ R hHyp), mul_comm]
  exact ζ_mul_αGenuine_one_eq hHyp

/-- **The order-0 face of the same family** (consistency): the `0`-th Hasse slice evaluated at
`α₀` vanishes — this is exactly `H ∣ evalX (C x₀) R` plus `H(α₀) = 0`, i.e. the base-root
equation `eval α₀ Q₀ = 0` in slice form. -/
theorem eval₂_slice_zero_eq_zero {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 0 R)) = 0 := by
  rw [hasseDerivX_zero]
  obtain ⟨g, hg⟩ := hHyp.dvd_evalX
  rw [hg, Polynomial.eval₂_mul, eval₂_H_α₀, zero_mul]

end OrderOne

/-! ## Part 4 — cross-lane bridge: the candidate's defect-cancel hypothesis has no slack -/

section CrossLane

variable {F : Type} [Field F] {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- If the assembled candidate series agrees with the genuine coefficients up to order `t`,
its `≤ t` truncation IS the genuine window. -/
theorem βHenselTrunc_eq_gammaTruncGenuine_of_agree {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (t : ℕ)
    (hagree : ∀ j ≤ t, PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp)
      = αGenuine H x₀ R hHyp j) :
    βHenselTrunc H x₀ R hHyp t = gammaTruncGenuine H x₀ R hHyp t := by
  ext j
  rw [βHenselTrunc, gammaTruncGenuine, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hj : j ≤ t
  · rw [if_pos hj, if_pos hj, hagree j hj]
  · rw [if_neg hj, if_neg hj]

/-- **The defect-cancel hypothesis has no slack.**  Under coefficient agreement up to `t`, the
`hcancel` equation at `t + 1` (the hypothesis shape of
`assembledSeries_isRoot_of_trunc_defect_cancel`) is EXACTLY coefficient agreement at `t + 1`:
the analytic recursion pins the candidate's next coefficient to the genuine one. -/
theorem trunc_defect_cancel_iff_coeff_eq_of_agree {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (t : ℕ)
    (hagree : ∀ j ≤ t, PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp)
      = αGenuine H x₀ R hHyp j) :
    (PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp) = 0)
      ↔ PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
          = αGenuine H x₀ R hHyp (t + 1) := by
  rw [βHenselTrunc_eq_gammaTruncGenuine_of_agree hHyp t hagree]
  have hgen : PowerSeries.coeff (t + 1)
      (Polynomial.eval (gammaTruncGenuine H x₀ R hHyp t) (Q x₀ R H))
      = -(ClaimA2.ζ R x₀ H * αGenuine H x₀ R hHyp (t + 1)) := by
    rw [ζ_mul_αGenuine_succ_eq_neg_coeff_eval_trunc hHyp t, neg_neg]
  rw [hgen]
  constructor
  · intro h
    have h3 : ClaimA2.ζ R x₀ H
        * (PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
            - αGenuine H x₀ R hHyp (t + 1)) = 0 := by
      rw [mul_sub, ← h]
      ring
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (ζ_ne_zero H x₀ R hHyp)
    · exact sub_eq_zero.mp h4
  · intro h
    rw [h]
    ring

end CrossLane

/-! ## Part 5 — the windowed Claim-5.9 successor residual over explicit data, with consumers -/

section WindowConsumers

variable {F : Type} [Field F] {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The successor `Z`-linearity residual ↔ its explicit-data form.**  The order-`(t+1)`
`Z`-degree-`≤ 1` statement on the opaque `αGenuine (t+1)` is equivalent to the same statement on
the explicit recursion value `− coeff (t+1) (eval window Q) / ζ`. -/
theorem zLinear_succ_iff_explicit {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    (∃ c₀ c₁ : F[X], αGenuine H x₀ R hHyp (t + 1)
        = liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
      ↔ ∃ c₀ c₁ : F[X],
          - PowerSeries.coeff (t + 1)
              (Polynomial.eval (gammaTruncGenuine H x₀ R hHyp t) (Q x₀ R H))
            / ClaimA2.ζ R x₀ H
          = liftToFunctionField (H := H) c₀
            + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ := by
  constructor
  · rintro ⟨c₀, c₁, h⟩
    exact ⟨c₀, c₁, by rw [← αGenuine_succ_eq_neg_coeff_eval_trunc_div_ζ hHyp t]; exact h⟩
  · rintro ⟨c₀, c₁, h⟩
    exact ⟨c₀, c₁, by rw [αGenuine_succ_eq_neg_coeff_eval_trunc_div_ζ hHyp t]; exact h⟩

/-- **The order-1 `Z`-linearity residual ↔ the explicit Newton-step form**: the residual at
`t = 1` is exactly a statement about `− (∂_X R)(x₀, α₀) / ζ`. -/
theorem zLinear_one_iff_explicit {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    (∃ c₀ c₁ : F[X], αGenuine H x₀ R hHyp 1
        = liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
      ↔ ∃ c₀ c₁ : F[X],
          - Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R))
            / ClaimA2.ζ R x₀ H
          = liftToFunctionField (H := H) c₀
            + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ := by
  constructor
  · rintro ⟨c₀, c₁, h⟩
    exact ⟨c₀, c₁, by rw [← αGenuine_one_eq hHyp]; exact h⟩
  · rintro ⟨c₀, c₁, h⟩
    exact ⟨c₀, c₁, by rw [αGenuine_one_eq hHyp]; exact h⟩

/-- **PROVEN consumer: the two-series Claim-5.9 form from the EXPLICIT window residual** (monic
`H`).  The windowed successor residual of `CurveFamilyZLinear` discharged from its explicit-data
form: the `Z`-degree-`≤ 1` shape of the recursion values `− coeff (t+1) (eval window Q) / ζ` at
the finitely many indices `1 ≤ t + 1 < n`, plus tail vanishing. -/
theorem gammaGenuine_eq_curve_sum_two_series_of_explicit_window_of_monic
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic) {n : ℕ}
    (hsucc : ∀ t : ℕ, t + 1 < n → ∃ c₀ c₁ : F[X],
      - PowerSeries.coeff (t + 1)
          (Polynomial.eval (gammaTruncGenuine H x₀ R hHyp t) (Q x₀ R H))
        / ClaimA2.ζ R x₀ H
      = liftToFunctionField (H := H) c₀
        + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    ∃ c₀ c₁ : ℕ → F[X],
      gammaGenuine x₀ R H hHyp
        = (∑ t ∈ Finset.range n,
              PowerSeries.C (liftToFunctionField (H := H) (c₀ t)) * PowerSeries.X ^ t)
          + PowerSeries.C (functionFieldT (H := H))
            * ∑ t ∈ Finset.range n,
                PowerSeries.C (liftToFunctionField (H := H) (c₁ t)) * PowerSeries.X ^ t :=
  FaithfulCurveExtraction.gammaGenuine_eq_curve_sum_two_series_of_succ_window_of_monic
    hHyp hmonic
    (fun t ht => (zLinear_succ_iff_explicit hHyp t).mpr (hsucc t ht)) htail

/-- **PROVEN consumer at `n = 2`: the two-series form from the explicit ORDER-1 equation alone**
(monic `H`).  The full window collapses to the single explicit Newton-step condition on
`− (∂_X R)(x₀, α₀) / ζ`, plus tail vanishing from order 2 on. -/
theorem gammaGenuine_eq_curve_sum_two_series_of_orderOne_explicit_of_monic
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic)
    (h1 : ∃ c₀ c₁ : F[X],
      - Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R))
        / ClaimA2.ζ R x₀ H
      = liftToFunctionField (H := H) c₀
        + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
    (htail : ∀ t, 2 ≤ t → αGenuine H x₀ R hHyp t = 0) :
    ∃ c₀ c₁ : ℕ → F[X],
      gammaGenuine x₀ R H hHyp
        = (∑ t ∈ Finset.range 2,
              PowerSeries.C (liftToFunctionField (H := H) (c₀ t)) * PowerSeries.X ^ t)
          + PowerSeries.C (functionFieldT (H := H))
            * ∑ t ∈ Finset.range 2,
                PowerSeries.C (liftToFunctionField (H := H) (c₁ t)) * PowerSeries.X ^ t := by
  refine FaithfulCurveExtraction.gammaGenuine_eq_curve_sum_two_series_of_succ_window_of_monic
    hHyp hmonic (n := 2) (fun t ht => ?_) htail
  have ht0 : t = 0 := by omega
  subst ht0
  exact (zLinear_one_iff_explicit hHyp).mpr h1

end WindowConsumers

end ArkLib.GammaCoeffRecursion

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, no `native_decide`. -/
#print axioms ArkLib.GammaCoeffRecursion.derivQ₀_mul_coeff_root_eq
#print axioms ArkLib.GammaCoeffRecursion.gammaTruncGenuine
#print axioms ArkLib.GammaCoeffRecursion.coeff_gammaTruncGenuine_of_le
#print axioms ArkLib.GammaCoeffRecursion.coeff_gammaTruncGenuine_of_gt
#print axioms ArkLib.GammaCoeffRecursion.gammaTruncGenuine_eq_coe_trunc
#print axioms ArkLib.GammaCoeffRecursion.ζ_mul_αGenuine_succ_eq_neg_coeff_eval_trunc
#print axioms ArkLib.GammaCoeffRecursion.αGenuine_succ_eq_neg_coeff_eval_trunc_div_ζ
#print axioms ArkLib.GammaCoeffRecursion.genuine_trunc_defect_cancel
#print axioms ArkLib.GammaCoeffRecursion.natDegree_Q_lt
#print axioms ArkLib.GammaCoeffRecursion.coeff_eval_Q_expand
#print axioms ArkLib.GammaCoeffRecursion.ζ_mul_αGenuine_succ_explicit
#print axioms ArkLib.GammaCoeffRecursion.natDegree_evalX_hasseDerivX_lt
#print axioms ArkLib.GammaCoeffRecursion.coeff_eval_C_eq_eval₂_slice
#print axioms ArkLib.GammaCoeffRecursion.gammaTruncGenuine_zero_eq
#print axioms ArkLib.GammaCoeffRecursion.ζ_mul_αGenuine_one_eq
#print axioms ArkLib.GammaCoeffRecursion.αGenuine_one_eq
#print axioms ArkLib.GammaCoeffRecursion.eval₂_slice_zero_eq_zero
#print axioms ArkLib.GammaCoeffRecursion.βHenselTrunc_eq_gammaTruncGenuine_of_agree
#print axioms ArkLib.GammaCoeffRecursion.trunc_defect_cancel_iff_coeff_eq_of_agree
#print axioms ArkLib.GammaCoeffRecursion.zLinear_succ_iff_explicit
#print axioms ArkLib.GammaCoeffRecursion.zLinear_one_iff_explicit
#print axioms ArkLib.GammaCoeffRecursion.gammaGenuine_eq_curve_sum_two_series_of_explicit_window_of_monic
#print axioms ArkLib.GammaCoeffRecursion.gammaGenuine_eq_curve_sum_two_series_of_orderOne_explicit_of_monic
