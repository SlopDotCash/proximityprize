/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CurveFamilyGenuine
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5GenuineZLinearMonic

/-!
# Issue #304 — the `Z`-linear (T-linear) curve form and its place-reading consumer

`CurveFamilyGenuine.gammaGenuine_eq_curve_sum` produces the single-series curve form
`γ = ∑_{t<n} C (lift c_t) · X^t` from **pure** base-rationality (`αGenuine t = lift c_t`).  That
hypothesis FAILS at `t = 0` for the genuine chain (`αGenuine 0 = α₀ = T/W` carries `T`-content),
so the faithful §5 route goes through Claim 5.9's *Z-linear* coefficient shape instead
(`S5Genuine.gammaGenuine_Z_linear_target`): every coefficient is
`αGenuine t = lift c₀ᵗ + T · lift c₁ᵗ` — `T`-degree `≤ 1` with base-rational coordinates.

This file supplies the missing bridge bricks on both edges of that core:

* **The T-linear curve form** (`gammaGenuine_eq_mk_curve_zLinear` /
  `gammaGenuine_eq_curve_sum_zLinear`): the per-coefficient `Z`-linear shape below `n` plus tail
  vanishing forces `γ = V₀ + C(T)·V₁` with `V_i = ∑_{t<n} C (lift c_iᵗ) · X^t` — the explicit
  truncated **two-series** rendering of [BCIKS20] Prop. 5.5 under Claim 5.9 (the analogue of
  `gammaGenuine_eq_curve_sum`, with the `t = 0` obstruction dissolved into the `T`-linear slot).
* **The target is exactly the per-coefficient form**
  (`coeffs_Z_linear_of_target` / `gammaGenuine_Z_linear_target_iff_coeffs_Z_linear`): the converse
  of `gammaGenuine_Z_linear_of_coeffs_Z_linear`, so the Claim 5.9 target and the per-coefficient
  `Z`-degree-`≤1` fact are interderivable — the residual surface cannot hide extra content.
* **Composition with the monic reductions**
  (`gammaGenuine_eq_curve_sum_two_series_of_target`,
  `gammaGenuine_eq_curve_sum_two_series_of_succ_of_monic`,
  `gammaGenuine_eq_curve_sum_two_series_of_succ_window_of_monic`): for monic `H` the two-series
  form needs only the **windowed successor residual** — the `Z`-degree-`≤1` fact at the finitely
  many indices `1 ≤ t < n` (order `0` is `claim59_zLinear_zero_of_monic`; `t ≥ n` is the
  truncation tail).  This pins the exact remaining content of Claim 5.9 on this lane: a finite
  window of the geometric §5.2.7 interpolation input.
* **The place-reading consumer** (`CurvePlaceReading`, `curveFamilyData_of_placeReading`,
  `hcoeffPoly_witness_of_placeReading`): the faithful per-`z` reading of the two-series form is
  `P z = (∑_{t<n} (z−x₀)^t • c₀ᵗ) + r z • (∑_{t<n} (z−x₀)^t • c₁ᵗ)` with `r z` the branch value
  of `T` at the place `z`.  We isolate that reading as the named honest residual
  (`CurvePlaceReading` — its production is the per-place evaluation of the `𝕃 H` identity, which
  has no in-tree evaluation map yet) and PROVE its consumer: whenever the branch is itself a
  centred polynomial of `m` coefficients (`r z = ∑_{s<m} b_s (z−x₀)^s` on the good set, the
  branch-rationality the §5 geometry supplies), the readings convolve into a genuine
  `CurveFamilyData` with `n + m` curve coefficients (`curve_reading_convolution`, pure algebra),
  hence into the keystone front doors of `FaithfulCurveExtraction`.

## Honest residuals after this file (this lane)

1. the **windowed successor residual** of Claim 5.9 (monic): the `Z`-degree-`≤1` shape of
   `αGenuine t` for `1 ≤ t < n` — the geometric §5.2.7 interpolation input (external degree
   budget of the GS interpolant; not derivable from the (A.1) recursion alone).
2. the **per-place reading** (`CurvePlaceReading`): evaluating the two-series identity at a place
   `z` (series var ↦ `z − x₀`, `T` ↦ branch value, ground layer ↦ codeword polynomials) — there
   is no in-tree evaluation homomorphism `𝕃 H → F[X]`-readings; the per-`z` machinery
   (`IngredientC.MatchingVanishes`, `π_z`, Claims 5.10/5.11) operates on `𝒪 H` and produces
   vanishing, not readings.
3. the **branch rationality** (`hbranch`): the branch values form a centred polynomial of
   bounded degree on the good set (the §5 "the root section is rational" content; for affine
   families it is the linear `Z ↦ z` substitution).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5.2.7 (Claim 5.9, fulltext 1707–1740), Prop. 5.5, §6.2.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open BCIKS20.HenselNumerator.S5Genuine
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace FaithfulCurveExtraction

/-! ## Part 0 — coefficient extraction for truncated series (helper) -/

section Helper

/-- Coefficient of a truncated series `∑_{t<n} C (g t) · X^t`: `if s < n then g s else 0`. -/
theorem coeff_range_sum_C_mul_X_pow {S : Type} [Semiring S] (n : ℕ) (g : ℕ → S) (s : ℕ) :
    PowerSeries.coeff s (∑ t ∈ Finset.range n, PowerSeries.C (g t) * PowerSeries.X ^ t)
      = if s < n then g s else 0 := by
  rw [map_sum]
  by_cases hs : s < n
  · rw [if_pos hs, Finset.sum_eq_single s
      (fun t _ hts => by
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (fun h => hts h.symm),
          mul_zero])
      (fun hs' => absurd (Finset.mem_range.mpr hs) hs'),
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun t ht => ?_
    have hts : s ≠ t := fun h => hs (h ▸ Finset.mem_range.mp ht)
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg hts, mul_zero]

end Helper

/-! ## Part 1 — the T-linear (Claim 5.9 shape) curve-series form -/

section CurveSeriesZLinear

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The T-linear curve-series form (mk shape).**  If the genuine Hensel coefficients are in
the Claim 5.9 `Z`-linear shape below `n` (`hbase : αGenuine t = lift c₀ᵗ + T · lift c₁ᵗ` — the
coefficient form of `gammaGenuine_Z_linear_target`) and vanish from `n` on (`htail`, the
truncation content), then `γ = V₀ + C(T)·V₁` with `V_i` the truncated base-rational series.
The analogue of `gammaGenuine_eq_mk_curve` with the `t = 0` obstruction (`α₀ = T/W` has
`T`-content) absorbed into the `T`-linear slot. -/
theorem gammaGenuine_eq_mk_curve_zLinear {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    {n : ℕ} {c₀ c₁ : ℕ → F[X]}
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) (c₀ t)
        + functionFieldT (H := H) * liftToFunctionField (H := H) (c₁ t))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    gammaGenuine x₀ R H hHyp
      = PowerSeries.mk (fun t => if t < n then liftToFunctionField (H := H) (c₀ t) else 0)
        + PowerSeries.C (functionFieldT (H := H))
          * PowerSeries.mk (fun t => if t < n then liftToFunctionField (H := H) (c₁ t) else 0) := by
  ext s
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hs : s < n
  · rw [if_pos hs, if_pos hs]
    exact hbase s hs
  · rw [if_neg hs, if_neg hs, mul_zero, add_zero]
    exact htail s (le_of_not_gt hs)

/-- **The T-linear curve-series form (finite-sum shape).**  Same hypotheses, with the conclusion
as the explicit truncated two-series decomposition
`γ = (∑_{t<n} C (lift c₀ᵗ) · X^t) + C(T) · (∑_{t<n} C (lift c₁ᵗ) · X^t)` — the series-level
rendering of [BCIKS20] Prop. 5.5 under Claim 5.9. -/
theorem gammaGenuine_eq_curve_sum_zLinear {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    {n : ℕ} {c₀ c₁ : ℕ → F[X]}
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) (c₀ t)
        + functionFieldT (H := H) * liftToFunctionField (H := H) (c₁ t))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    gammaGenuine x₀ R H hHyp
      = (∑ t ∈ Finset.range n,
            PowerSeries.C (liftToFunctionField (H := H) (c₀ t)) * PowerSeries.X ^ t)
        + PowerSeries.C (functionFieldT (H := H))
          * ∑ t ∈ Finset.range n,
              PowerSeries.C (liftToFunctionField (H := H) (c₁ t)) * PowerSeries.X ^ t := by
  ext s
  rw [map_add, PowerSeries.coeff_C_mul, coeff_range_sum_C_mul_X_pow,
    coeff_range_sum_C_mul_X_pow]
  by_cases hs : s < n
  · rw [if_pos hs, if_pos hs]
    exact hbase s hs
  · rw [if_neg hs, if_neg hs, mul_zero, add_zero]
    exact htail s (le_of_not_gt hs)

/-- **The Claim 5.9 target yields the per-coefficient `Z`-linear form** — the converse of
`gammaGenuine_Z_linear_of_coeffs_Z_linear`: from `γ = v₀ + C(T)·v₁` with base-rational
coefficient series, every `αGenuine t` is `lift c₀ + T · lift c₁`. -/
theorem coeffs_Z_linear_of_target {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (htarget : gammaGenuine_Z_linear_target H x₀ R hHyp) :
    ∀ t, ∃ c₀ c₁ : F[X],
      αGenuine H x₀ R hHyp t
        = liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ := by
  obtain ⟨v₀, v₁, hγ, hcoeffs⟩ := htarget
  intro t
  obtain ⟨c₀, c₁, h₀, h₁⟩ := hcoeffs t
  refine ⟨c₀, c₁, ?_⟩
  have hcoeff : αGenuine H x₀ R hHyp t
      = PowerSeries.coeff t (gammaGenuine x₀ R H hHyp) := rfl
  rw [hcoeff, hγ, map_add, PowerSeries.coeff_C_mul, h₀, h₁]

/-- **Claim 5.9's target ↔ the per-coefficient `Z`-linear form (both directions PROVEN).**
The residual surface of Claim 5.9 is *exactly* the per-coefficient `Z`-degree-`≤1` fact —
no content hides in the series-level packaging. -/
theorem gammaGenuine_Z_linear_target_iff_coeffs_Z_linear {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    gammaGenuine_Z_linear_target H x₀ R hHyp
      ↔ ∀ t, ∃ c₀ c₁ : F[X],
          αGenuine H x₀ R hHyp t
            = liftToFunctionField (H := H) c₀
              + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ :=
  ⟨coeffs_Z_linear_of_target hHyp, gammaGenuine_Z_linear_of_coeffs_Z_linear H hHyp⟩

/-- **The explicit truncated two-series form from the Claim 5.9 target + truncation.**
`gammaGenuine_Z_linear_target` plus tail vanishing below `n` (Claim 5.8′'s content) yield
witnesses `c₀, c₁ : ℕ → F[X]` with `γ = V₀ + C(T)·V₁`, both `V_i` truncated at `n`. -/
theorem gammaGenuine_eq_curve_sum_two_series_of_target {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) {n : ℕ}
    (htarget : gammaGenuine_Z_linear_target H x₀ R hHyp)
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    ∃ c₀ c₁ : ℕ → F[X],
      gammaGenuine x₀ R H hHyp
        = (∑ t ∈ Finset.range n,
              PowerSeries.C (liftToFunctionField (H := H) (c₀ t)) * PowerSeries.X ^ t)
          + PowerSeries.C (functionFieldT (H := H))
            * ∑ t ∈ Finset.range n,
                PowerSeries.C (liftToFunctionField (H := H) (c₁ t)) * PowerSeries.X ^ t := by
  classical
  choose c₀ c₁ hc using coeffs_Z_linear_of_target hHyp htarget
  exact ⟨c₀, c₁, gammaGenuine_eq_curve_sum_zLinear hHyp (fun t _ => hc t) htail⟩

/-- **The two-series form for monic `H`, from the WINDOWED successor residual.**  For monic `H`
the order-0 face is `claim59_zLinear_zero_of_monic` and the tail (`t ≥ n`) is the truncation
hypothesis, so the only remaining Claim 5.9 input is the `Z`-degree-`≤1` shape at the finitely
many indices `1 ≤ t < n` — the windowed successor residual.  This is the sharpest honest form of
the Claim 5.9 reduction on this lane: a *finite window* of the geometric §5.2.7 input. -/
theorem gammaGenuine_eq_curve_sum_two_series_of_succ_window_of_monic
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic) {n : ℕ}
    (hsucc : ∀ t : ℕ, t + 1 < n → ∃ c₀ c₁ : F[X],
      αGenuine H x₀ R hHyp (t + 1)
        = liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    ∃ c₀ c₁ : ℕ → F[X],
      gammaGenuine x₀ R H hHyp
        = (∑ t ∈ Finset.range n,
              PowerSeries.C (liftToFunctionField (H := H) (c₀ t)) * PowerSeries.X ^ t)
          + PowerSeries.C (functionFieldT (H := H))
            * ∑ t ∈ Finset.range n,
                PowerSeries.C (liftToFunctionField (H := H) (c₁ t)) * PowerSeries.X ^ t := by
  classical
  have hbase : ∀ t, ∃ c₀ c₁ : F[X], t < n →
      αGenuine H x₀ R hHyp t
        = liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ := by
    intro t
    by_cases ht : t < n
    · cases t with
      | zero =>
          obtain ⟨c₀, c₁, h⟩ := claim59_zLinear_zero_of_monic H hHyp hmonic
          exact ⟨c₀, c₁, fun _ => h⟩
      | succ s =>
          obtain ⟨c₀, c₁, h⟩ := hsucc s ht
          exact ⟨c₀, c₁, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h ht⟩
  choose c₀ c₁ hc using hbase
  exact ⟨c₀, c₁, gammaGenuine_eq_curve_sum_zLinear hHyp (fun t ht => hc t ht) htail⟩

/-- **The two-series form for monic `H`, from the full successor residual** — the hypothesis
shape of `gammaGenuine_Z_linear_target_of_succ_of_monic`, composed down to the explicit
truncated two-series form. -/
theorem gammaGenuine_eq_curve_sum_two_series_of_succ_of_monic
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic) {n : ℕ}
    (hsucc : ∀ t : ℕ, ∃ c₀ c₁ : F[X],
      αGenuine H x₀ R hHyp (t + 1)
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
  gammaGenuine_eq_curve_sum_two_series_of_succ_window_of_monic hHyp hmonic
    (fun t _ => hsucc t) htail

end CurveSeriesZLinear

/-! ## Part 2 — the per-`z` place reading and its proven curve-family consumer -/

section PlaceReading

variable {F : Type} [Field F]

/-- **The reading convolution (pure algebra).**  A two-series reading with a centred polynomial
branch is itself a polynomial curve: for every `z`,
`(∑_{t<n} (z−x₀)^t • c₀ᵗ) + (∑_{s<m} b_s (z−x₀)^s) • (∑_{t<n} (z−x₀)^t • c₁ᵗ)`
equals `∑_{j<n+m} (z−x₀)^j • e_j` with the explicit convolved coefficients
`e_j = (if j < n then c₀ⱼ else 0) + ∑_{s+t=j} b_s • c₁ᵗ`. -/
theorem curve_reading_convolution (x₀ : F) {n m : ℕ} (c₀ c₁ : ℕ → F[X]) (b : ℕ → F) (z : F) :
    (∑ t ∈ Finset.range n, (z - x₀) ^ t • c₀ t)
      + (∑ s ∈ Finset.range m, b s * (z - x₀) ^ s)
        • ∑ t ∈ Finset.range n, (z - x₀) ^ t • c₁ t
      = ∑ j ∈ Finset.range (n + m),
          (z - x₀) ^ j •
            ((if j < n then c₀ j else 0)
              + ∑ p ∈ (Finset.range m ×ˢ Finset.range n).filter (fun p => p.1 + p.2 = j),
                  b p.1 • c₁ p.2) := by
  classical
  have hsplit : ∀ j ∈ Finset.range (n + m), (z - x₀) ^ j •
      ((if j < n then c₀ j else 0)
        + ∑ p ∈ (Finset.range m ×ˢ Finset.range n).filter (fun p => p.1 + p.2 = j),
            b p.1 • c₁ p.2)
      = (z - x₀) ^ j • (if j < n then c₀ j else 0)
        + ∑ p ∈ (Finset.range m ×ˢ Finset.range n).filter (fun p => p.1 + p.2 = j),
            (z - x₀) ^ j • (b p.1 • c₁ p.2) := by
    intro j _
    rw [smul_add, Finset.smul_sum]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  · -- the `c₀` piece: extend the truncated sum by zeros
    have h1 : ∑ t ∈ Finset.range n, (z - x₀) ^ t • c₀ t
        = ∑ j ∈ Finset.range n, (z - x₀) ^ j • (if j < n then c₀ j else 0) :=
      Finset.sum_congr rfl (fun j hj => by rw [if_pos (Finset.mem_range.mp hj)])
    rw [h1]
    exact Finset.sum_subset (Finset.range_subset_range.mpr (Nat.le_add_right n m))
      (fun j _ hj => by rw [if_neg (fun h => hj (Finset.mem_range.mpr h)), smul_zero])
  · -- the convolution piece: fiberwise collapse over `s + t = j`
    have hfib : ∑ j ∈ Finset.range (n + m),
        ∑ p ∈ (Finset.range m ×ˢ Finset.range n).filter (fun p => p.1 + p.2 = j),
          (z - x₀) ^ j • (b p.1 • c₁ p.2)
        = ∑ p ∈ Finset.range m ×ˢ Finset.range n,
            (z - x₀) ^ (p.1 + p.2) • (b p.1 • c₁ p.2) := by
      have hinner : ∀ j ∈ Finset.range (n + m),
          ∑ p ∈ (Finset.range m ×ˢ Finset.range n).filter (fun p => p.1 + p.2 = j),
            (z - x₀) ^ j • (b p.1 • c₁ p.2)
          = ∑ p ∈ (Finset.range m ×ˢ Finset.range n).filter (fun p => p.1 + p.2 = j),
              (z - x₀) ^ (p.1 + p.2) • (b p.1 • c₁ p.2) := by
        intro j _
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [(Finset.mem_filter.mp hp).2]
      rw [Finset.sum_congr rfl hinner]
      refine Finset.sum_fiberwise_of_maps_to (fun p hp => ?_) _
      have h1 := Finset.mem_range.mp (Finset.mem_product.mp hp).1
      have h2 := Finset.mem_range.mp (Finset.mem_product.mp hp).2
      exact Finset.mem_range.mpr (by omega)
    rw [hfib, Finset.sum_product, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [smul_smul, smul_smul]
    congr 1
    rw [pow_add]
    ring

end PlaceReading

section PlaceReadingBundle

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The per-`z` place reading of the two-series form (the honest residual).**  At every good
`z`, the decoded `P z` reads the T-linear curve form with the series variable at `z − x₀` and
`T` at the branch value `r z`:
`P z = (∑_{t<n} (z−x₀)^t • c₀ᵗ) + r z • (∑_{t<n} (z−x₀)^t • c₁ᵗ)`.

Producing this datum is the genuine per-place-evaluation step (BCIKS20 §6.2 readings of the §5.2.7
`Z`-linear form): there is no in-tree evaluation homomorphism from `𝕃 H` to per-`z` codeword
polynomials — the per-`z` machinery (`IngredientC.MatchingVanishes`, Claims 5.10/5.11) produces
*vanishing* at places, not *readings*.  We therefore isolate the reading as a named structure with
its consumers proven below. -/
structure CurvePlaceReading {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F)
    (x₀ : F) (n : ℕ) (c₀ c₁ : ℕ → F[X]) : Type where
  /-- the per-`z` branch value of `T` at the place `z`. -/
  r : F → F
  /-- the per-`z` two-series reading of the decoded family on the good set. -/
  hread : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    P z = (∑ t ∈ Finset.range n, (z - x₀) ^ t • c₀ t)
      + r z • ∑ t ∈ Finset.range n, (z - x₀) ^ t • c₁ t

omit [Nonempty ι] [DecidableEq ι] in
/-- **The proven consumer: place readings with a rational branch are a curve family.**  If the
branch is a centred polynomial of `m` coefficients on the good set
(`r z = ∑_{s<m} b_s (z−x₀)^s` — the §5 branch-rationality) and `n + m < k + 2` (the GS degree
budget), the per-`z` readings convolve into a genuine `CurveFamilyData` with the explicit
coefficients `e_j = (if j < n then c₀ⱼ else 0) + ∑_{s+t=j} b_s • c₁ᵗ` — hence into every
keystone front door of `FaithfulCurveExtraction`. -/
noncomputable def curveFamilyData_of_placeReading {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c₀ c₁ : ℕ → F[X]} {m : ℕ} {b : ℕ → F}
    (hnm : n + m < k + 2)
    (d : CurvePlaceReading (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c₀ c₁)
    (hbranch : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      d.r z = ∑ s ∈ Finset.range m, b s * (z - x₀) ^ s) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  { x₀ := x₀
    n := n + m
    hn := hnm
    c := fun j => (if j < n then c₀ j else 0)
      + ∑ p ∈ (Finset.range m ×ˢ Finset.range n).filter (fun p => p.1 + p.2 = j),
          b p.1 • c₁ p.2
    hPz := fun z hz => by
      rw [d.hread z hz, hbranch z hz, curve_reading_convolution] }

omit [Nonempty ι] [DecidableEq ι] in
/-- **The keystone-facing witness from a place reading.**  Composes the proven consumer with
`hcoeffPoly_witness_of_curveFamilyData`: the place reading plus branch rationality yield the
bundled `hcoeffPoly` existential consumed by the §5 keystone front doors. -/
theorem hcoeffPoly_witness_of_placeReading {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c₀ c₁ : ℕ → F[X]} {m : ℕ} {b : ℕ → F}
    (hnm : n + m < k + 2)
    (d : CurvePlaceReading (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c₀ c₁)
    (hbranch : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      d.r z = ∑ s ∈ Finset.range m, b s * (z - x₀) ^ s) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z :=
  hcoeffPoly_witness_of_curveFamilyData (curveFamilyData_of_placeReading hnm d hbranch)

end PlaceReadingBundle

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FaithfulCurveExtraction.coeff_range_sum_C_mul_X_pow
#print axioms ArkLib.FaithfulCurveExtraction.gammaGenuine_eq_mk_curve_zLinear
#print axioms ArkLib.FaithfulCurveExtraction.gammaGenuine_eq_curve_sum_zLinear
#print axioms ArkLib.FaithfulCurveExtraction.coeffs_Z_linear_of_target
#print axioms ArkLib.FaithfulCurveExtraction.gammaGenuine_Z_linear_target_iff_coeffs_Z_linear
#print axioms ArkLib.FaithfulCurveExtraction.gammaGenuine_eq_curve_sum_two_series_of_target
#print axioms ArkLib.FaithfulCurveExtraction.gammaGenuine_eq_curve_sum_two_series_of_succ_window_of_monic
#print axioms ArkLib.FaithfulCurveExtraction.gammaGenuine_eq_curve_sum_two_series_of_succ_of_monic
#print axioms ArkLib.FaithfulCurveExtraction.curve_reading_convolution
#print axioms ArkLib.FaithfulCurveExtraction.CurvePlaceReading
#print axioms ArkLib.FaithfulCurveExtraction.curveFamilyData_of_placeReading
#print axioms ArkLib.FaithfulCurveExtraction.hcoeffPoly_witness_of_placeReading
