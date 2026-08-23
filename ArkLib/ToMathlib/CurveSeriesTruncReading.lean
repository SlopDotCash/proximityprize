/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CurveFamilyZLinear
import ArkLib.ToMathlib.ZLinearClosureAudit
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.WPowerInjective

/-!
# Issue #304 — the series-identity route: truncated descents and per-`z` readings

The per-`z` reading core, attacked at the **whole-series** level: instead of specializing the
curve identity coefficient-by-coefficient, we truncate the genuine series identity
(`gammaGenuine = ∑_{t<n} C (lift c_t) · X^t`, `CurveFamilyGenuine.gammaGenuine_eq_curve_sum`)
to a polynomial over `𝕃 H`, descend it through the injective base embedding
`liftToFunctionField : F[X] →+* 𝕃 H` to a single polynomial `Q ∈ (F[X])[X]`, and read it at a
place `z` by evaluating the curve variable at `C (z − x₀)` (`Polynomial.eval`).

## What is PROVEN here

* **Descent existence and canonicity (single series).**
  `trunc m γ = map lift (curvePoly n c)` (`map_lift_curvePoly_eq_trunc`,
  `trunc_gammaGenuine_eq_map_curvePoly`), and ANY descent `Q` with
  `map lift Q = trunc m γ` equals `curvePoly n c` (`eq_curvePoly_of_map_lift_eq_trunc`, via
  `WPowerInjective.liftToFunctionField_injective`).  So the truncated genuine root has a
  *unique* codeword-polynomial representative — no witness freedom.
* **The reading is trunc-evaluation algebra.**  `(curvePoly n c).eval (C a) = ∑_{t<n} a^t • c_t`
  (`eval_curvePoly`), and for any `Q` of bounded degree
  `Q.eval (C a) = ∑_{t<n} a^t • Q.coeff t` (`eval_C_eq_centred_sum`).
* **THE COLLAPSE, machine-checked** (`trunc_reading_iff`, `gammaGenuine_trunc_reading_iff`):
  given the base-rationality + truncation hypotheses, the per-`z` series-route residual
  "`P z` equals the reading at `z` of some descent of `trunc m γ`" is **equivalent** to the
  faithful `hPz` conclusion `P z = ∑_{t<n} (z−x₀)^t • c_t`.  The orchestrating question — does
  the family/series route reduce the per-`z` residual? — is answered precisely: it does NOT
  shrink it (the coefficients `c_t` are series-constants, so the reading is forced), but it
  does make the descent **canonical**.  The genuine remaining content of the per-`z` core is
  exactly the identification of the decoded `P z` with the reading — nothing else.
* **Two-series (Claim 5.9 / `Z`-linear) canonicity at `d_H ≥ 2`** (`zLinear_repr_unique`,
  `two_series_descent_unique`): the affine-in-`T` representation
  `lift c₀ + T · lift c₁` is **unique** for every curve with `2 ≤ H.natDegree`
  (representatives below the modulus, `ZLinearClosureAudit.eq_of_liftBivariate_eq_of_natDegree_lt`).
  Hence the Claim 5.9 target's witnesses `c₀ᵗ, c₁ᵗ` are canonical, the truncated two-series
  descent `(Q₀, Q₁)` is unique, and the per-`z` two-series reading collapse holds
  (`two_series_trunc_reading_iff`): per-`z` existential witness freedom in the reading residual
  is eliminated — all witnesses are forced to be the global `curvePoly n c₀, curvePoly n c₁`.
* **Producers (keystone front doors).**  `curveFamilyData_of_descentReading` (a single global
  descent polynomial `Q` of degree `≤ k` plus per-`z` readings gives `CurveFamilyData`),
  `curveFamilyData_of_gammaGenuine_truncReading` (readings of the truncated genuine root),
  `curvePlaceReading_of_descentReading` (the two-series reading bundle), and
  `curveFamilyData_of_gammaGenuine_twoSeriesReading` (per-`z` two-series readings of the
  truncated genuine root with a rational branch, `d_H ≥ 2` — the per-`z` witnesses are
  quantified per `z` but forced globally constant by canonicity).
* **Interface interderivability** (`αGenuine_eq_lift_coeff_of_truncDescent`,
  `lift_coeff_eq_coeff_of_map_eq_trunc`): the whole-series trunc-descent interface implies the
  per-coefficient base-rationality interface (`hbase`) with `c := Q.coeff` — the series lane
  and the per-coefficient lane consume interchangeable currencies.

## Honest residuals (unchanged in content, sharpened in form)

The per-`z` reading identification itself — `P z = Q.eval (C (z − x₀))` on the good set —
remains the irreducible per-`z` core (provably equivalent to `hPz`/`CurvePlaceReading.hread`
by the collapse theorems here; producing it needs the per-place evaluation of the `𝕃 H`
identity, which has no in-tree homomorphism).  This file contributes canonicity (descent and
witness uniqueness), the trunc/eval bridge algebra, and proven keystone-facing consumers.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Prop. 5.5, Claim 5.9, §5.2.7), §6.2, Appendix A.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open BCIKS20.HenselNumerator.S5Genuine
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace FaithfulCurveExtraction

namespace TruncReading

/-! ## Part 0 — the descended curve polynomial and its trunc/eval algebra (generic) -/

section Generic

/-- **The descended curve polynomial**: `curvePoly n c = ∑_{t<n} C (c t) · X^t` — the canonical
polynomial (over the coefficient ring) carrying the first `n` curve coefficients.  Over
`S = F[X]` this is the codeword-polynomial curve; its image under `map lift` is the truncated
series identity's polynomial form over `𝕃 H`. -/
noncomputable def curvePoly {S : Type} [CommSemiring S] (n : ℕ) (c : ℕ → S) : Polynomial S :=
  ∑ t ∈ Finset.range n, Polynomial.C (c t) * Polynomial.X ^ t

/-- Coefficients of the descended curve polynomial: `if s < n then c s else 0`. -/
theorem coeff_curvePoly {S : Type} [CommSemiring S] (n : ℕ) (c : ℕ → S) (s : ℕ) :
    (curvePoly n c).coeff s = if s < n then c s else 0 := by
  simp only [curvePoly]
  rw [Polynomial.finset_sum_coeff]
  by_cases hs : s < n
  · rw [if_pos hs, Finset.sum_eq_single s
      (fun t _ hts => by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hts h.symm),
          mul_zero])
      (fun hs' => absurd (Finset.mem_range.mpr hs) hs'),
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun t ht => ?_
    have hts : s ≠ t := fun h => hs (h ▸ Finset.mem_range.mp ht)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hts, mul_zero]

/-- The descended curve polynomial is functorial in the coefficient ring. -/
theorem map_curvePoly {S T : Type} [CommSemiring S] [CommSemiring T] (f : S →+* T) (n : ℕ)
    (c : ℕ → S) :
    (curvePoly n c).map f = curvePoly n (fun t => f (c t)) := by
  ext s
  rw [Polynomial.coeff_map, coeff_curvePoly, coeff_curvePoly]
  split_ifs with h
  · rfl
  · exact map_zero f

/-- **Truncation of a curve series is the descended curve polynomial**: for `n ≤ m`,
`trunc m (∑_{t<n} C (g t) · X^t) = curvePoly n g`. -/
theorem trunc_curve_sum {S : Type} [CommSemiring S] {n m : ℕ} (hnm : n ≤ m) (g : ℕ → S) :
    PowerSeries.trunc m (∑ t ∈ Finset.range n, PowerSeries.C (g t) * PowerSeries.X ^ t)
      = curvePoly n g := by
  ext s
  rw [PowerSeries.coeff_trunc, coeff_range_sum_C_mul_X_pow n g s, coeff_curvePoly n g s]
  by_cases hsm : s < m
  · rw [if_pos hsm]
  · have hsn : ¬ s < n := fun h => hsm (lt_of_lt_of_le h hnm)
    rw [if_neg hsm, if_neg hsn]

/-- **Truncation of a two-series (`T`-linear) curve form**: for `n ≤ m`,
`trunc m (V₀ + C τ · V₁) = curvePoly n g₀ + C τ · curvePoly n g₁`. -/
theorem trunc_two_series {S : Type} [CommSemiring S] {n m : ℕ} (hnm : n ≤ m)
    (g₀ g₁ : ℕ → S) (τ : S) :
    PowerSeries.trunc m
        ((∑ t ∈ Finset.range n, PowerSeries.C (g₀ t) * PowerSeries.X ^ t)
          + PowerSeries.C τ * ∑ t ∈ Finset.range n, PowerSeries.C (g₁ t) * PowerSeries.X ^ t)
      = curvePoly n g₀ + Polynomial.C τ * curvePoly n g₁ := by
  ext s
  rw [PowerSeries.coeff_trunc, map_add, PowerSeries.coeff_C_mul,
    coeff_range_sum_C_mul_X_pow n g₀ s, coeff_range_sum_C_mul_X_pow n g₁ s,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_curvePoly n g₀ s,
    coeff_curvePoly n g₁ s]
  by_cases hsm : s < m
  · rw [if_pos hsm]
  · have hsn : ¬ s < n := fun h => hsm (lt_of_lt_of_le h hnm)
    rw [if_neg hsm, if_neg hsn, if_neg hsn, mul_zero, add_zero]

/-- **The per-`z` reading IS trunc-evaluation algebra**: evaluating the descended curve
polynomial at the constant `C a` (curve variable ↦ `a = z − x₀`) yields the centred sum
`∑_{t<n} a^t • c_t` — the `hPz` shape of `CurveFamilyData`. -/
theorem eval_curvePoly {R : Type} [CommSemiring R] (n : ℕ) (c : ℕ → Polynomial R) (a : R) :
    (curvePoly n c).eval (Polynomial.C a) = ∑ t ∈ Finset.range n, a ^ t • c t := by
  simp only [curvePoly]
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ← Polynomial.C_pow, Polynomial.smul_eq_C_mul]
  ring

/-- The reading of an arbitrary degree-bounded polynomial over `F[X]`: for `Q.natDegree < n`,
`Q.eval (C a) = ∑_{t<n} a^t • Q.coeff t`. -/
theorem eval_C_eq_centred_sum {R : Type} [CommSemiring R] {Q : Polynomial (Polynomial R)}
    {n : ℕ} (hQ : Q.natDegree < n) (a : R) :
    Q.eval (Polynomial.C a) = ∑ t ∈ Finset.range n, a ^ t • Q.coeff t := by
  rw [Polynomial.eval_eq_sum_range' hQ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Polynomial.C_pow, Polynomial.smul_eq_C_mul]
  ring

end Generic

/-! ## Part 1 — single-series descent through the injective lift, and the reading collapse -/

section SingleSeries

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **Descent existence**: if `γ` is the curve series `∑_{t<n} C (lift (c t)) · X^t`, its
`m`-truncation (`n ≤ m`) is the lift of the descended curve polynomial. -/
theorem map_lift_curvePoly_eq_trunc {n m : ℕ} (hnm : n ≤ m) {γ : PowerSeries (𝕃 H)}
    {c : ℕ → F[X]}
    (hγ : γ = ∑ t ∈ Finset.range n,
      PowerSeries.C (liftToFunctionField (H := H) (c t)) * PowerSeries.X ^ t) :
    Polynomial.map (liftToFunctionField (H := H)) (curvePoly n c) = PowerSeries.trunc m γ := by
  rw [hγ, trunc_curve_sum hnm (fun t => liftToFunctionField (H := H) (c t)),
    map_curvePoly (liftToFunctionField (H := H)) n c]

omit [Fact (Irreducible H)] in
/-- **Descent canonicity**: any `Q ∈ (F[X])[X]` whose lift is the truncated curve series equals
the descended curve polynomial — `liftToFunctionField` is injective, so the descent is unique.
No choice is involved in reading the truncated genuine root over the base. -/
theorem eq_curvePoly_of_map_lift_eq_trunc {n m : ℕ} (hnm : n ≤ m) {γ : PowerSeries (𝕃 H)}
    {c : ℕ → F[X]}
    (hγ : γ = ∑ t ∈ Finset.range n,
      PowerSeries.C (liftToFunctionField (H := H) (c t)) * PowerSeries.X ^ t)
    {Q : Polynomial F[X]}
    (hQ : Polynomial.map (liftToFunctionField (H := H)) Q = PowerSeries.trunc m γ) :
    Q = curvePoly n c :=
  Polynomial.map_injective _ (BCIKS20.WPow.liftToFunctionField_injective H)
    (by rw [hQ, map_lift_curvePoly_eq_trunc H hnm hγ])

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- A trunc-descent recovers the series coefficients below the truncation level:
`lift (Q.coeff t) = coeff t γ` for `t < m`.  (The bridge from the whole-series interface to the
per-coefficient interface.) -/
theorem lift_coeff_eq_coeff_of_map_eq_trunc {m : ℕ} {γ : PowerSeries (𝕃 H)}
    {Q : Polynomial F[X]}
    (hQ : Polynomial.map (liftToFunctionField (H := H)) Q = PowerSeries.trunc m γ)
    {t : ℕ} (ht : t < m) :
    liftToFunctionField (H := H) (Q.coeff t) = PowerSeries.coeff t γ := by
  have h : (Polynomial.map (liftToFunctionField (H := H)) Q).coeff t
      = (PowerSeries.trunc m γ).coeff t := by rw [hQ]
  rwa [Polynomial.coeff_map, PowerSeries.coeff_trunc, if_pos ht] at h

omit [Fact (Irreducible H)] in
/-- **THE READING COLLAPSE (single series), machine-checked.**  Given the curve-series identity,
the per-`z` series-route residual — "`p` is the reading at `a` of SOME descent of `trunc m γ`" —
is **equivalent** to the faithful `hPz` shape `p = ∑_{t<n} a^t • c_t`.  Forward: the descent is
unique (`eq_curvePoly_of_map_lift_eq_trunc`) and its reading is forced (`eval_curvePoly`);
backward: `curvePoly n c` is a descent.  The series-identity route therefore adds canonicity
but cannot shrink the per-`z` identification residual. -/
theorem trunc_reading_iff {n m : ℕ} (hnm : n ≤ m) {γ : PowerSeries (𝕃 H)} {c : ℕ → F[X]}
    (hγ : γ = ∑ t ∈ Finset.range n,
      PowerSeries.C (liftToFunctionField (H := H) (c t)) * PowerSeries.X ^ t)
    (a : F) (p : F[X]) :
    (∃ Q : Polynomial F[X],
        Polynomial.map (liftToFunctionField (H := H)) Q = PowerSeries.trunc m γ ∧
          p = Q.eval (Polynomial.C a))
      ↔ p = ∑ t ∈ Finset.range n, a ^ t • c t := by
  constructor
  · rintro ⟨Q, hQ, hp⟩
    rw [hp, eq_curvePoly_of_map_lift_eq_trunc H hnm hγ hQ, eval_curvePoly]
  · intro hp
    exact ⟨curvePoly n c, map_lift_curvePoly_eq_trunc H hnm hγ,
      by rw [hp, eval_curvePoly]⟩

/-- **The genuine root's truncation descends canonically** under the base-rationality (`hbase`)
and truncation (`htail`) hypotheses of `gammaGenuine_eq_curve_sum`:
`trunc m γ = map lift (curvePoly n c)` for every `m ≥ n`. -/
theorem trunc_gammaGenuine_eq_map_curvePoly {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) {n m : ℕ} (hnm : n ≤ m) {c : ℕ → F[X]}
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) (c t))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    PowerSeries.trunc m (gammaGenuine x₀ R H hHyp)
      = Polynomial.map (liftToFunctionField (H := H)) (curvePoly n c) :=
  (map_lift_curvePoly_eq_trunc H hnm (gammaGenuine_eq_curve_sum hHyp hbase htail)).symm

/-- **Interface interderivability**: a trunc-descent of the genuine root yields the
per-coefficient base-rationality interface (`hbase`) with `c := Q.coeff` — the whole-series
lane and the per-coefficient lane consume interchangeable currencies. -/
theorem αGenuine_eq_lift_coeff_of_truncDescent {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) {m : ℕ} {Q : Polynomial F[X]}
    (hQ : Polynomial.map (liftToFunctionField (H := H)) Q
      = PowerSeries.trunc m (gammaGenuine x₀ R H hHyp)) :
    ∀ t < m, αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) (Q.coeff t) := by
  intro t ht
  have h := lift_coeff_eq_coeff_of_map_eq_trunc H hQ ht
  have hcoeff : αGenuine H x₀ R hHyp t
      = PowerSeries.coeff t (gammaGenuine x₀ R H hHyp) := rfl
  rw [hcoeff, ← h]

/-- **The reading collapse at the genuine root**: under `hbase`/`htail`, the per-`z` reading of
any descent of `trunc m (gammaGenuine)` at `z` is exactly the faithful `hPz` body
`p = ∑_{t<n} (z − x₀)^t • c_t`. -/
theorem gammaGenuine_trunc_reading_iff {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) {n m : ℕ} (hnm : n ≤ m) {c : ℕ → F[X]}
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) (c t))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) (z : F) (p : F[X]) :
    (∃ Q : Polynomial F[X],
        Polynomial.map (liftToFunctionField (H := H)) Q
            = PowerSeries.trunc m (gammaGenuine x₀ R H hHyp) ∧
          p = Q.eval (Polynomial.C (z - x₀)))
      ↔ p = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t :=
  trunc_reading_iff H hnm (gammaGenuine_eq_curve_sum hHyp hbase htail) (z - x₀) p

end SingleSeries

/-! ## Part 2 — two-series (Claim 5.9 / `Z`-linear) canonicity at `d_H ≥ 2` -/

section TwoSeries

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

omit [Fact (Irreducible H)] in
/-- **Canonicity of the affine-in-`T` representation for `d_H ≥ 2`.**  The Claim 5.9 coefficient
shape `lift c₀ + T · lift c₁` determines its witnesses: two representations of the same element
of `𝕃 H` agree coordinatewise.  (Representatives `C c₀ + X · C c₁` have `Y`-degree `≤ 1 < d_H`,
so they live below the modulus and `liftBivariate` is faithful there.)  Consequence: the
witnesses in `S5Genuine.gammaGenuine_Z_linear_target` and in
`CurveFamilyZLinear`'s per-coefficient form are unique for every curve with `2 ≤ H.natDegree`. -/
theorem zLinear_repr_unique (hdeg : 2 ≤ H.natDegree) {a₀ a₁ b₀ b₁ : F[X]}
    (h : liftToFunctionField (H := H) a₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) a₁
        = liftToFunctionField (H := H) b₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) b₁) :
    a₀ = b₀ ∧ a₁ = b₁ := by
  have hbig : liftBivariate (H := H)
        (Polynomial.C a₀ + Polynomial.X * Polynomial.C a₁ : F[X][Y])
      = liftBivariate (H := H)
        (Polynomial.C b₀ + Polynomial.X * Polynomial.C b₁ : F[X][Y]) := by
    simp only [map_add, map_mul, liftBivariate_C, liftBivariate_X]
    exact h
  have heq := BCIKS20.ZLinearClosureAudit.eq_of_liftBivariate_eq_of_natDegree_lt H hbig
    (lt_of_le_of_lt (BCIKS20.ZLinearClosureAudit.natDegree_linear_le a₀ a₁) (by omega))
    (lt_of_le_of_lt (BCIKS20.ZLinearClosureAudit.natDegree_linear_le b₀ b₁) (by omega))
  constructor
  · have h0 : (Polynomial.C a₀ + Polynomial.X * Polynomial.C a₁ : F[X][Y]).coeff 0
        = (Polynomial.C b₀ + Polynomial.X * Polynomial.C b₁ : F[X][Y]).coeff 0 := by rw [heq]
    rwa [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.mul_coeff_zero,
      Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, zero_mul, add_zero,
      add_zero, Polynomial.coeff_C_zero, Polynomial.coeff_C_zero] at h0
  · have h1 : (Polynomial.C a₀ + Polynomial.X * Polynomial.C a₁ : F[X][Y]).coeff 1
        = (Polynomial.C b₀ + Polynomial.X * Polynomial.C b₁ : F[X][Y]).coeff 1 := by rw [heq]
    have hXC : ∀ q : F[X], (Polynomial.X * Polynomial.C q : F[X][Y]).coeff 1 = q := fun q => by
      rw [show (1 : ℕ) = 0 + 1 from rfl, Polynomial.coeff_X_mul, Polynomial.coeff_C_zero]
    rw [Polynomial.coeff_add, Polynomial.coeff_add, hXC, hXC] at h1
    simpa [Polynomial.coeff_C] using h1

omit [Fact (Irreducible H)] in
/-- **Two-series descent canonicity (`d_H ≥ 2`)**: the truncated two-series decomposition
`map lift Q₀ + C(T) · map lift Q₁` determines `(Q₀, Q₁)` uniquely — coefficientwise by
`zLinear_repr_unique`. -/
theorem two_series_descent_unique (hdeg : 2 ≤ H.natDegree) {Q₀ Q₁ Q₀' Q₁' : Polynomial F[X]}
    (h : Polynomial.map (liftToFunctionField (H := H)) Q₀
          + Polynomial.C (functionFieldT (H := H))
            * Polynomial.map (liftToFunctionField (H := H)) Q₁
        = Polynomial.map (liftToFunctionField (H := H)) Q₀'
          + Polynomial.C (functionFieldT (H := H))
            * Polynomial.map (liftToFunctionField (H := H)) Q₁') :
    Q₀ = Q₀' ∧ Q₁ = Q₁' := by
  have hco : ∀ s : ℕ,
      liftToFunctionField (H := H) (Q₀.coeff s)
          + functionFieldT (H := H) * liftToFunctionField (H := H) (Q₁.coeff s)
        = liftToFunctionField (H := H) (Q₀'.coeff s)
          + functionFieldT (H := H) * liftToFunctionField (H := H) (Q₁'.coeff s) := by
    intro s
    have hs : (Polynomial.map (liftToFunctionField (H := H)) Q₀
          + Polynomial.C (functionFieldT (H := H))
            * Polynomial.map (liftToFunctionField (H := H)) Q₁).coeff s
        = (Polynomial.map (liftToFunctionField (H := H)) Q₀'
          + Polynomial.C (functionFieldT (H := H))
            * Polynomial.map (liftToFunctionField (H := H)) Q₁').coeff s := by rw [h]
    rwa [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_map, Polynomial.coeff_map,
      Polynomial.coeff_map, Polynomial.coeff_map] at hs
  exact ⟨Polynomial.ext fun s => (zLinear_repr_unique H hdeg (hco s)).1,
    Polynomial.ext fun s => (zLinear_repr_unique H hdeg (hco s)).2⟩

/-- **The genuine root's truncation in two-series form**: under the `Z`-linear base shape
(`hbase`, Claim 5.9's per-coefficient form) and truncation (`htail`),
`trunc m γ = map lift (curvePoly n c₀) + C(T) · map lift (curvePoly n c₁)` for `m ≥ n`. -/
theorem trunc_gammaGenuine_eq_two_series {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) {n m : ℕ} (hnm : n ≤ m) {c₀ c₁ : ℕ → F[X]}
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) (c₀ t)
        + functionFieldT (H := H) * liftToFunctionField (H := H) (c₁ t))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    PowerSeries.trunc m (gammaGenuine x₀ R H hHyp)
      = Polynomial.map (liftToFunctionField (H := H)) (curvePoly n c₀)
        + Polynomial.C (functionFieldT (H := H))
          * Polynomial.map (liftToFunctionField (H := H)) (curvePoly n c₁) := by
  rw [gammaGenuine_eq_curve_sum_zLinear hHyp hbase htail,
    trunc_two_series hnm (fun t => liftToFunctionField (H := H) (c₀ t))
      (fun t => liftToFunctionField (H := H) (c₁ t)) (functionFieldT (H := H)),
    map_curvePoly (liftToFunctionField (H := H)) n c₀,
    map_curvePoly (liftToFunctionField (H := H)) n c₁]

/-- **THE READING COLLAPSE (two series, `d_H ≥ 2`), machine-checked.**  Under the Claim 5.9
`Z`-linear base shape and truncation, the per-`z` two-series reading residual — "`p` is the
branch-weighted reading of SOME two-series descent of `trunc m γ`" — is **equivalent** to the
`CurvePlaceReading.hread` body with the canonical `c₀, c₁`.  Per-`z` witness freedom is
eliminated: every witness pair is forced to `(curvePoly n c₀, curvePoly n c₁)`. -/
theorem two_series_trunc_reading_iff (hdeg : 2 ≤ H.natDegree) {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) {n m : ℕ} (hnm : n ≤ m) {c₀ c₁ : ℕ → F[X]}
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) (c₀ t)
        + functionFieldT (H := H) * liftToFunctionField (H := H) (c₁ t))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) (z r : F) (p : F[X]) :
    (∃ Q₀ Q₁ : Polynomial F[X],
        Polynomial.map (liftToFunctionField (H := H)) Q₀
            + Polynomial.C (functionFieldT (H := H))
              * Polynomial.map (liftToFunctionField (H := H)) Q₁
            = PowerSeries.trunc m (gammaGenuine x₀ R H hHyp) ∧
          p = Q₀.eval (Polynomial.C (z - x₀)) + r • Q₁.eval (Polynomial.C (z - x₀)))
      ↔ p = (∑ t ∈ Finset.range n, (z - x₀) ^ t • c₀ t)
          + r • ∑ t ∈ Finset.range n, (z - x₀) ^ t • c₁ t := by
  constructor
  · rintro ⟨Q₀, Q₁, hQ, hp⟩
    rw [trunc_gammaGenuine_eq_two_series H hHyp hnm hbase htail] at hQ
    obtain ⟨h₀, h₁⟩ := two_series_descent_unique H hdeg hQ
    rw [hp, h₀, h₁, eval_curvePoly, eval_curvePoly]
  · intro hp
    exact ⟨curvePoly n c₀, curvePoly n c₁,
      (trunc_gammaGenuine_eq_two_series H hHyp hnm hbase htail).symm,
      by rw [hp, eval_curvePoly, eval_curvePoly]⟩

end TwoSeries

/-! ## Part 3 — keystone-facing producers -/

section Producers

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty ι] [DecidableEq ι] in
/-- **`CurveFamilyData` from a single global descent polynomial.**  A polynomial
`Q ∈ (F[X])[X]` of curve-degree `≤ k` plus the per-`z` reading identification
`P z = Q.eval (C (z − x₀))` on the good set yield the faithful per-`(u, P)` §5 extraction
datum, with curve coefficients `c := Q.coeff`.  This is the leanest interface of the
series-identity lane: ONE global object and the per-`z` identification — nothing else. -/
noncomputable def curveFamilyData_of_descentReading {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (x₀ : F) (Q : Polynomial F[X]) (hQ : Q.natDegree ≤ k)
    (hread : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      P z = Q.eval (Polynomial.C (z - x₀))) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  { x₀ := x₀
    n := k + 1
    hn := by omega
    c := Q.coeff
    hPz := fun z hz => by
      rw [hread z hz, eval_C_eq_centred_sum (lt_of_le_of_lt hQ (Nat.lt_succ_self k))] }

omit [Nonempty ι] [DecidableEq ι] in
/-- **`CurveFamilyData` from per-`z` readings of the truncated genuine root.**  Base-rationality
(`hbase`) and truncation (`htail`) of the genuine Hensel coefficients, plus the per-`z` reading
of (any, hence the canonical) descent of `trunc m (gammaGenuine)`, produce the faithful datum.
The per-`z` existential carries no real freedom (`eq_curvePoly_of_map_lift_eq_trunc`). -/
noncomputable def curveFamilyData_of_gammaGenuine_truncReading {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    {n m : ℕ} (hn : n < k + 2) (hnm : n ≤ m) {c : ℕ → F[X]}
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) (c t))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (hread : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ∃ Q : Polynomial F[X],
        Polynomial.map (liftToFunctionField (H := H)) Q
            = PowerSeries.trunc m (gammaGenuine x₀ R H hHyp) ∧
          P z = Q.eval (Polynomial.C (z - x₀))) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  { x₀ := x₀
    n := n
    hn := hn
    c := c
    hPz := fun z hz =>
      (gammaGenuine_trunc_reading_iff H hHyp hnm hbase htail z (P z)).mp (hread z hz) }

omit [Nonempty ι] [DecidableEq ι] in
/-- **`CurvePlaceReading` from a two-series descent reading**: two global descent polynomials of
curve-degree `< n` plus the per-`z` branch-weighted reading identification yield the place
reading bundle with coefficient data `Q₀.coeff, Q₁.coeff`. -/
noncomputable def curvePlaceReading_of_descentReading {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (x₀ : F) {n : ℕ} (Q₀ Q₁ : Polynomial F[X]) (h₀ : Q₀.natDegree < n) (h₁ : Q₁.natDegree < n)
    (r : F → F)
    (hread : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      P z = Q₀.eval (Polynomial.C (z - x₀)) + r z • Q₁.eval (Polynomial.C (z - x₀))) :
    CurvePlaceReading (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n
      Q₀.coeff Q₁.coeff :=
  { r := r
    hread := fun z hz => by
      rw [hread z hz, eval_C_eq_centred_sum h₀, eval_C_eq_centred_sum h₁] }

omit [Nonempty ι] [DecidableEq ι] in
/-- **`CurveFamilyData` from per-`z` two-series readings of the truncated genuine root
(`d_H ≥ 2`).**  The Claim 5.9 `Z`-linear base shape + truncation + per-`z` branch-weighted
readings of (any) two-series descent of `trunc m (gammaGenuine)`, with a centred-polynomial
branch of `mb` coefficients and the GS budget `n + mb < k + 2`, produce the faithful datum.
The per-`z` witness pairs are forced globally constant by `two_series_descent_unique`. -/
noncomputable def curveFamilyData_of_gammaGenuine_twoSeriesReading {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) (hdeg : 2 ≤ H.natDegree)
    {n m : ℕ} (hnm : n ≤ m) {c₀ c₁ : ℕ → F[X]} {mb : ℕ} {b : ℕ → F}
    (hnmb : n + mb < k + 2)
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) (c₀ t)
        + functionFieldT (H := H) * liftToFunctionField (H := H) (c₁ t))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (hread : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ∃ Q₀ Q₁ : Polynomial F[X],
        Polynomial.map (liftToFunctionField (H := H)) Q₀
            + Polynomial.C (functionFieldT (H := H))
              * Polynomial.map (liftToFunctionField (H := H)) Q₁
            = PowerSeries.trunc m (gammaGenuine x₀ R H hHyp) ∧
          P z = Q₀.eval (Polynomial.C (z - x₀))
            + (∑ s ∈ Finset.range mb, b s * (z - x₀) ^ s)
              • Q₁.eval (Polynomial.C (z - x₀))) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  let d : CurvePlaceReading (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c₀ c₁ :=
    { r := fun z => ∑ s ∈ Finset.range mb, b s * (z - x₀) ^ s
      hread := fun z hz => by
        obtain ⟨Q₀, Q₁, hQ, hp⟩ := hread z hz
        exact (two_series_trunc_reading_iff H hdeg hHyp hnm hbase htail z
          (∑ s ∈ Finset.range mb, b s * (z - x₀) ^ s) (P z)).mp ⟨Q₀, Q₁, hQ, hp⟩ }
  curveFamilyData_of_placeReading (b := b) hnmb d (fun z hz => rfl)

end Producers

end TruncReading

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.curvePoly
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.coeff_curvePoly
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.map_curvePoly
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.trunc_curve_sum
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.trunc_two_series
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.eval_curvePoly
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.eval_C_eq_centred_sum
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.map_lift_curvePoly_eq_trunc
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.eq_curvePoly_of_map_lift_eq_trunc
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.lift_coeff_eq_coeff_of_map_eq_trunc
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.trunc_reading_iff
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.trunc_gammaGenuine_eq_map_curvePoly
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.αGenuine_eq_lift_coeff_of_truncDescent
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.gammaGenuine_trunc_reading_iff
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.zLinear_repr_unique
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.two_series_descent_unique
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.trunc_gammaGenuine_eq_two_series
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.two_series_trunc_reading_iff
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.curveFamilyData_of_descentReading
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.curveFamilyData_of_gammaGenuine_truncReading
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.curvePlaceReading_of_descentReading
#print axioms ArkLib.FaithfulCurveExtraction.TruncReading.curveFamilyData_of_gammaGenuine_twoSeriesReading
