/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CurveHenselDatumProducers

/-!
# Issue #304 — the `π̂_z` base-rational reading: `htrunc` DERIVED from base-rationality

`curveHenselDatum_of_truncatedLocalRoot` (the analytic per-`z` producer of the faithful
`CurveHenselDatum`) consumes the per-`z` base-rational reading

```
htrunc : (PowerSeries.trunc n (localSeries hHyp z (root z) (hx z hz)) : Polynomial F)
           = ∑ t ∈ Finset.range n, (z − x₀) ^ t • c t
```

as an *input*.  This file DERIVES it from the §5 base-rationality of the genuine Hensel
coefficients (`hbase : αGenuine t = liftToFunctionField (c t)`, the exact hypothesis shape of
`CurveFamilyGenuine.gammaGenuine_eq_curve_sum`), eliminating `htrunc` from the analytic lane.

## The composition (monic `H`)

1. **`𝒪`-descent of base-rationality** (`βHensel_eq_mk_C_mul_ξ_pow_of_base_rational`):
   `αGenuine t = lift (c t)` forces, via the proven monic lift identity
   `emb (βHensel t) = αGenuine t · W^{t+1} · (emb ξ)^{2t−1}` and injectivity of `𝒪 H ↪ 𝕃 H`,
   the `𝒪`-level factorization `βHensel t = mk (C (c t)) · ξ^{2t−1}`.
2. **The place reading** (`π_z_βHensel_of_base_rational`,
   `coeff_localSeries_eq_eval_of_base_rational`): applying the ring hom `π_z` (X ↦ z, Y ↦ root)
   and the read-off `coeff t (localSeries) · π_z(ξ)^{2t−1} = π_z(βHensel t)` gives — after
   cancelling the nonzero `π_z(ξ)^{2t−1}` — the clean per-coefficient reading
   `coeff t (localSeries hHyp z root hx) = (c t).eval z`.
   (`π̂_z` of the lift of `c` is `c` **evaluated at `z`** — a scalar, not a polynomial: the
   composition `π_z ∘ mk ∘ C = eval z` is `π_z_mk` + `evalEval_C`.)
3. **The transposition identity** (`sum_C_eval_eq_transposed_curve_sum`, pure algebra): the
   truncated reading `∑_{t<n} C ((c t).eval z) · X^t` IS a polynomial curve in `z` — recentre
   each scalar `(c t).eval z` at `x₀` by Taylor expansion and exchange the two finite sums:
   `∑_{t<n} C ((c t).eval z)·X^t = ∑_{s<N} (z − x₀)^s • cᵀ_s` with the **transposed
   coefficients** `cᵀ_s := ∑_{t<n} C ((taylor x₀ (c t)).coeff s) · X^t`
   (`transposedCurveCoeffs`), valid for every `z` once `N` exceeds all `natDegree (c t)`.
4. **The supplied `htrunc`** (`trunc_localSeries_of_base_rational`,
   `htrunc_of_base_rational`): the degree-`< N` truncation of the local series has coefficients
   `(c t).eval z` below `n` (step 2) and `0` on `[n, N)` (tail vanishing of `αGenuine`,
   transported through the monic `BetaRecGenuineBridge`), so it equals the transposed curve sum
   — exactly the shape `curveHenselDatum_of_truncatedLocalRoot` demands.
5. **The producers** (`curveHenselDatum_of_baseRational`, `curveFamilyData_of_baseRational`):
   the faithful per-`(u, P)` bundles with `htrunc` REMOVED from the input surface; the curve
   coefficients of the output are the explicit `transposedCurveCoeffs x₀ n c`.

## Honest remaining inputs after this file (analytic lane)

`hbase` (the §5 rational-section content below `n`), `hvanish` (tail vanishing of `αGenuine`,
supplied on `[k, T]` by `αGenuine_eq_zero_on_range_of_matching_monic` and beyond `T` by the
algebraic-degree lane), and the decoded-side GS cargo `hdvd`/`hcong` (`MatchingFactorLift`).
The per-`z` base-rational reading `htrunc` is no longer one of them.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Prop. 5.5), §6.2 (Hensel uniqueness `π_z(γ) = P_z`), Appendix A.3–A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code NNReal Finset Function
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open scoped BigOperators ENNReal

namespace ArkLib

/-! ## Part 1 — the `𝒪`-descent of base-rationality and the per-`z` coefficient reading -/

section Reading

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **`𝒪`-descent of base-rationality (monic).**  If the genuine Hensel coefficient is
base-rational, `αGenuine t = lift (c t)`, then the `(A.1)` numerator factors in `𝒪 H` as
`βHensel t = mk (C (c t)) · ξ^{2t−1}`: combine the proven monic lift identity
`emb (βHensel t) = αGenuine t · W^{t+1} · (emb ξ)^{2t−1}` with `W = 1` and the injectivity of
`𝒪 H ↪ 𝕃 H`. -/
theorem βHensel_eq_mk_C_mul_ξ_pow_of_base_rational {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) {t : ℕ} {ct : F[X]}
    (hbase : αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) ct) :
    βHensel H x₀ R hHyp t
      = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C ct)
          * (ξ x₀ R H hHyp) ^ (2 * t - 1) := by
  apply embeddingOf𝒪Into𝕃_injective (Fact.out)
  rw [map_mul, map_pow, emb_mk_C,
    βHensel_lift_identity_of_monic H x₀ R hHyp hlc t, hbase, hlc, map_one, one_pow, mul_one]

/-- **The place reading of the `(A.1)` numerator at a base-rational order:**
`π_z (βHensel t) = (c t).eval z · π_z(ξ)^{2t−1}`.  The composition `π_z ∘ mk ∘ C` is evaluation
at `z` (`π_z_mk` + `evalEval_C`) — the `π̂_z`-reading of the lift of a base polynomial is the
polynomial **evaluated at the place**, a scalar. -/
theorem π_z_βHensel_of_base_rational {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z) {t : ℕ} {ct : F[X]}
    (hbase : αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) ct) :
    (π_z z root) (βHensel H x₀ R hHyp t)
      = ct.eval z * ((π_z z root) (ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
  rw [βHensel_eq_mk_C_mul_ξ_pow_of_base_rational hHyp hlc hbase, map_mul, map_pow, π_z_mk,
    Polynomial.evalEval_C]

/-- **The per-`z` coefficient reading of the local series (monic).**  At a base-rational order,
the `t`-th coefficient of `localSeries` at the place `z` is the base polynomial evaluated at
`z`: `coeff t (localSeries hHyp z root hx) = (c t).eval z`.  Cancel the nonzero
`π_z(ξ)^{2t−1}` in the read-off `coeff_localSeries_mul`. -/
theorem coeff_localSeries_eq_eval_of_base_rational {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {t : ℕ} {ct : F[X]}
    (hbase : αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) ct) :
    PowerSeries.coeff t (localSeries hHyp z root hx) = ct.eval z := by
  have h := coeff_localSeries_mul hHyp z root hx t
  rw [π_z_βHensel_of_base_rational hHyp hlc z root hbase] at h
  exact mul_right_cancel₀ (pow_ne_zero _ hx) h

end Reading

/-! ## Part 2 — the transposition identity (pure polynomial algebra) -/

section Transposition

variable {F : Type} [Field F]

/-- **The transposed curve coefficients.**  The `s`-th codeword-polynomial coefficient of the
curve carrying the readings `z ↦ ∑_{t<n} C ((c t).eval z)·X^t`: Taylor-expand each `c t` at the
centre `x₀` and transpose the two indices,
`cᵀ_s := ∑_{t<n} C ((taylor x₀ (c t)).coeff s) · X^t`. -/
noncomputable def transposedCurveCoeffs (x₀ : F) (n : ℕ) (c : ℕ → F[X]) (s : ℕ) : F[X] :=
  ∑ t ∈ Finset.range n, Polynomial.C ((Polynomial.taylor x₀ (c t)).coeff s) * Polynomial.X ^ t

/-- Coefficient extraction for `∑_{t<n} C (g t) · X^t` in `F[X]`:
`coeff j = if j < n then g j else 0`. -/
theorem coeff_sum_C_mul_X_pow (n : ℕ) (g : ℕ → F) (j : ℕ) :
    (∑ t ∈ Finset.range n, Polynomial.C (g t) * Polynomial.X ^ t).coeff j
      = if j < n then g j else 0 := by
  rw [Polynomial.finset_sum_coeff]
  by_cases hj : j < n
  · rw [if_pos hj, Finset.sum_eq_single j
      (fun t _ htj => by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => htj h.symm),
          mul_zero])
      (fun hj' => absurd (Finset.mem_range.mpr hj) hj'),
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · rw [if_neg hj]
    refine Finset.sum_eq_zero fun t ht => ?_
    have htj : j ≠ t := fun h => hj (h ▸ Finset.mem_range.mp ht)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg htj, mul_zero]

/-- **The transposition identity (pure algebra, every `z`).**  The per-`z` reading polynomial
`∑_{t<n} C ((c t).eval z) · X^t` IS the polynomial curve in `z` centred at `x₀` with the
transposed coefficients: `= ∑_{s<N} (z − x₀)^s • transposedCurveCoeffs x₀ n c s`, provided `N`
exceeds every `natDegree (c t)`.  Proof: Taylor-expand `(c t).eval z` at `x₀`
(`taylor_eval` + `eval_eq_sum_range'`) and exchange the two finite sums. -/
theorem sum_C_eval_eq_transposed_curve_sum (x₀ : F) {n N : ℕ} (c : ℕ → F[X])
    (hdeg : ∀ t < n, (c t).natDegree < N) (z : F) :
    (∑ t ∈ Finset.range n, Polynomial.C ((c t).eval z) * Polynomial.X ^ t)
      = ∑ s ∈ Finset.range N, (z - x₀) ^ s • transposedCurveCoeffs x₀ n c s := by
  unfold transposedCurveCoeffs
  rw [show (∑ s ∈ Finset.range N, (z - x₀) ^ s •
        ∑ t ∈ Finset.range n, Polynomial.C ((Polynomial.taylor x₀ (c t)).coeff s)
          * Polynomial.X ^ t)
      = ∑ s ∈ Finset.range N, ∑ t ∈ Finset.range n, (z - x₀) ^ s •
          (Polynomial.C ((Polynomial.taylor x₀ (c t)).coeff s) * Polynomial.X ^ t) from
    Finset.sum_congr rfl fun s _ => Finset.smul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hN : (Polynomial.taylor x₀ (c t)).natDegree < N := by
    rw [Polynomial.natDegree_taylor]
    exact hdeg t (Finset.mem_range.mp ht)
  have heval : (c t).eval z
      = ∑ s ∈ Finset.range N, (Polynomial.taylor x₀ (c t)).coeff s * (z - x₀) ^ s := by
    calc (c t).eval z = (Polynomial.taylor x₀ (c t)).eval (z - x₀) := by
          rw [Polynomial.taylor_eval, sub_add_cancel]
      _ = _ := Polynomial.eval_eq_sum_range' hN _
  rw [heval, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul]
  ring

end Transposition

/-! ## Part 3 — the derived `htrunc` -/

section Htrunc

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The truncated local series in reading form.**  Below `n` the coefficients are the
base-rational readings `(c t).eval z`; on `[n, N)` they vanish (tail vanishing of `αGenuine`
through the monic bridge); so the degree-`< N` truncation is exactly
`∑_{t<n} C ((c t).eval z) · X^t`. -/
theorem trunc_localSeries_of_base_rational {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {n N : ℕ} {c : ℕ → F[X]} (hnN : n ≤ N)
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) (c t))
    (hvanish : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    (PowerSeries.trunc N (localSeries hHyp z root hx) : Polynomial F)
      = ∑ t ∈ Finset.range n, Polynomial.C ((c t).eval z) * Polynomial.X ^ t := by
  ext j
  rw [PowerSeries.coeff_trunc, coeff_sum_C_mul_X_pow]
  by_cases hjn : j < n
  · rw [if_pos (lt_of_lt_of_le hjn hnN), if_pos hjn]
    exact coeff_localSeries_eq_eval_of_base_rational hHyp hlc z root hx (hbase j hjn)
  · rw [if_neg hjn]
    by_cases hjN : j < N
    · rw [if_pos hjN]
      refine coeff_localSeries_eq_zero_of_alphaFromBeta_eq_zero hHyp hξ z root hx j ?_
      rw [BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic x₀ R hHyp hlc j]
      exact hvanish j (le_of_not_gt hjn)
    · rw [if_neg hjN]

/-- **The derived `htrunc` (the exact consumer shape).**  From base-rationality below `n` and
tail vanishing from `n` on, the degree-`< N` truncation of the local series IS the polynomial
curve at the transposed coefficients:
`trunc N (localSeries hHyp z root hx) = ∑_{s<N} (z − x₀)^s • transposedCurveCoeffs x₀ n c s` —
precisely the `htrunc` hypothesis of `curveHenselDatum_of_truncatedLocalRoot` at
`(N, transposedCurveCoeffs x₀ n c)`. -/
theorem htrunc_of_base_rational {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {n N : ℕ} {c : ℕ → F[X]} (hnN : n ≤ N)
    (hdeg : ∀ t < n, (c t).natDegree < N)
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) (c t))
    (hvanish : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    (PowerSeries.trunc N (localSeries hHyp z root hx) : Polynomial F)
      = ∑ s ∈ Finset.range N, (z - x₀) ^ s • transposedCurveCoeffs x₀ n c s := by
  rw [trunc_localSeries_of_base_rational hHyp hξ hlc z root hx hnN hbase hvanish,
    sum_C_eval_eq_transposed_curve_sum x₀ c hdeg z]

end Htrunc

/-! ## Part 4 — the producers with `htrunc` eliminated -/

namespace FaithfulCurveExtraction

section Producers

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **`CurveHenselDatum` from base-rationality (the `htrunc`-free analytic producer).**
The per-`z` base-rational reading is DERIVED: `hbase` (the §5 rational-section content,
`αGenuine t = lift (c t)` below `n`) and the tail vanishing `hvanish` supply the `htrunc` of
`curveHenselDatum_of_truncatedLocalRoot_genuine` at the transposed coefficients
`transposedCurveCoeffs x₀ n c`, with truncation length any `N ≥ n` exceeding every
`natDegree (c t)`.  Remaining inputs: `hbase`, `hvanish`, and the decoded-side GS cargo
`hdvd`/`hcong` — `htrunc` is gone. -/
noncomputable def curveHenselDatum_of_baseRational {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n N : ℕ} {c : ℕ → F[X]} (hnN : n ≤ N) (hdeg : ∀ t < n, (c t).natDegree < N)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) (c t))
    (hvanish : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))))
    (hcong : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (root z))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ N
      (transposedCurveCoeffs x₀ n c) :=
  curveHenselDatum_of_truncatedLocalRoot_genuine (n := N)
    (c := transposedCurveCoeffs x₀ n c) hHyp hξ hlc hR root hx
    (fun t ht => hvanish t (hnN.trans ht))
    (fun z hz => htrunc_of_base_rational hHyp hξ hlc z (root z) (hx z hz) hnN hdeg
      hbase hvanish)
    hdvd hcong

/-- **The faithful `CurveFamilyData` from base-rationality** — the `htrunc`-free composition
into the §5 keystone front doors (`δ_ε_correlatedAgreementCurves` via
`curveFamilyData_of_curveHenselDatum`).  The curve coefficients of the output are the explicit
`transposedCurveCoeffs x₀ n c`. -/
noncomputable def curveFamilyData_of_baseRational {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n N : ℕ} {c : ℕ → F[X]} (hnN : n ≤ N) (hdeg : ∀ t < n, (c t).natDegree < N)
    (hN : N < k + 2)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) (c t))
    (hvanish : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))))
    (hcong : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (root z))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  curveFamilyData_of_curveHenselDatum hN
    (curveHenselDatum_of_baseRational hHyp hξ hlc hR hnN hdeg root hx hbase hvanish hdvd hcong)

end Producers

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.βHensel_eq_mk_C_mul_ξ_pow_of_base_rational
#print axioms ArkLib.π_z_βHensel_of_base_rational
#print axioms ArkLib.coeff_localSeries_eq_eval_of_base_rational
#print axioms ArkLib.transposedCurveCoeffs
#print axioms ArkLib.coeff_sum_C_mul_X_pow
#print axioms ArkLib.sum_C_eval_eq_transposed_curve_sum
#print axioms ArkLib.trunc_localSeries_of_base_rational
#print axioms ArkLib.htrunc_of_base_rational
#print axioms ArkLib.FaithfulCurveExtraction.curveHenselDatum_of_baseRational
#print axioms ArkLib.FaithfulCurveExtraction.curveFamilyData_of_baseRational
