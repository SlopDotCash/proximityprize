/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.NewtonTailEntry
import ArkLib.ToMathlib.PigeonholeTruncationCapstone

/-!
# Issue #304 — the Newton tail transported to `gammaGenuine`: the hrepT-FREE capstone

`NewtonTailEntry` proved the ab-initio tail for the abstract Newton iteration.  This file
transports it to the genuine object and composes the final, representative-free truncation
capstone:

* `gammaGenuine_eq_newton` — `gammaGenuine` IS the Newton diagonal `HenselSeriesCoeff.γ`
  (Hensel root uniqueness: both root `Q x₀ R H`, both reduce to `α₀` mod `X`, and the
  derivative is a unit there — the unit transported from `isUnit_eval_α₀_derivative_Q₀`
  through `constantCoeff_eval` + `derivative_map` + `PowerSeries.isUnit_iff_constantCoeff`).
* `coeff_Q_eq_zero_of_centre_degree` — the in-tree `Q x₀ R H` has polynomial-coerced
  coefficients: they vanish past the centre-line degree of `R`'s coefficients (Taylor
  preserves degree).
* `alphaGenuine_tail_of_range` — **the ab-initio `αGenuine` tail**: vanishing on the explicit
  finite range `[k, DX + deg_Y R · (k−1)]` closes the entire tail.
* `gammaGenuine_eq_trunc_of_range` — the truncation identity from the explicit finite range
  alone.
* `gammaGenuine_eq_trunc_of_pigeonhole_abInitio` — **THE hrepT-FREE CAPSTONE**: Claim 5.8′
  from the pigeonhole matching data + global GS facts + the numeric chain **at the explicit
  index `T := DX + deg_Y R · (k−1)`** — the representative `(P₀, P₁)` and `hrepT` are GONE
  from the hypothesis list.  The converter then produces `hrepT` *from* this truncation
  (monic `d_H ≤ 2`), completing the corrected-representative story in the right direction.

## References
* [BCIKS20] §5 (Claims 5.8/5.8′, Prop 5.5), Appendix A; the F-series ledger on issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator BCIKS20.HenselNumerator.S5Genuine
open ProximityPrize.BCIKS20.GammaGenuine
open ProximityPrize.HenselSeriesCoeff
open PowerSeries

namespace ArkLib

namespace NewtonTailTransport

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The identification with the Newton diagonal -/

/-- The derivative-unit at the constant approximation, in the power-series ring: transported
from `isUnit_eval_α₀_derivative_Q₀` through the constant-coefficient reading. -/
theorem isUnit_derivative_eval_C_α₀ {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    IsUnit ((ProximityPrize.BCIKS20.GammaGenuine.Q x₀ R H).derivative.eval
      (PowerSeries.C (α₀ H))) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [ProximityPrize.HenselSeriesCoeff.constantCoeff_eval]
  rw [PowerSeries.constantCoeff_C]
  have hcomm : ProximityPrize.HenselSeriesCoeff.Q₀
        ((ProximityPrize.BCIKS20.GammaGenuine.Q x₀ R H).derivative)
      = Polynomial.derivative (ProximityPrize.HenselSeriesCoeff.Q₀
          (ProximityPrize.BCIKS20.GammaGenuine.Q x₀ R H)) := by
    rw [ProximityPrize.HenselSeriesCoeff.Q₀, ProximityPrize.HenselSeriesCoeff.Q₀,
      Polynomial.derivative_map]
  rw [hcomm]
  exact isUnit_eval_α₀_derivative_Q₀ hHyp

/-- **`gammaGenuine` IS the Newton diagonal.**  Both root `Q x₀ R H` and both reduce to `α₀`
mod `X`; Hensel root uniqueness identifies them. -/
theorem gammaGenuine_eq_newton {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    gammaGenuine x₀ R H hHyp
      = ProximityPrize.HenselSeriesCoeff.γ
          (ProximityPrize.BCIKS20.GammaGenuine.Q x₀ R H) (α₀ H) := by
  set QΓ := ProximityPrize.BCIKS20.GammaGenuine.Q x₀ R H with hQΓ
  refine hensel_root_unique QΓ (a₀ := PowerSeries.C (α₀ H)) ?_ ?_ ?_ ?_ ?_
  · -- gammaGenuine roots QΓ
    exact gammaGenuine_root hHyp
  · -- the Newton diagonal roots QΓ
    exact eval_γ_eq_zero QΓ (α₀ H) (eval_α₀_Q₀_eq_zero hHyp)
      (isUnit_eval_α₀_derivative_Q₀ hHyp)
  · -- gammaGenuine ≡ C α₀ mod X
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub,
      gammaGenuine_constantCoeff hHyp, PowerSeries.constantCoeff_C, sub_self]
  · -- the Newton diagonal ≡ C α₀ mod X
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub,
      ProximityPrize.HenselSeriesCoeff.constantCoeff_γ, PowerSeries.constantCoeff_C, sub_self]
  · exact isUnit_derivative_eval_C_α₀ hHyp

/-- The coefficient transport: `αGenuine t` is the Newton diagonal's `t`-th coefficient. -/
theorem alphaGenuine_eq_coeff_newton {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    αGenuine H x₀ R hHyp t
      = PowerSeries.coeff t (ProximityPrize.HenselSeriesCoeff.γ
          (ProximityPrize.BCIKS20.GammaGenuine.Q x₀ R H) (α₀ H)) := by
  have h := congrArg (PowerSeries.coeff t) (gammaGenuine_eq_newton hHyp)
  exact h

/-! ## The degree bound at the in-tree `Q` -/

/-- **The in-tree `Q` is polynomial-coerced**: its coefficients vanish past the centre-line
degree of `R`'s coefficients (Taylor preserves degree). -/
theorem coeff_Q_eq_zero_of_centre_degree {x₀ : F} {R : F[X][X][Y]} {DX : ℕ}
    (hDX : ∀ i, (R.coeff i).natDegree ≤ DX) :
    ∀ i, ∀ a, DX < a →
      coeff a ((ProximityPrize.BCIKS20.GammaGenuine.Q x₀ R H).coeff i) = 0 := by
  intro i a ha
  rw [ProximityPrize.BCIKS20.GammaGenuine.Q, Polynomial.coeff_map, coeff_coeffHom]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt, map_zero]
  rw [Polynomial.natDegree_taylor]
  exact lt_of_le_of_lt (hDX i) ha

/-! ## The ab-initio `αGenuine` tail and the truncation identity -/

/-- **The ab-initio `αGenuine` tail.**  Vanishing on the explicit finite range
`[k, DX + deg_Y R · (k−1)]` closes the entire tail — no representative input. -/
theorem alphaGenuine_tail_of_range {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) {DX k : ℕ} (hk : 0 < k)
    (hDX : ∀ i, (R.coeff i).natDegree ≤ DX)
    (hrange : ∀ s, k ≤ s → s ≤ DX + R.natDegree * (k - 1) →
      αGenuine H x₀ R hHyp s = 0) :
    ∀ t, k ≤ t → αGenuine H x₀ R hHyp t = 0 := by
  set QΓ := ProximityPrize.BCIKS20.GammaGenuine.Q x₀ R H with hQΓ
  -- the Newton-side range, at the (possibly smaller) honest index of QΓ
  have hQdeg : QΓ.natDegree ≤ R.natDegree := Polynomial.natDegree_map_le
  have hrange' : ∀ s, k ≤ s → s ≤ DX + QΓ.natDegree * (k - 1) →
      PowerSeries.coeff s (ProximityPrize.HenselSeriesCoeff.γ QΓ (α₀ H)) = 0 := by
    intro s hks hsT
    rw [← alphaGenuine_eq_coeff_newton hHyp]
    refine hrange s hks (le_trans hsT ?_)
    have : QΓ.natDegree * (k - 1) ≤ R.natDegree * (k - 1) :=
      Nat.mul_le_mul_right _ hQdeg
    omega
  intro t hkt
  rw [alphaGenuine_eq_coeff_newton hHyp]
  exact ProximityPrize.HenselSeriesCoeff.tail_of_range_vanish_of_polyQ QΓ (α₀ H)
    (eval_α₀_Q₀_eq_zero hHyp) (isUnit_eval_α₀_derivative_Q₀ hHyp) hk
    (coeff_Q_eq_zero_of_centre_degree hDX) hrange' t hkt

/-- **The truncation identity from the explicit finite range alone** — representative-free
Claim 5.8′. -/
theorem gammaGenuine_eq_trunc_of_range {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) {DX k : ℕ} (hk : 0 < k)
    (hDX : ∀ i, (R.coeff i).natDegree ≤ DX)
    (hrange : ∀ s, k ≤ s → s ≤ DX + R.natDegree * (k - 1) →
      αGenuine H x₀ R hHyp s = 0) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) := by
  have htail : ∀ t, k ≤ t → αGenuine H x₀ R hHyp t = 0 :=
    alphaGenuine_tail_of_range hHyp hk hDX hrange
  ext t
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases ht : t < k
  · rw [if_pos ht]
  · rw [if_neg ht]
    have hcoeff : PowerSeries.coeff t (gammaGenuine x₀ R H hHyp)
        = αGenuine H x₀ R hHyp t := rfl
    rw [hcoeff, htail t (not_lt.mp ht)]

/-! ## THE hrepT-FREE CAPSTONE -/

section Capstone

variable [Fintype F] [DecidableEq F]

/-- **THE hrepT-FREE CAPSTONE: Claim 5.8′ with no representative input.**
`gammaGenuine = trunc k gammaGenuine` from the pigeonhole matching data + global GS facts +
the numeric chain at the explicit index `T := DX + deg_Y R · (k−1)`.  The corrected
representative `(P₀, P₁)`/`hrepT` is gone: the tail is ab initio (`NewtonTailEntry`), and the
converter recovers `hrepT` *from* this truncation afterwards. -/
theorem gammaGenuine_eq_trunc_of_pigeonhole_abInitio {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ClaimA2.ξ x₀ R H hHyp ≠ 0)
    {D DX k : ℕ} (hk : 0 < k) (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDX : ∀ i, (R.coeff i).natDegree ≤ DX)
    {matchingSet : Finset F} {Pz : F → F[X]}
    (hinc : ∀ z ∈ matchingSet, Polynomial.evalEval z ((Pz z).eval x₀) H = 0)
    (hdvd : ∀ z ∈ matchingSet, Polynomial.X - Polynomial.C (Pz z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (BranchValuePigeonhole.incidenceRootFn (H := H) (hinc z hz)))
        (ClaimA2.ξ x₀ R H hHyp) ≠ 0)
    (hR : R.Separable)
    {n : ℕ}
    (hbudget : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (DX + R.natDegree * (k - 1)) < n)
    (hcard : n ≤ matchingSet.card) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) := by
  -- the §5 largeness on the explicit range, from the pigeonhole + the direct counting
  have hlarge := PigeonholeTruncationCapstone.SβLargeAtFin_of_card H hHyp hD hH hmonic hd2
    hdHD hD_Rx0 hRgrade
    (PigeonholeTruncationCapstone.hvanish_of_pigeonhole H hHyp hξ hmonic.leadingCoeff
      hinc hdvd hdeg hx hR (DX + R.natDegree * (k - 1)))
    hbudget hcard
  -- per-index αGenuine vanishing on the range (monic Claim 5.8)
  have hrange : ∀ s, k ≤ s → s ≤ DX + R.natDegree * (k - 1) →
      αGenuine H x₀ R hHyp s = 0 := fun s hks hsT =>
    claim58_genuine_of_monic H hHyp hmonic.leadingCoeff (hlarge s hks hsT)
  -- the ab-initio tail + the truncation
  exact gammaGenuine_eq_trunc_of_range hHyp hk hDX hrange

end Capstone

end NewtonTailTransport

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.NewtonTailTransport.isUnit_derivative_eval_C_α₀
#print axioms ArkLib.NewtonTailTransport.gammaGenuine_eq_newton
#print axioms ArkLib.NewtonTailTransport.alphaGenuine_eq_coeff_newton
#print axioms ArkLib.NewtonTailTransport.coeff_Q_eq_zero_of_centre_degree
#print axioms ArkLib.NewtonTailTransport.alphaGenuine_tail_of_range
#print axioms ArkLib.NewtonTailTransport.gammaGenuine_eq_trunc_of_range
#print axioms ArkLib.NewtonTailTransport.gammaGenuine_eq_trunc_of_pigeonhole_abInitio
