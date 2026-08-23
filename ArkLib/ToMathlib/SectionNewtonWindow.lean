/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionNewtonPlaceReading
import ArkLib.ToMathlib.SectionNewtonGamma

/-!
# The Claim-5.8 window from decoded roots (#304 — the full middle-window discharge)

The composition closing the [BCIKS20] Claim-5.8 **middle window** on the section-Newton
route, from per-place decoded data only:

* `specializedGamma_eq_of_root` — **per-place Hensel uniqueness**: any power-series root of
  the specialized data sharing the seed *is* the specialized Newton root
  (`root_unique_seriesCoeff`; the unit response at the place is the `φ`-image of the
  localized response, by functoriality — no separability anywhere).
* `coeff_specializedGamma_eq_zero_of_poly_root` — on the matching set the specialized root
  is the (coerced) **decoded polynomial** of degree `< k`, so its coefficients die from `k`
  on.
* `window_vanish_of_decoded_roots` — **THE WINDOW**: per-place decoded roots on a matching
  set larger than the cleared budget ⟹ the localized Newton coefficient vanishes at every
  order `t ≥ k` up to the budgeted horizon — i.e. the [BCIKS20] Claim 5.8 middle window,
  discharged by counting against the explicit `clearedBudget`.

The remaining inputs are GS-construction data only: the per-place root facts (the
S10-converse divisibility, read at the recentred coercion), the seed agreement
`(P z).eval x₀ = v(z)` (the §6 incidence), the response identification, and the count.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8), Appendix A.
-/

set_option linter.style.longLine false

namespace ArkLib.SectionNewtonCleared

open PowerSeries ProximityPrize.HenselSeriesCoeff ArkLib.SectionNewtonGamma

variable {F : Type*} [Field F] (ξ : Polynomial F)

local notation "𝔞" => algebraMap (Polynomial F) (Localization.Away ξ)

variable (QA : Polynomial (PowerSeries (Localization.Away ξ))) (v : Polynomial F)

/-! ## Per-place Hensel uniqueness against the specialized Newton root -/

/-- The specialized derivative response is the evaluated `ξ̄` — functoriality of the
response. -/
theorem specialized_response_eq {z : F} (hz : ξ.eval z ≠ 0)
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ) :
    Polynomial.eval (v.eval z)
        (Polynomial.derivative (Q₀ (QA.map (PowerSeries.map (placeMap ξ hz)))))
      = ξ.eval z := by
  have h := eval_derivative_Q₀_map (placeMap ξ hz) QA (𝔞 v)
  rw [placeMap_algebraMap ξ hz v] at h
  rw [h, hresp, placeMap_algebraMap ξ hz ξ]

/-- **Per-place Hensel uniqueness**: any root of the specialized data sharing the seed `v(z)`
is the specialized Newton root.  No separability — only the per-place response
nonvanishing. -/
theorem specializedGamma_eq_of_root {z : F} (hz : ξ.eval z ≠ 0)
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ)
    {γ' : PowerSeries F}
    (hroot : Polynomial.eval γ' (QA.map (PowerSeries.map (placeMap ξ hz))) = 0)
    (hseed : constantCoeff γ' = v.eval z) :
    specializedGamma ξ QA v hz = γ' := by
  have hu : IsUnit (Polynomial.eval (v.eval z)
      (Polynomial.derivative (Q₀ (QA.map (PowerSeries.map (placeMap ξ hz)))))) := by
    rw [specialized_response_eq ξ QA v hz hresp]
    exact isUnit_iff_ne_zero.mpr hz
  -- the seed root fact for the specialized data, read off the given root
  have hc0 : Polynomial.eval (v.eval z) (Q₀ (QA.map (PowerSeries.map (placeMap ξ hz))))
      = 0 := by
    have h := congrArg constantCoeff hroot
    rw [constantCoeff_eval, hseed, map_zero] at h
    exact h
  show γ (QA.map (PowerSeries.map (placeMap ξ hz))) (v.eval z) = γ'
  have hccγ : constantCoeff (γ (QA.map (PowerSeries.map (placeMap ξ hz))) (v.eval z))
      = constantCoeff γ' := by
    rw [constantCoeff_γ, hseed]
  have huγ : IsUnit (Polynomial.eval
      (constantCoeff (γ (QA.map (PowerSeries.map (placeMap ξ hz))) (v.eval z)))
      (Polynomial.derivative (Q₀ (QA.map (PowerSeries.map (placeMap ξ hz)))))) := by
    rw [constantCoeff_γ]
    exact hu
  exact root_unique_seriesCoeff hccγ huγ (isRoot_gamma _ _ hc0 hu) hroot

/-- On the matching set the specialized root is the **coerced decoded polynomial**: its
coefficients die from the decoded degree bound on. -/
theorem coeff_specializedGamma_eq_zero_of_poly_root {z : F} (hz : ξ.eval z ≠ 0)
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ)
    {p : Polynomial F} {k : ℕ} (hdeg : p.natDegree < k)
    (hroot : Polynomial.eval (p : PowerSeries F)
      (QA.map (PowerSeries.map (placeMap ξ hz))) = 0)
    (hseed : Polynomial.constantCoeff p = v.eval z)
    {t : ℕ} (ht : k ≤ t) :
    coeff t (specializedGamma ξ QA v hz) = 0 := by
  have hseed' : constantCoeff (p : PowerSeries F) = v.eval z := by
    rw [← hseed]
    exact Polynomial.constantCoeff_coe p
  rw [specializedGamma_eq_of_root ξ QA v hz hresp hroot hseed']
  rw [Polynomial.coeff_coe]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-! ## THE WINDOW -/

/-- **THE CLAIM-5.8 MIDDLE WINDOW, END TO END**: per-place decoded roots (degree `< k`,
correct seed) on a matching set exceeding the cleared budget (plus the counted `ξ̄`-root
excess) kill every localized Newton coefficient of order `≥ k` within the horizon. -/
theorem window_vanish_of_decoded_roots {DZ : ℕ} (hξ0 : ξ ≠ 0)
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ)
    {k T : ℕ} (M : Finset F)
    (hcard : clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree T + ξ.natDegree
      < M.card)
    (P : F → Polynomial F)
    (hdeg : ∀ z ∈ M, (P z).natDegree < k)
    (hroot : ∀ z, ∀ (_ : z ∈ M) (hzξ : ξ.eval z ≠ 0),
      Polynomial.eval ((P z : Polynomial F) : PowerSeries F)
        (QA.map (PowerSeries.map (placeMap ξ hzξ))) = 0)
    (hseed : ∀ z ∈ M, Polynomial.constantCoeff (P z) = v.eval z) :
    ∀ t, k ≤ t → t ≤ T → coeff t (γ QA (𝔞 v)) = 0 := by
  intro t htk htT
  refine coeff_gamma_eq_zero_of_specialized_vanish_sdiff ξ QA v hξ0 hQdeg hresp t M ?_ ?_
  · calc clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t + ξ.natDegree
        ≤ clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree T + ξ.natDegree :=
          Nat.add_le_add_right
            (clearedBudget_mono QA.natDegree v.natDegree DZ ξ.natDegree htT) _
      _ < M.card := hcard
  · intro z hz hzξ
    exact coeff_specializedGamma_eq_zero_of_poly_root ξ QA v hzξ hresp
      (hdeg z hz) (hroot z hz hzξ) (hseed z hz) htk

end ArkLib.SectionNewtonCleared

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonCleared.specialized_response_eq
#print axioms ArkLib.SectionNewtonCleared.specializedGamma_eq_of_root
#print axioms ArkLib.SectionNewtonCleared.coeff_specializedGamma_eq_zero_of_poly_root
#print axioms ArkLib.SectionNewtonCleared.window_vanish_of_decoded_roots
