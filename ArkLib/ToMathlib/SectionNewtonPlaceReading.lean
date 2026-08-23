/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionNewtonCleared
import ArkLib.ToMathlib.SectionNewtonFunctorial

/-!
# Per-place readings of the cleared Newton filtration (#304)

The composition of the cleared filtration (`SectionNewtonCleared`) with the transport
unifier (`SectionNewtonFunctorial`) at the per-place evaluation maps:

* `placeMap` — the evaluation `Localization.Away ξ̄ →+* F` at a place `z` with
  `ξ̄(z) ≠ 0` (`Localization.awayLift` of `Polynomial.evalRingHom`);
* `numerator_eval_eq` — **the per-place reading of the `Cleared` identity**: the explicit
  numerator evaluates at `z` to `ξ̄(z)^(2t−1) ·` (the `t`-th coefficient of the **specialized**
  Newton root) — the multiplied-out per-place `(A.4)` identity (`coeff_localSeries_mul` of the
  legacy lane), now a one-line consequence of functoriality;
* `coeff_gamma_eq_zero_of_specialized_vanish` — **THE WINDOW EXIT**: if the specialized Newton
  coefficient vanishes at more places than the cleared budget (per-place Hensel uniqueness
  supplies this on the matching set: the specialized root *is* the decoded Taylor series,
  truncated below `k`), the localized Newton coefficient vanishes — the [BCIKS20] Claim 5.8
  middle window, end to end, by ordinary root counting.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8), Appendix A.
-/

set_option linter.style.longLine false

namespace ArkLib.SectionNewtonCleared

open PowerSeries ProximityPrize.HenselSeriesCoeff

variable {F : Type*} [Field F] (ξ : Polynomial F)

local notation "𝔞" => algebraMap (Polynomial F) (Localization.Away ξ)

/-! ## The place maps -/

/-- The per-place evaluation `Localization.Away ξ̄ →+* F` at a place with nonvanishing
response. -/
noncomputable def placeMap {z : F} (hz : ξ.eval z ≠ 0) :
    Localization.Away ξ →+* F :=
  Localization.awayLift (Polynomial.evalRingHom z) ξ
    (by simpa using (isUnit_iff_ne_zero.mpr hz))

/-- The place map restricts to evaluation on the base polynomials. -/
@[simp]
theorem placeMap_algebraMap {z : F} (hz : ξ.eval z ≠ 0) (q : Polynomial F) :
    placeMap ξ hz (𝔞 q) = q.eval z :=
  IsLocalization.lift_eq _ q

/-! ## The specialized Newton data -/

variable (QA : Polynomial (PowerSeries (Localization.Away ξ))) (v : Polynomial F)

/-- The specialized Newton root at a place: the same iteration over `F`, with the
place-mapped data and the evaluated seed. -/
noncomputable def specializedGamma {z : F} (hz : ξ.eval z ≠ 0) : PowerSeries F :=
  γ (QA.map (PowerSeries.map (placeMap ξ hz))) (v.eval z)

/-- Functoriality at the place map: the specialized root is the place image of the
localized root. -/
theorem placeMap_gamma {z : F} (hz : ξ.eval z ≠ 0)
    (hu : IsUnit (Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)))) (t : ℕ) :
    placeMap ξ hz (coeff t (γ QA (𝔞 v)))
      = coeff t (specializedGamma ξ QA v hz) := by
  have h := coeff_map_γ (placeMap ξ hz) QA (𝔞 v) hu t
  rw [placeMap_algebraMap ξ hz v] at h
  exact h

/-! ## The per-place reading of the cleared identity -/

/-- **The per-place reading**: the explicit numerator evaluates at each good place to
`ξ̄(z)^(2t−1)` times the specialized Newton coefficient — the multiplied-out per-place
`(A.4)` identity, from functoriality alone. -/
theorem numerator_eval_eq {z : F} (hz : ξ.eval z ≠ 0)
    (hu : IsUnit (Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA))))
    {t : ℕ} {N : Polynomial F}
    (hmap : 𝔞 N = (𝔞 ξ) ^ (2 * t - 1) * coeff t (γ QA (𝔞 v))) :
    N.eval z = (ξ.eval z) ^ (2 * t - 1) * coeff t (specializedGamma ξ QA v hz) := by
  have h := congrArg (placeMap ξ hz) hmap
  rw [placeMap_algebraMap ξ hz N, map_mul, map_pow, placeMap_algebraMap ξ hz ξ,
    placeMap_gamma ξ QA v hz hu t] at h
  exact h

/-! ## The window exit -/

/-- **THE WINDOW EXIT** ([BCIKS20] Claim 5.8 middle window, end to end): if the specialized
Newton coefficient vanishes at more places (with nonvanishing response) than the cleared
budget, the localized Newton coefficient vanishes.  Per-place Hensel uniqueness supplies the
specialized vanishing on the matching set: there the specialized root IS the decoded Taylor
series, whose coefficients die from `k` on. -/
theorem coeff_gamma_eq_zero_of_specialized_vanish {DZ : ℕ}
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ)
    (t : ℕ) (M : Finset F)
    (hcard : clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t < M.card)
    (hMξ : ∀ z ∈ M, ξ.eval z ≠ 0)
    (hvanish : ∀ z, ∀ hz : z ∈ M,
      coeff t (specializedGamma ξ QA v (hMξ z hz)) = 0) :
    coeff t (γ QA (𝔞 v)) = 0 := by
  have hu : IsUnit (Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA))) := by
    rw [hresp]
    exact isUnit_xi ξ
  refine coeff_gamma_eq_zero_of_eval_vanish ξ QA v hQdeg hresp t M hcard ?_
  intro N _ hmap z hz
  rw [numerator_eval_eq ξ QA v (hMξ z hz) hu hmap, hvanish z hz, mul_zero]

/-- **The boundary-counted form**: vanishing on a matching set minus the (counted) response
roots.  `M` need not avoid the `ξ̄`-roots a priori — the bad places are subtracted and the
budget strengthened by `ξ̄.natDegree`, packaging the standard exceptional-set bookkeeping. -/
theorem coeff_gamma_eq_zero_of_specialized_vanish_sdiff {DZ : ℕ} (hξ0 : ξ ≠ 0)
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ)
    (t : ℕ) (M : Finset F)
    (hcard : clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t + ξ.natDegree
      < M.card)
    (hvanish : ∀ z, ∀ (hz : z ∈ M) (hzξ : ξ.eval z ≠ 0),
      coeff t (specializedGamma ξ QA v hzξ) = 0) :
    coeff t (γ QA (𝔞 v)) = 0 := by
  classical
  set Mg : Finset F := M.filter (fun z => ¬ ξ.eval z = 0) with hMg
  have hMgsub : ∀ z ∈ Mg, ξ.eval z ≠ 0 := fun z hz => (Finset.mem_filter.mp hz).2
  have hbadcard : (M.filter (fun z => ξ.eval z = 0)).card ≤ ξ.natDegree := by
    have hsub : M.filter (fun z => ξ.eval z = 0) ⊆ ξ.roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hξ0]
      exact (Finset.mem_filter.mp hz).2
    calc (M.filter (fun z => ξ.eval z = 0)).card
        ≤ ξ.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card ξ.roots := ξ.roots.toFinset_card_le
      _ ≤ ξ.natDegree := ξ.card_roots'
  have hMgcard : clearedBudget QA.natDegree v.natDegree DZ ξ.natDegree t < Mg.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := M) (p := fun z => ξ.eval z = 0)
    rw [hMg]
    omega
  exact coeff_gamma_eq_zero_of_specialized_vanish ξ QA v hQdeg hresp t Mg hMgcard hMgsub
    (fun z hz => hvanish z (Finset.mem_filter.mp hz).1 (hMgsub z hz))

end ArkLib.SectionNewtonCleared

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonCleared.placeMap_algebraMap
#print axioms ArkLib.SectionNewtonCleared.placeMap_gamma
#print axioms ArkLib.SectionNewtonCleared.numerator_eval_eq
#print axioms ArkLib.SectionNewtonCleared.coeff_gamma_eq_zero_of_specialized_vanish
#print axioms ArkLib.SectionNewtonCleared.coeff_gamma_eq_zero_of_specialized_vanish_sdiff
