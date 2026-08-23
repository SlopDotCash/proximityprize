/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionNewtonWindow
import ArkLib.ToMathlib.SectionNewtonClearedSharp

/-!
# The sharp Claim-5.8 window (#304 — the F15-repaired middle window)

`SectionNewtonWindow.window_vanish_of_decoded_roots` at the **quadratic** budget of the F15
repair: the matching count threshold drops from the exponential `clearedBudget` to
`sharpBudget … T + deg ξ̄` — polynomial in the GS parameters, satisfiable at
`|F| ≳ poly(n)`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8), Appendix A.
-/

set_option linter.style.longLine false

namespace ArkLib.SectionNewtonCleared

open PowerSeries ProximityPrize.HenselSeriesCoeff

variable {F : Type*} [Field F] (ξ : Polynomial F)

local notation "𝔞" => algebraMap (Polynomial F) (Localization.Away ξ)

variable (QA : Polynomial (PowerSeries (Localization.Away ξ))) (v : Polynomial F)

/-- The sharp specialized-vanish window exit. -/
theorem coeff_gamma_eq_zero_of_specialized_vanish_sharp {DZ : ℕ}
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ)
    (t : ℕ) (M : Finset F)
    (hcard : sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree t < M.card)
    (hMξ : ∀ z ∈ M, ξ.eval z ≠ 0)
    (hvanish : ∀ z, ∀ hz : z ∈ M,
      coeff t (specializedGamma ξ QA v (hMξ z hz)) = 0) :
    coeff t (γ QA (𝔞 v)) = 0 := by
  have hu : IsUnit (Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA))) := by
    rw [hresp]
    exact isUnit_xi ξ
  refine coeff_gamma_eq_zero_of_eval_vanish_sharp ξ QA v hQdeg hresp t M hcard ?_
  intro N _ hmap z hz
  rw [numerator_eval_eq ξ QA v (hMξ z hz) hu hmap, hvanish z hz, mul_zero]

/-- The sharp window exit with the counted `ξ̄`-root excess built in. -/
theorem coeff_gamma_eq_zero_of_specialized_vanish_sdiff_sharp {DZ : ℕ} (hξ0 : ξ ≠ 0)
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ)
    (t : ℕ) (M : Finset F)
    (hcard : sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree t + ξ.natDegree
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
  have hMgcard : sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree t < Mg.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := M) (p := fun z => ξ.eval z = 0)
    rw [hMg]
    omega
  exact coeff_gamma_eq_zero_of_specialized_vanish_sharp ξ QA v hQdeg hresp t Mg hMgcard
    hMgsub (fun z hz => hvanish z (Finset.mem_filter.mp hz).1 (hMgsub z hz))

/-- **THE SHARP CLAIM-5.8 MIDDLE WINDOW**: per-place decoded roots on a matching set
exceeding the *quadratic* budget kill every localized Newton coefficient of order `≥ k`
within the horizon. -/
theorem window_vanish_of_decoded_roots_sharp {DZ : ℕ} (hξ0 : ξ ≠ 0)
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ)
    {k T : ℕ} (M : Finset F)
    (hcard : sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree T + ξ.natDegree
      < M.card)
    (P : F → Polynomial F)
    (hdeg : ∀ z ∈ M, (P z).natDegree < k)
    (hroot : ∀ z, ∀ (_ : z ∈ M) (hzξ : ξ.eval z ≠ 0),
      Polynomial.eval ((P z : Polynomial F) : PowerSeries F)
        (QA.map (PowerSeries.map (placeMap ξ hzξ))) = 0)
    (hseed : ∀ z ∈ M, Polynomial.constantCoeff (P z) = v.eval z) :
    ∀ t, k ≤ t → t ≤ T → coeff t (γ QA (𝔞 v)) = 0 := by
  intro t htk htT
  refine coeff_gamma_eq_zero_of_specialized_vanish_sdiff_sharp ξ QA v hξ0 hQdeg hresp t M
    ?_ ?_
  · calc sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree t + ξ.natDegree
        ≤ sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree T + ξ.natDegree :=
          Nat.add_le_add_right
            (sharpBudget_mono QA.natDegree v.natDegree DZ ξ.natDegree htT) _
      _ < M.card := hcard
  · intro z hz hzξ
    exact coeff_specializedGamma_eq_zero_of_poly_root ξ QA v hzξ hresp
      (hdeg z hz) (hroot z hz hzξ) (hseed z hz) htk

end ArkLib.SectionNewtonCleared

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonCleared.coeff_gamma_eq_zero_of_specialized_vanish_sharp
#print axioms ArkLib.SectionNewtonCleared.coeff_gamma_eq_zero_of_specialized_vanish_sdiff_sharp
#print axioms ArkLib.SectionNewtonCleared.window_vanish_of_decoded_roots_sharp
