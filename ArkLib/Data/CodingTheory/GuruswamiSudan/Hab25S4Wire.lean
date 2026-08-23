/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.GuruswamiSudan.Hab25SeparableSupply
import ArkLib.Data.CodingTheory.GuruswamiSudan.Hab25FactorWeld

/-!
# S4 Factor Weld Integration

This module wires the output of `Hab25SeparableSupply` into the `hnosq` requirements
of the S6→S8 `Hab25FactorWeld`.
-/

namespace GuruswamiSudan.OverRatFunc

open Polynomial Polynomial.Bivariate

attribute [local instance] Classical.propDecidable

/-- Wiring of the separable specialization hypothesis (`hnosq`) using `Hab25SeparableSupply`. -/
theorem exists_specialized_factor_assignment_charZero {F : Type} [Field F] [CharZero F]
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hd : d ≠ 0) (hQ0 : Q ≠ 0)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hdeg : 0 < Q₀.natDegree) (hdiscr : Q₀.discr ≠ 0) :
    ∃ (rep : (RatFunc F)[X][Y] → (F[X])[X][Y]) (bad : F[X]), bad ≠ 0 ∧
      (∀ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
        ∃ dR : F[X], dR ≠ 0 ∧
          (rep R).map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
            Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) * R ∧
          ∀ z : F, bad.eval z ≠ 0 → dR.eval z ≠ 0) ∧
      (∀ z : F, bad.eval z ≠ 0 → ∀ q : F[X],
        (Polynomial.X - Polynomial.C q) ∣
            Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
          ∃ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
            (Polynomial.X - Polynomial.C q) ∣
              (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) ∧
      (∀ z : F, bad.eval z ≠ 0 →
        ∀ q : F[X], ∀ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
          (Polynomial.X - Polynomial.C q) ∣
              Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
          (Polynomial.X - Polynomial.C q) ∣
              (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
          ∀ R' ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
            (Polynomial.X - Polynomial.C q) ∣
                (rep R').map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
            R = R') := by
  have h_spec := @exists_good_specialization_no_sq_linear F _ Q₀ hdeg hdiscr
  obtain ⟨g, hg_ne_zero, hg_nosq⟩ := h_spec
  obtain ⟨rep, bad', hbad_ne_zero, h1, h2, h3⟩ :=
    exists_specialized_factor_assignment_sep hd hQ0 hrep
  refine ⟨rep, bad' * g, mul_ne_zero hbad_ne_zero hg_ne_zero, ?_, ?_, ?_⟩
  · intro R hR
    obtain ⟨dR, hdR_ne_zero, hrepR, hbad_eval⟩ := h1 R hR
    refine ⟨dR, hdR_ne_zero, hrepR, fun z hz => ?_⟩
    exact hbad_eval z (fun h => hz (by simp [h]))
  · intro z hz q hq
    exact h2 z (fun h => hz (by simp [h])) q hq
  · intro z hz q R hR hqR hrepR R' hR' hrepR'
    have hbad' : bad'.eval z ≠ 0 := fun h => hz (by simp [h])
    have hg : g.eval z ≠ 0 := fun h => hz (by simp [h])
    exact h3 z hbad' (hg_nosq z hg) q R hR R' hR' hrepR hrepR'

end GuruswamiSudan.OverRatFunc
