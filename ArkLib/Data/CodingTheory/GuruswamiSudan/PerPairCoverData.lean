/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.MCAEventDecodedBridge
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorAssignment

/-!
# The per-pair cover data — every bad scalar claimed by a factor or the content index (#302)

The second half of the `PerPairFactorData.hcover` production: layering the per-`z` factor
assignment (`exists_specialized_factor_assignment`, PROVEN) on the `mcaEvent → GS` bridge
(`mcaEvent_decoded_data`), with the **content-term avoidance** ([BCHKS25] footnote 5): a
nonzero avoidance polynomial `badAll` such that every `mcaEvent`-bad scalar `γ` either

* satisfies `badAll γ ≠ 0` and its decoded codeword is claimed by SOME irreducible factor
  of the generic interpolant (the factor's `Efactor` membership, carrying the capture
  data); or
* is a root of `badAll` (the junk/content index — at most `natDegree badAll` scalars,
  counted by the dichotomy's `T`-branch).

## Main results

* `exists_perPair_cover_data` — **the cover data**: the assignment + the avoidance
  polynomial + the per-scalar dichotomized claim.

## References

* [BCIKS20] ePrint 2020/654 §5; [BCHKS25] ePrint 2025/2055 (footnote 5);
  [Hab25] ePrint 2025/2110.
-/

open Polynomial Polynomial.Bivariate
open _root_.ProximityGap
open scoped NNReal

set_option linter.unusedSectionVars false

namespace GuruswamiSudan.OverRatFunc

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

/-- A nonzero bivariate integer representative has a nonzero `F[Z]`-coefficient whose
nonvanishing at `z` forces the specialization nonzero. -/
theorem exists_specialization_guard {Q₀ : (F[X])[X][Y]} (h : Q₀ ≠ 0) :
    ∃ c : F[X], c ≠ 0 ∧ ∀ z : F, c.eval z ≠ 0 →
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0 := by
  -- pick a nonzero inner coefficient (the leading coefficients)
  have hj : Q₀.coeff Q₀.natDegree ≠ 0 :=
    show Q₀.leadingCoeff ≠ 0 from Polynomial.leadingCoeff_ne_zero.mpr h
  set j := Q₀.natDegree
  have hi : (Q₀.coeff j).coeff (Q₀.coeff j).natDegree ≠ 0 :=
    show (Q₀.coeff j).leadingCoeff ≠ 0 from Polynomial.leadingCoeff_ne_zero.mpr hj
  set i := (Q₀.coeff j).natDegree
  refine ⟨(Q₀.coeff j).coeff i, hi, fun z hz hmap => ?_⟩
  have h1 : (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).coeff j = 0 := by
    rw [hmap]; rfl
  rw [Polynomial.coeff_map] at h1
  have h2 : ((Q₀.coeff j).map (Polynomial.evalRingHom z)).coeff i = 0 := by
    rw [show (Polynomial.mapRingHom (Polynomial.evalRingHom z)) (Q₀.coeff j)
        = (Q₀.coeff j).map (Polynomial.evalRingHom z) from rfl] at h1
    rw [h1, Polynomial.coeff_zero]
  rw [Polynomial.coeff_map] at h2
  exact hz h2

/-- **The per-pair cover data.**  The factor assignment + the avoidance polynomial: every
`mcaEvent`-bad scalar `γ` with `badAll γ ≠ 0` has its decoded codeword claimed by some
irreducible factor of `Q` (with the capture-shaped witness data); the `badAll`-roots are
the content/junk index, at most `natDegree badAll` many. -/
theorem exists_perPair_cover_data {n k m : ℕ}
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain ωs) (genericFold f₀ f₁) Q)
    (hd : d ≠ 0) (hQ0 : Q ≠ 0) (hQ₀ : Q₀ ≠ 0)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hk : k + 1 ≤ n) (hm : 1 ≤ m) (hn : 0 < n)
    (δ : ℝ≥0) (hδ1 : δ < 1) (hδj : (δ : ℝ) < gs_johnson k n m) :
    ∃ (rep : (RatFunc F)[X][Y] → (F[X])[X][Y]) (badAll : F[X]), badAll ≠ 0 ∧
      ∀ γ : F, mcaEvent (ReedSolomon.code ωs k : Set (Fin n → F)) δ f₀ f₁ γ →
        badAll.eval γ ≠ 0 →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
          ∃ p : ReedSolomon.code ωs k,
            (Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p)) ∣
              (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ∧
            ∃ S : Finset (Fin n),
              ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n)) ∧
              (∀ i ∈ S, (ReedSolomon.codewordToPoly p).eval (ωs i)
                = f₀ i + γ * f₁ i) ∧
              ¬ pairJointAgreesOn
                (ReedSolomon.code ωs k : Set (Fin n → F)) S f₀ f₁ := by
  classical
  obtain ⟨rep, bad, hbad0, _hreps, hassign⟩ :=
    exists_specialized_factor_assignment hd hQ0 hrep
  obtain ⟨c, hc0, hguard⟩ := exists_specialization_guard hQ₀
  refine ⟨rep, bad * c, mul_ne_zero hbad0 hc0, fun γ hev hγ => ?_⟩
  have hbadγ : bad.eval γ ≠ 0 := fun h => hγ (by rw [Polynomial.eval_mul, h, zero_mul])
  have hcγ : c.eval γ ≠ 0 := fun h => hγ (by rw [Polynomial.eval_mul, h, mul_zero])
  have hγQ : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 :=
    hguard γ hcγ
  obtain ⟨p, hroot, S, hScard, hSagree, hnj⟩ :=
    mcaEvent_decoded_data ωs f₀ f₁ hQ hrep γ hγQ hk hm hn δ hδ1 hδj hev
  have hdvd : (Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p)) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) :=
    Polynomial.dvd_iff_isRoot.mpr hroot
  obtain ⟨R, hR, hclaim⟩ := hassign γ hbadγ (ReedSolomon.codewordToPoly p) hdvd
  exact ⟨R, hR, p, hclaim, S, hScard, hSagree, hnj⟩

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit -/
#print axioms GuruswamiSudan.OverRatFunc.exists_specialization_guard
#print axioms GuruswamiSudan.OverRatFunc.exists_perPair_cover_data
