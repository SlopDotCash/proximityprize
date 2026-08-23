/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Capture
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonDichotomy

/-!
# The improve disjunct from heavy data — the dichotomy's useful branch (#302)

The per-factor production for `Hab25JohnsonDichotomyData.hdichotomy`'s **improve branch**:
on a heavy monic branch, the streams of Claim 5.9 (`gammaGenuine_paperZ_linear`, obtained
from the heavy data WITHOUT passing through the collapse) build the fixed affine pencil;
every captured bad scalar is then `AffineCaptured` (`affineCaptured_of_pencil_proximity`),
and `affineCaptured_improve` yields exactly the disjunct shape

`∃ d₀ d₁, ∀ z ∈ E, ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0`.

Composed with the threshold branch (a `card ≤ T` count — no production needed), this is the
complete per-factor dichotomy: `dichotomy_disjunct_of_heavy_or_light`.

## Main results

* `paperZ_linear_of_heavy_agreement` — the Claim 5.9 streams from the heavy-agreement
  surface (the collapse-free reading of `natDegree_eq_one_of_heavy_agreement`).
* `improve_disjunct_of_heavy` — **the improve branch**, in the verbatim `hdichotomy` shape.
* `dichotomy_disjunct_of_heavy_or_light` — the full per-factor disjunct by cases.

## References

* [BCIKS20] ePrint 2020/654 — §5.2.7–5.2.8.
* [Hab25] ePrint 2025/2110 — Claim 1.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open BCIKS20.Claim59Lagrange
open BCIKS20.Claim510Kill BCIKS20.Claim510Supply BCIKS20.Claim510Agreement
open BCIKS20.Claim510SliceAffine BCIKS20.Claim510Capture
open ProximityPrize.BCIKS20.GammaGenuine
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open _root_.ProximityGap Code
open scoped NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510Improve

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable {x₀ : F} {R : F[X][X][Y]}

/-- **The Claim 5.9 streams from the heavy-agreement surface** — the collapse-free reading:
identical hypothesis surface to `natDegree_eq_one_of_heavy_agreement`, concluding the
ground streams themselves. -/
theorem paperZ_linear_of_heavy_agreement
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F)
    (hagree : ∀ j, ∀ z ∈ matchingSet j, ∃ root : rationalRoot (H_tilde' H) z,
      (∑ t ∈ Finset.range n,
        π_z z root (aPre H x₀ R hHyp hlc t) * (e j) ^ t) = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card) :
    BCIKS20.ZLinearClosureAudit.gammaGenuine_paperZ_linear H x₀ R hHyp := by
  classical
  refine gammaGenuine_paperZ_linear_of_vandermonde_values H hHyp htail e he u₀ u₁ fun j => ?_
  refine coeff_sum_eq_ground_of_large_fin H x₀ R hHyp hlc
    (fun t _ => Claim510Weld.liftIdentity_of_monic H x₀ R hHyp hlc t)
    (e j) (u₀ j) (u₁ j) hD ?_
  refine Claim510Weld.largeness_of_card H x₀ R hHyp (e j) (u₀ j) (u₁ j) (matchingSet j)
    (fun z hz => ?_) (hweight j) (hcard j)
  obtain ⟨root, hroot⟩ := hagree j z hz
  exact mem_S_β_killTarget_of_pin_agree H x₀ R hHyp (e j) (u₀ j) (u₁ j) z root
    (fun t => π_z z root (aPre H x₀ R hHyp hlc t))
    (fun t _ => pi_z_pinning_of_monic H x₀ R hHyp hlc z root t) hroot

/-- **The improve disjunct from heavy data** — the dichotomy's useful branch, in the
verbatim `hdichotomy` shape: a FIXED pair `(d₀, d₁)` such that every bad scalar of the
factor improves agreement at a disagreement coordinate. -/
theorem improve_disjunct_of_heavy
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    -- the heavy-agreement surface (producing the streams)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (v₀ v₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (nodeSet : Fin n → Finset F)
    (hagreeNodes : ∀ j, ∀ z ∈ nodeSet j, ∃ root : rationalRoot (H_tilde' H) z,
      (∑ t ∈ Finset.range n,
        π_z z root (aPre H x₀ R hHyp hlc t) * (e j) ^ t) = v₀ j + z * v₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n (e j) (v₀ j) (v₁ j)) D ≤ (W : WithBot ℕ))
    (hcardNodes : ∀ j, W * H.natDegree < (nodeSet j).card)
    -- the decoded surface (for the pencil identity at the bad scalars)
    {w : F[X][Y]} (hwn : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    -- the RS context and the factor's bad-scalar set with per-scalar capture data
    (domain : ι₀ ↪ F) (k : ℕ) (hnk : n ≤ k) (δ : ℝ≥0)
    (u : Code.WordStack F (Fin 2) ι₀)
    (Efactor : Finset F)
    (hper : ∀ z ∈ Efactor, ∃ root : rationalRoot (H_tilde' H) z,
      (π_z z root) (ξ x₀ R H hHyp) ≠ 0 ∧
      (w.eval (Polynomial.C x₀)).eval z = root.1 ∧
      ∃ S : Finset ι₀, ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι₀) ∧
        (∀ i ∈ S, (w.eval (Polynomial.C (domain i))).eval z = u 0 i + z • u 1 i) ∧
        ¬ _root_.ProximityGap.pairJointAgreesOn
          ((ReedSolomon.code domain k : Set (ι₀ → F))) S (u 0) (u 1)) :
    ∃ d₀ d₁ : ι₀ → F, ∀ z ∈ Efactor,
      ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0 := by
  classical
  -- the streams
  obtain ⟨a, b, hab⟩ := paperZ_linear_of_heavy_agreement hHyp hlc htail e he v₀ v₁ hD
    nodeSet hagreeNodes hweight hcardNodes
  -- the fixed pencil pair and its degree bounds
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hwn
  have hdeg₀ : (affinePencil x₀ a n).natDegree < k :=
    lt_of_lt_of_le (affinePencil_natDegree_lt x₀ a hn) hnk
  have hdeg₁ : (affinePencil x₀ b n).natDegree < k :=
    lt_of_lt_of_le (affinePencil_natDegree_lt x₀ b hn) hnk
  refine ⟨fun i => (affinePencil x₀ a n).eval (domain i) - u 0 i,
          fun i => (affinePencil x₀ b n).eval (domain i) - u 1 i,
          fun z hz => ?_⟩
  obtain ⟨root, hx, hbase, S, hScard, hSagree, hSnoJoint⟩ := hper z hz
  have hcap : AffineCaptured domain k δ u z (affinePencil x₀ a n, affinePencil x₀ b n) :=
    affineCaptured_of_pencil_proximity hHyp hξ hlc hab hwn hdvd hR z root hx hbase
      domain k δ u S hScard hSagree hSnoJoint
  exact affineCaptured_improve hdeg₀ hdeg₁ hcap

/-- **The full per-factor dichotomy disjunct**: a factor is light (`card ≤ T` — counted, no
production) or heavy (carrying the improve data) — the verbatim `hdichotomy` field shape of
`Hab25JohnsonDichotomyData`. -/
theorem dichotomy_disjunct_of_heavy_or_light
    (T : ℕ) (Efactor : Finset F) (d₀ d₁ : ι₀ → F)
    (h : Efactor.card ≤ T ∨ ∀ z ∈ Efactor,
      ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0) :
    Efactor.card ≤ T ∨ ∃ d₀' d₁' : ι₀ → F, ∀ z ∈ Efactor,
      ∃ x ∈ disagreeSet d₀' d₁' , affineGap d₀' d₁' z x = 0 :=
  h.imp id fun himp => ⟨d₀, d₁, himp⟩

end BCIKS20.Claim510Improve

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510Improve.paperZ_linear_of_heavy_agreement
#print axioms BCIKS20.Claim510Improve.improve_disjunct_of_heavy
#print axioms BCIKS20.Claim510Improve.dichotomy_disjunct_of_heavy_or_light
