/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge

/-!
# Rate-quarter half predecessor: the far-direction branch

At `n=2h`, threshold `h+1`, and `2k<=h`, the ordinary Johnson denominator becomes

```text
(h+1)^2 - (2h)k >= 2h+1.
```

Consequently any selected rich-point family whose distinct agreement sets meet in at most
`k` coordinates has strictly fewer than `2h` points.  For the MCA family this pair cap follows
whenever the received direction row agrees with every degree-`<k` polynomial on at most `k`
coordinates: the intersection of two selected agreements is contained in the root set of their
slope polynomial.

This closes the generic/far direction at rate `1/4`.  Hence a hypothetical sharp counterexample
must have an exceptional direction polynomial with at least `k+1` agreement coordinates, exactly
the large-core branch isolated by the recursive analysis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFarDirection

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The received direction has no exceptional degree-`<k` agreement core. -/
def DirectionAgreementCap (dom : ι ↪ F) (u1 : ι → F) (k : ℕ) : Prop :=
  ∀ r : F[X], r.natDegree < k →
    (Finset.univ.filter fun i => r.eval (dom i) = u1 i).card ≤ k

/-- The exact Johnson arithmetic at the rate-quarter boundary. -/
theorem card_lt_two_mul_of_pair_inter_le
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hh : 1 ≤ h) (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h)
    (hpair : ∀ gamma ∈ family.G, ∀ beta ∈ family.G, gamma ≠ beta →
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
        fullAgreement dom (u 0) (u 1) beta (family.q beta)).card ≤ k) :
    family.G.card < 2 * h := by
  by_cases hG : family.G = ∅
  · simp only [hG, Finset.card_empty]
    omega
  let κ := {gamma // gamma ∈ family.G}
  let S : κ → Finset ι := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1)
  letI : Nonempty κ := by
    obtain ⟨gamma, hgamma⟩ := Finset.nonempty_iff_ne_empty.mpr hG
    exact ⟨⟨gamma, hgamma⟩⟩
  have hlo : ∀ gamma : κ, h + 1 ≤ (S gamma).card := by
    intro gamma
    rw [← hthreshold]
    exact family.threshold_le gamma.1 gamma.2
  have hpair' : ∀ gamma beta : κ, gamma ≠ beta →
      (S gamma ∩ S beta).card ≤ k := by
    intro gamma beta hne
    apply hpair gamma.1 gamma.2 beta.1 beta.2
    intro hval
    apply hne
    exact Subtype.ext hval
  have hgap : Fintype.card ι * k ≤ (h + 1) ^ 2 := by
    rw [hn]
    have hmul := Nat.mul_le_mul_left h hrate
    nlinarith
  have hjohnson := ArkLib.Coverage.card_mul_sub_le_of_agreement
    S (h + 1) k hlo hpair' hgap
  simp only [S, κ, Fintype.card_coe, hn] at hjohnson
  have hmul : 2 * h * k ≤ h * h := by
    have := Nat.mul_le_mul_left h hrate
    nlinarith
  have hdenom : 2 * h + 1 ≤ (h + 1) ^ 2 - 2 * h * k := by
    have hexpand : (h + 1) ^ 2 = h * h + 2 * h + 1 := by ring
    rw [hexpand]
    omega
  by_contra hnot
  rw [not_lt] at hnot
  have hlower : (2 * h) * (2 * h + 1) ≤
      family.G.card * ((h + 1) ^ 2 - 2 * h * k) :=
    Nat.mul_le_mul hnot hdenom
  have hstrict : (2 * h) ^ 2 < (2 * h) * (2 * h + 1) := by
    nlinarith
  omega

/-- Distinct selected agreements have intersection at most `k` when the direction
row has no exceptional degree-`<k` agreement core. -/
theorem pair_inter_card_le_of_directionAgreementCap
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hdir : DirectionAgreementCap dom (u 1) k)
    {gamma beta : F} (hgamma : gamma ∈ family.G)
    (hbeta : beta ∈ family.G) (hne : gamma ≠ beta) :
    (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
      fullAgreement dom (u 0) (u 1) beta (family.q beta)).card ≤ k := by
  let r := slopePolynomial gamma beta (family.q gamma) (family.q beta)
  let roots := Finset.univ.filter fun i => r.eval (dom i) = u 1 i
  have hrdeg : r.natDegree < k := by
    exact slopePolynomial_natDegree_lt
      (family.degree_lt gamma hgamma) (family.degree_lt beta hbeta)
  have hsub :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) ⊆ roots := by
    intro i hi
    have hi' := Finset.mem_inter.mp hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    exact slopePolynomial_eval_eq_direction
      dom (u 0) (u 1) hne hi'.1 hi'.2
  exact (Finset.card_le_card hsub).trans (hdir r hrdeg)

/-- **Far-direction rate-quarter branch.**  A hypothetical family of `2h` bad
scalars forces the received direction to agree with some degree-`<k` polynomial on at least
`k+1` coordinates. -/
theorem card_lt_two_mul_of_directionAgreementCap
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hh : 1 ≤ h) (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h)
    (hdir : DirectionAgreementCap dom (u 1) k) :
    family.G.card < 2 * h := by
  apply card_lt_two_mul_of_pair_inter_le family hh hn hthreshold hrate
  intro gamma hgamma beta hbeta hne
  exact pair_inter_card_le_of_directionAgreementCap
    family hdir hgamma hbeta hne

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFarDirection

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFarDirection
#print axioms card_lt_two_mul_of_pair_inter_le
#print axioms card_lt_two_mul_of_directionAgreementCap
