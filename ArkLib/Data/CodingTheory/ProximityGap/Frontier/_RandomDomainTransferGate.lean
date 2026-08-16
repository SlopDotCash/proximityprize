/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Random-domain theorems need a fixed-domain transfer certificate

This file records the finite logical gate behind the random-RS / subspace-design literature route
for issue #464.

Random-domain and "there exists a good evaluation set" results have the wrong quantifier for the
Ethereum prize target.  The prize fixes the smooth subgroup domain.  A theorem saying that some
domain is good, or that all but a small exceptional set of domains are good, proves the smooth-domain
statement only after one additionally proves that the smooth domain is outside the exceptional set.

The statements below are deliberately abstract.  `Ω` is a finite family of candidate domains and
`Good : Ω -> Prop` is any desired proximity/list-decoding predicate.  The Boolean countermodels are
the whole point: one good domain, or even one exceptional domain among many, can still leave the
designated smooth domain bad.
-/

namespace ArkLib.ProximityGap.Frontier.RandomDomainTransferGate

open Finset

variable {Ω : Type}

/-- There exists at least one good domain. -/
def ExistsGoodDomain (Good : Ω -> Prop) : Prop :=
  ∃ ω : Ω, Good ω

/-- Every domain in the family is good. -/
def AllDomainsGood (Good : Ω -> Prop) : Prop :=
  ∀ ω : Ω, Good ω

/-- The designated fixed domain is good.  In the prize application, this is the smooth subgroup
domain, not a random evaluation set. -/
def FixedDomainGood (Good : Ω -> Prop) (ω₀ : Ω) : Prop :=
  Good ω₀

/-- Number of bad domains in a finite family. -/
noncomputable def badDomainCount [Fintype Ω] (Good : Ω -> Prop) : ℕ := by
  classical
  exact (Finset.univ.filter (fun ω : Ω => ¬ Good ω)).card

/-- Uniform goodness implies the designated fixed domain is good. -/
theorem fixedDomainGood_of_allDomainsGood
    (Good : Ω -> Prop) (ω₀ : Ω)
    (h : AllDomainsGood Good) :
    FixedDomainGood Good ω₀ :=
  h ω₀

/-- Zero bad domains is exactly the finite form of uniform goodness. -/
theorem allDomainsGood_of_badDomainCount_eq_zero [Fintype Ω]
    (Good : Ω -> Prop)
    (hbad : badDomainCount Good = 0) :
    AllDomainsGood Good := by
  classical
  intro ω
  by_contra hω
  have hmem : ω ∈ (Finset.univ.filter (fun ω : Ω => ¬ Good ω)) := by
    simp [hω]
  have hpos : 0 < (Finset.univ.filter (fun ω : Ω => ¬ Good ω)).card :=
    Finset.card_pos.mpr ⟨ω, hmem⟩
  unfold badDomainCount at hbad
  omega

/-- Uniform goodness gives zero bad domains. -/
theorem badDomainCount_eq_zero_of_allDomainsGood [Fintype Ω]
    (Good : Ω -> Prop)
    (h : AllDomainsGood Good) :
    badDomainCount Good = 0 := by
  classical
  unfold badDomainCount
  rw [Finset.card_eq_zero]
  exact Finset.filter_eq_empty_iff.mpr (fun ω _ => not_not.mpr (h ω))

/-- A zero-exception theorem gives the designated fixed-domain theorem. -/
theorem fixedDomainGood_of_no_bad_domains [Fintype Ω]
    (Good : Ω -> Prop) (ω₀ : Ω)
    (hbad : badDomainCount Good = 0) :
    FixedDomainGood Good ω₀ :=
  fixedDomainGood_of_allDomainsGood Good ω₀
    (allDomainsGood_of_badDomainCount_eq_zero Good hbad)

/-- The good-domain predicate on `Bool` with `true` good and `false` bad. -/
def boolGood : Bool -> Prop :=
  fun b => b = true

/-- There exists a good domain, but the designated domain `false` is bad. -/
theorem existsGoodDomain_not_force_fixedDomainGood :
    ExistsGoodDomain boolGood ∧ ¬ FixedDomainGood boolGood false := by
  constructor
  · exact ⟨true, rfl⟩
  · simp [FixedDomainGood, boolGood]

/-- The Boolean countermodel has exactly one exceptional domain. -/
theorem badDomainCount_boolGood :
    badDomainCount boolGood = 1 := by
  classical
  unfold badDomainCount boolGood
  have hfilter :
      (Finset.univ.filter (fun b : Bool => ¬b = true)) = ({false} : Finset Bool) := by
    ext b
    cases b <;> simp
  have hcard := congrArg Finset.card hfilter
  simpa using hcard

/-- Even "all but one domain is good" does not certify a designated domain: the fixed domain may be
the unique exception. -/
theorem one_exception_can_be_the_fixed_domain :
    ExistsGoodDomain boolGood ∧ badDomainCount boolGood = 1 ∧
      ¬ FixedDomainGood boolGood false := by
  exact ⟨existsGoodDomain_not_force_fixedDomainGood.1, badDomainCount_boolGood,
    existsGoodDomain_not_force_fixedDomainGood.2⟩

/-! ## Average-score form -/

/-- Uniform average of a real-valued domain score. -/
noncomputable def domainAverage [Fintype Ω] (score : Ω -> ℝ) : ℝ :=
  (∑ ω : Ω, score ω) / (Fintype.card Ω : ℝ)

/-- A score spike at the designated Boolean domain. -/
def boolFixedSpike (high : ℝ) : Bool -> ℝ :=
  fun b => if b then 0 else high

/-- The Boolean fixed-domain spike has average `high / 2`. -/
theorem domainAverage_boolFixedSpike (high : ℝ) :
    domainAverage (boolFixedSpike high) = high / 2 := by
  classical
  unfold domainAverage boolFixedSpike
  norm_num

/-- An average-domain score bound does not bound the designated fixed domain.  The fixed domain can
carry the entire spike while the average pays only the one-domain mass. -/
theorem averageDomainBound_not_force_fixedDomainBound
    {T high : ℝ} (hThigh : T < high) :
    ∃ score : Bool -> ℝ,
      domainAverage score = high / 2 ∧ T < score false := by
  refine ⟨boolFixedSpike high, domainAverage_boolFixedSpike high, ?_⟩
  simpa [boolFixedSpike] using hThigh

end ArkLib.ProximityGap.Frontier.RandomDomainTransferGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.RandomDomainTransferGate.fixedDomainGood_of_allDomainsGood
#print axioms ArkLib.ProximityGap.Frontier.RandomDomainTransferGate.allDomainsGood_of_badDomainCount_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.RandomDomainTransferGate.badDomainCount_eq_zero_of_allDomainsGood
#print axioms ArkLib.ProximityGap.Frontier.RandomDomainTransferGate.fixedDomainGood_of_no_bad_domains
#print axioms ArkLib.ProximityGap.Frontier.RandomDomainTransferGate.existsGoodDomain_not_force_fixedDomainGood
#print axioms ArkLib.ProximityGap.Frontier.RandomDomainTransferGate.badDomainCount_boolGood
#print axioms ArkLib.ProximityGap.Frontier.RandomDomainTransferGate.one_exception_can_be_the_fixed_domain
#print axioms ArkLib.ProximityGap.Frontier.RandomDomainTransferGate.domainAverage_boolFixedSpike
#print axioms ArkLib.ProximityGap.Frontier.RandomDomainTransferGate.averageDomainBound_not_force_fixedDomainBound
