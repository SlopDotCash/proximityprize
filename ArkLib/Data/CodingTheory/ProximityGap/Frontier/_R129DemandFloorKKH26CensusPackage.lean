/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R128DemandFloorSubsetSumCensusProducer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R121DemandFloorTailTheoremInterface

/-!
# Packaged KKH26 census route for the demand tail

R128's subset-sum census producer shows that an exact KKH26 monomial-pair bad-scalar census
over any `2g`-point domain fits the R125 maximal-binomial allowance.  This file packages the
corresponding remaining theorem: dominate the candidate bad-count family by such an exact
census at every active deep tail rung.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage

open ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer
open ArkLib.ProximityGap.Frontier.R128DemandFloorSubsetSumCensusProducer
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface

/-- The exact KKH26 bad-scalar census cardinality over a finite field domain. -/
noncomputable def kkh26BadScalarCensusCard
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    (H : Finset F) (r : ℕ) : ℕ := by
  classical
  exact
    (Finset.univ.filter (fun lam : F =>
      ∃ q : Polynomial F, q.natDegree ≤ r - 2 ∧
        r ≤ (ArkLib.ProximityGap.KKH26.lineAgreeSet H r lam q).card)).card

/-- The proof payload for one KKH26 census dominator after the field/domain have been chosen. -/
structure KKH26CensusDominatorWitness
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    {F : Type} [Field F] [DecidableEq F] [Fintype F] (H : Finset F) : Prop where
  hH : H.card = 2 * g
  hBad : Bad r (4 * g) ≤ kkh26BadScalarCensusCard H r

/-- At one active rung, the bad-count family is dominated by an exact KKH26 census on some
finite field domain of size `2g`. -/
def KKH26CensusDominatesAt (Bad : ℕ → ℕ → ℕ) (g r : ℕ) : Prop :=
  ∃ (F : Type) (field : Field F) (dec : DecidableEq F) (fin : Fintype F),
    ∃ H : Finset F, @KKH26CensusDominatorWitness Bad g r F field dec fin H

/-- The KKH26 census domination route, uniformly over all active deep rungs. -/
def HasKKH26CensusDominators (Bad : ℕ → ℕ → ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → KKH26CensusDominatesAt Bad g r

/-- A single KKH26 census dominator gives the maximal-binomial allowance at its rung. -/
theorem maximal_allowance_of_kkh26_census_dominator_at
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hr : 6 ≤ r)
    (W : KKH26CensusDominatesAt Bad g r) :
    Bad r (4 * g) ≤ (4 * g) * maximalTailOP g r + 1 := by
  rcases W with ⟨F, instField, instDec, instFin, H, W⟩
  letI : Field F := instField
  letI : DecidableEq F := instDec
  letI : Fintype F := instFin
  exact W.hBad.trans
    (by
      rw [kkh26BadScalarCensusCard]
      exact kkh26_badScalar_census_card_le_maximal_allowance H g r W.hH (by omega))

/-- Uniform KKH26 census dominators imply the R125 maximal tail count bound. -/
theorem maximal_tail_count_bound_of_kkh26_census_dominators
    (Bad : ℕ → ℕ → ℕ)
    (hdom : HasKKH26CensusDominators Bad) :
    MaximalTailCountBound Bad := by
  intro g r hg hr hrg
  exact maximal_allowance_of_kkh26_census_dominator_at Bad g r hr (hdom g r hg hr hrg)

/-- Uniform KKH26 census dominators produce the natural-range deep-tail orbit certificates
expected by the R120/R121 demand theorem interface. -/
theorem deep_tail_orbit_certificates_le_of_kkh26_census_dominators
    (Bad : ℕ → ℕ → ℕ)
    (hdom : HasKKH26CensusDominators Bad)
    (g : ℕ) (hg : 3 ≤ g) :
    HasDeepTailOrbitCertificatesLe Bad g := by
  intro r hr hrg
  refine ⟨maximalTailOP g r, ?_, ?_⟩
  · exact le_rfl
  · exact maximal_allowance_of_kkh26_census_dominator_at Bad g r hr
      (hdom g r hg hr hrg)

/-- Checked prefix agreement plus uniform KKH26 census dominators give the packaged natural
demand certificate at one active `g`. -/
theorem natural_demand_certificate_of_prefix_and_kkh26_census_dominators
    (Bad : ℕ → ℕ → ℕ)
    (hdom : HasKKH26CensusDominators Bad)
    (g : ℕ) (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g) :
    HasNaturalDemandCertificate Bad g :=
  ⟨hprefix, deep_tail_orbit_certificates_le_of_kkh26_census_dominators Bad hdom g hg⟩

/-- Uniform checked prefixes plus uniform KKH26 census dominators give the full natural demand
certificate theorem consumed by R121. -/
theorem natural_demand_theorem_of_prefixes_and_kkh26_census_dominators
    (Bad : ℕ → ℕ → ℕ)
    (hdom : HasKKH26CensusDominators Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) :
    NaturalDemandCertificateTheorem Bad :=
  natural_demand_theorem_of_maximal_tail_count_bound Bad hprefix
    (maximal_tail_count_bound_of_kkh26_census_dominators Bad hdom)

end ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage.kkh26BadScalarCensusCard
#print axioms
  ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage.KKH26CensusDominatorWitness
#print axioms
  ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage.KKH26CensusDominatesAt
#print axioms
  ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage.HasKKH26CensusDominators
#print axioms
  ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage.maximal_allowance_of_kkh26_census_dominator_at
#print axioms
  ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage.maximal_tail_count_bound_of_kkh26_census_dominators
#print axioms
  ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage.deep_tail_orbit_certificates_le_of_kkh26_census_dominators
#print axioms
  ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage.natural_demand_certificate_of_prefix_and_kkh26_census_dominators
#print axioms
  ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage.natural_demand_theorem_of_prefixes_and_kkh26_census_dominators
