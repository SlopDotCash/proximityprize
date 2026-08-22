/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R127DemandFloorLadderListProducer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R121DemandFloorTailTheoremInterface

/-!
# Packaged ladder-list majorant for the demand tail

R127 shows that a pointwise majorant of `Bad r (4g)` by the corresponding ladder-list count
implies the R125 maximal-binomial allowance.  This file packages the remaining theorem as a
single producer predicate: for each active tail rung, choose production parameters and a ladder
domain whose list count dominates the bad family.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage

open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer
open ArkLib.ProximityGap.Frontier.R127DemandFloorLadderListProducer
open ProximityGap.LadderList
open ProximityGap.SpikeFloor ProximityGap.LadderListModP

/-- The proof payload for one ladder-list majorant after all production data have been chosen. -/
structure LadderMajorantWitness
    (Bad : ℕ → ℕ → ℕ) (g r p n ν k : ℕ) [Fact p.Prime]
    (root lam : ZMod p) (dom : Fin n ↪ ZMod p) : Prop where
  hn4 : n = 4 * g
  hr : 1 ≤ r
  hν : 1 ≤ ν
  hroot : IsPrimitiveRoot root (2 ^ ν)
  hn : n = 2 ^ ν
  hdomain : ∀ i, (dom i) ^ n = 1
  hk1 : 1 ≤ k
  hk2 : k ≤ 2 * r - 2
  hk3 : 2 * r - 3 ≤ k
  hp : (2 * r) ^ 2 ^ (ν - 1) < p
  hBad : Bad r (4 * g) ≤ (4 * g) * ladderListCount p n r k lam dom + 1

/-- A packaged ladder-list majorant for one active tail rung, existentially choosing all
production data. -/
def HasLadderMajorantAt (Bad : ℕ → ℕ → ℕ) (g r : ℕ) : Prop :=
  ∃ (p n ν k : ℕ), ∃ (_hp : Fact p.Prime),
    ∃ (root lam : ZMod p), ∃ (dom : Fin n ↪ ZMod p),
      LadderMajorantWitness Bad g r p n ν k root lam dom

/-- The remaining ladder-list route, uniformly over all active deep rungs. -/
def HasLadderMajorants (Bad : ℕ → ℕ → ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → HasLadderMajorantAt Bad g r

/-- A single ladder majorant witness gives the maximal-binomial allowance at its rung. -/
theorem maximal_allowance_of_ladder_majorant_at
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (W : HasLadderMajorantAt Bad g r) :
    Bad r (4 * g) ≤ (4 * g) * maximalTailOP g r + 1 := by
  rcases W with ⟨p, n, ν, k, hp, root, lam, dom, W⟩
  letI : Fact p.Prime := hp
  exact bad_le_maximal_allowance_of_ladder_list_majorant
    (Bad := Bad) (p := p) (n := n) (ν := ν) (r := r) (k := k)
    (g := g) (root := root) (lam := lam) (dom := dom)
    W.hn4 W.hr W.hν W.hroot W.hn W.hdomain W.hk1 W.hk2 W.hk3 W.hp W.hBad

/-- Uniform ladder majorants imply the R125 maximal tail count bound. -/
theorem maximal_tail_count_bound_of_ladder_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hmajor : HasLadderMajorants Bad) :
    MaximalTailCountBound Bad := by
  intro g r hg hr hrg
  exact maximal_allowance_of_ladder_majorant_at Bad g r (hmajor g r hg hr hrg)

/-- Uniform ladder-list majorants produce the natural-range deep-tail orbit certificates
expected by the R120/R121 demand theorem interface. -/
theorem deep_tail_orbit_certificates_le_of_ladder_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hmajor : HasLadderMajorants Bad)
    (g : ℕ) (hg : 3 ≤ g) :
    HasDeepTailOrbitCertificatesLe Bad g := by
  intro r hr hrg
  refine ⟨maximalTailOP g r, ?_, ?_⟩
  · exact le_rfl
  · exact maximal_allowance_of_ladder_majorant_at Bad g r (hmajor g r hg hr hrg)

/-- Checked prefix agreement plus uniform ladder-list majorants give the packaged natural
demand certificate at one active `g`. -/
theorem natural_demand_certificate_of_prefix_and_ladder_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hmajor : HasLadderMajorants Bad)
    (g : ℕ) (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g) :
    HasNaturalDemandCertificate Bad g :=
  ⟨hprefix, deep_tail_orbit_certificates_le_of_ladder_majorants Bad hmajor g hg⟩

/-- Uniform checked prefixes plus uniform ladder-list majorants give the full natural demand
certificate theorem consumed by R121. -/
theorem natural_demand_theorem_of_prefixes_and_ladder_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hmajor : HasLadderMajorants Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) :
    NaturalDemandCertificateTheorem Bad :=
  natural_demand_theorem_of_maximal_tail_count_bound Bad hprefix
    (maximal_tail_count_bound_of_ladder_majorants Bad hmajor)

end ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage.LadderMajorantWitness
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage.HasLadderMajorantAt
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage.HasLadderMajorants
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage.maximal_allowance_of_ladder_majorant_at
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage.maximal_tail_count_bound_of_ladder_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage.deep_tail_orbit_certificates_le_of_ladder_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage.natural_demand_certificate_of_prefix_and_ladder_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage.natural_demand_theorem_of_prefixes_and_ladder_majorants
