/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R331OrbitChebyshevSurplusWeld
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R391RelationHeightLedger

/-!
# LANE B2 (#466 round 392): THE CAPSTONE CONSUMER — a relation-count bound is the ONLY
  open input of the whole moment arc

This brick composes the entire r300–r391 chain into ONE conditional theorem with ONE named
hypothesis:

* **`RealizedRelationCountBound`** :  the named open Prop — the total number of realized
  vanishing relations (over all sectors) is at most `K`;
* **`rEnergy_le_of_relationCountBound`** :  under the r310 rep-identification, a relation
  count bound gives `E_r ≤ (1 + K) · shadowEnergy` (r312 identity + r388 union bound);
* **`orbit_count_of_relationCountBound`** (THE CAPSTONE):  a relation-count bound implies
  the depth-`r` orbit-level Chebyshev

  ```text
  |R| · |G| · T²  ≤  q · (q · (1 + K) · shadowEnergy(n, m, r) − |G|^{2r})
  ```

  for every pairwise `G`-inequivalent family `R` of `T`-large deviations — i.e. the
  moment-side control the prize pipeline consumes, with `shadowEnergy` an exact char-0
  constant and `K` the single remaining unknown.

Everything else in the statement is machine-checked; the arc's honest summary is now a
formal biconditional-shaped reduction: sub-Wick moment control at depth `r` needs exactly a
sub-Wick-scale `K`.  With r389 (census identity), r390/r391 (height-certified
annihilators), and r371/r372 (orbit quantization), `K` is a COUNT of bounded-height sparse
cyclotomic relations vanishing at the prime — the open core, as one named Prop.
Issue #466, round 392, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R392RelationCountCapstone

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance
open ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R331OrbitChebyshevSurplusWeld
open ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The named open Prop**: at most `K` realized vanishing relations, over all sectors.
This is the single remaining input of the moment arc. -/
def RealizedRelationCountBound (g : F) (n m r K : ℕ) : Prop :=
  ∑ s ∈ Finset.range (m + 1), (sectorRelations g n m r s).card ≤ K

/-- A relation-count bound controls the full depth-`r` energy:
`E_r ≤ (1 + K) · shadowEnergy`. -/
theorem rEnergy_le_of_relationCountBound (g : F) (G : Finset F) (n m r K : ℕ)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hrep : PowerShadowRepIdentifies g G n r)
    (hK : RealizedRelationCountBound g n m r K) :
    rEnergy G r ≤ (1 + K) * shadowEnergy n m r := by
  have hid := rEnergy_eq_shadowEnergy_add_collisionMass_of_repIdentifies
    g G n m r hm hn hg hrep
  have hcount := collisionMass_le_relCount_mul_shadowEnergy g n m r
  have hmono : (∑ s ∈ Finset.range (m + 1), (sectorRelations g n m r s).card)
      * shadowEnergy n m r ≤ K * shadowEnergy n m r :=
    Nat.mul_le_mul_right _ hK
  calc rEnergy G r
      = shadowEnergy n m r + shadowCollisionMass g n m r := hid
    _ ≤ shadowEnergy n m r + K * shadowEnergy n m r :=
        Nat.add_le_add_left (le_trans hcount hmono) _
    _ = (1 + K) * shadowEnergy n m r := by ring

/-- **THE CAPSTONE**: a relation-count bound implies the depth-`r` orbit-level Chebyshev
with the char-0 constant — the moment-side control of the prize pipeline, conditional on
exactly one named count. -/
theorem orbit_count_of_relationCountBound (g : F) (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (n m r K : ℕ) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hrep : PowerShadowRepIdentifies g G n r)
    (hK : RealizedRelationCountBound g n m r K)
    (Rset : Finset F)
    (hR0 : ∀ b ∈ Rset, b ≠ 0)
    (hdisj : ∀ b ∈ Rset, ∀ b' ∈ Rset, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ Rset, T ≤ |R303GeneralROrbitChebyshev.deviationR G r b|) :
    (Rset.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ)
              * ((1 + K : ℕ) * (shadowEnergy n m r : ℝ))
            - (G.card : ℝ) ^ (2 * r)) := by
  have hE : (rEnergy G r : ℝ) ≤ ((1 + K : ℕ) : ℝ) * (shadowEnergy n m r : ℝ) := by
    have := rEnergy_le_of_relationCountBound g G n m r K hm hn hg hrep hK
    calc (rEnergy G r : ℝ)
        ≤ (((1 + K) * shadowEnergy n m r : ℕ) : ℝ) := by exact_mod_cast this
      _ = ((1 + K : ℕ) : ℝ) * (shadowEnergy n m r : ℝ) := by push_cast; ring
  have h := orbit_count_le_shadow_plus_surplus G hmul hinv h0 n m r
    (((1 + K : ℕ) : ℝ) * (shadowEnergy n m r : ℝ) - (shadowEnergy n m r : ℝ))
    (by linarith) Rset hR0 hdisj hT hbig
  calc (Rset.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ)
              * ((shadowEnergy n m r : ℝ)
                + (((1 + K : ℕ) : ℝ) * (shadowEnergy n m r : ℝ)
                  - (shadowEnergy n m r : ℝ)))
            - (G.card : ℝ) ^ (2 * r)) := h
    _ = (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ)
              * ((1 + K : ℕ) * (shadowEnergy n m r : ℝ))
            - (G.card : ℝ) ^ (2 * r)) := by ring

end ArkLib.ProximityGap.Frontier.R392RelationCountCapstone

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R392RelationCountCapstone.rEnergy_le_of_relationCountBound
#print axioms
  ArkLib.ProximityGap.Frontier.R392RelationCountCapstone.orbit_count_of_relationCountBound
