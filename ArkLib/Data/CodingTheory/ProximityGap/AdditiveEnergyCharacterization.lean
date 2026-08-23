/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyLowerBound

/-!
# THE ENERGY CHARACTERIZATION OF SIDON-MOD-NEGATION (#389)

Completing the additive-energy extremality picture: `additiveEnergy_eq_of_sidonModNeg` (equality
from Sidon) + `additiveEnergy_ge` (lower bound) give one direction; this file proves the converse
`sidonModNeg_of_additiveEnergy_eq` (energy-minimal ⟹ Sidon) and packages the **iff**:

> **`additiveEnergy_eq_iff_sidonModNeg`** — for negation-closed `G ∌ 0` (char `≠ 2`),
> `E(G) = 3|G|² − 3|G|  ↔  SidonModNeg G`.

So the char-0 minimal energy `3|G|² − 3|G|` is attained *exactly* at the Sidon-modulo-negation sets:
equality in the lower bound forces, pointwise, that every nonzero `a+b` has exactly the two trivial
representations `{a, b}`.  Axiom-clean.  Issue #389.
-/

open Finset ArkLib.ProximityGap.AdditiveEnergyRepBound
namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Energy-minimal ⟹ Sidon-mod-negation.**  If a negation-closed `G ∌ 0` (char `≠ 2`) attains the
minimal additive energy `3|G|² − 3|G|`, then it is Sidon-modulo-negation — the converse of
`additiveEnergy_eq_of_sidonModNeg`.  Equality in the lower bound forces, pointwise, that every
nonzero `a+b` has *exactly* the two trivial representations `{a, b}`. -/
theorem sidonModNeg_of_additiveEnergy_eq {G : Finset F} (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) (hE : additiveEnergy G = 3 * G.card ^ 2 - 3 * G.card) :
    SidonModNeg G := by
  classical
  -- the structural sum equals the energy (both = 3|G|²−3|G|)
  have hval : (∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card))
      = additiveEnergy G := by
    rw [Finset.sum_congr rfl fun a ha => structuredInner_eq h2 h0 hneg ha,
      Finset.sum_const, smul_eq_mul, hE]
    rcases Nat.eq_zero_or_pos G.card with h | h
    · rw [h]; simp
    · have h1 : 3 ≤ 3 * G.card := by omega
      have hsq : G.card ≤ G.card ^ 2 := Nat.le_self_pow (by norm_num) _
      zify [h1, show 3 * G.card ≤ 3 * G.card ^ 2 by omega]; ring
  -- the energy is the sum of repCounts, and structural ≤ repCount pointwise; equality forces
  -- pointwise equality
  have houter : ∀ a ∈ G,
      (∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card))
        = ∑ b ∈ G, repCount G (a + b) := by
    refine (Finset.sum_eq_sum_iff_of_le ?_).mp ?_
    · exact fun a ha => Finset.sum_le_sum fun b hb => repCount_ge_structured hneg ha hb
    · rw [hval]; rfl
  have hpt : ∀ a ∈ G, ∀ b ∈ G,
      (if a + b = 0 then G.card else ({a, b} : Finset F).card) = repCount G (a + b) := by
    intro a ha
    exact (Finset.sum_eq_sum_iff_of_le
      (fun b hb => repCount_ge_structured hneg ha hb)).mp (houter a ha)
  -- conclude SidonModNeg from pointwise equality at nonzero sums
  intro a ha b hb c hc d hd hsum'
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnp1, hnp2, hns⟩ := hcon
  -- `c` represents `a+b`, so it lies in the rep set, which has card `|{a,b}|`
  have hkey := hpt a ha b hb
  rw [if_neg hns] at hkey
  -- {a,b} ⊆ rep set and |rep set| = |{a,b}|, so rep set = {a,b}
  have hsub : ({a, b} : Finset F) ⊆ G.filter (fun y => a + b - y ∈ G) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    rcases hx with hxa | hxb
    · rw [hxa]; exact ⟨ha, by rw [show a + b - a = b by ring]; exact hb⟩
    · rw [hxb]; exact ⟨hb, by rw [show a + b - b = a by ring]; exact ha⟩
  have hcard : (G.filter (fun y => a + b - y ∈ G)).card = ({a, b} : Finset F).card := by
    unfold repCount at hkey; omega
  have heq : G.filter (fun y => a + b - y ∈ G) = ({a, b} : Finset F) :=
    (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)).symm
  -- `c` is in the rep set (since `(a+b) - c = d ∈ G`), hence `c = a` or `c = b`
  have hcrep : c ∈ G.filter (fun y => a + b - y ∈ G) := by
    rw [Finset.mem_filter]
    refine ⟨hc, ?_⟩
    rw [show a + b - c = d by linear_combination hsum']; exact hd
  rw [heq, Finset.mem_insert, Finset.mem_singleton] at hcrep
  rcases hcrep with rfl | rfl
  · exact hnp1 rfl (by linear_combination hsum')
  · exact hnp2 (by linear_combination hsum') rfl

/-- **The energy characterization of Sidon-modulo-negation.**  For a negation-closed `G ∌ 0`
(char `≠ 2`), `additiveEnergy G = 3|G|² − 3|G|` *iff* `G` is Sidon-modulo-negation — the char-0
minimal energy is attained exactly at the Sidon-mod-negation sets. -/
theorem additiveEnergy_eq_iff_sidonModNeg {G : Finset F} (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    additiveEnergy G = 3 * G.card ^ 2 - 3 * G.card ↔ SidonModNeg G :=
  ⟨sidonModNeg_of_additiveEnergy_eq h2 h0 hneg,
    additiveEnergy_eq_of_sidonModNeg h2 h0 hneg⟩

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.sidonModNeg_of_additiveEnergy_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_eq_iff_sidonModNeg
