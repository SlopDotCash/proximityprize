/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyCharacterization

/-!
# THE REP-COUNT CHARACTERIZATION OF SIDON-MOD-NEGATION (#389)

The third face of the Sidon-modulo-negation characterization, completing the **triple equivalence**
for a negation-closed `G ∌ 0` in characteristic `≠ 2`:

> `additiveEnergy G = 3|G|² − 3|G|   ↔   SidonModNeg G   ↔   ∀ c ≠ 0, repCount G c ≤ 2`.

`additiveEnergy_eq_iff_sidonModNeg` (in `AdditiveEnergyCharacterization`) gives the first `↔`; this
file gives the second via `sidonModNeg_of_repCount_le_two` (a genuine nontrivial coincidence would
produce a *third* distinct representation of `a + b`) and packages it as
`sidonModNeg_iff_repCount_le_two`.  Axiom-clean.  Issue #389.
-/

open Finset ArkLib.ProximityGap.AdditiveEnergyRepBound
namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Bounded rep-count ⟹ Sidon-mod-negation.**  If every nonzero shift has at most `2`
representations, then `G` is Sidon-modulo-negation.  (A genuine nontrivial coincidence would give a
third, distinct representation of `a + b`.) -/
theorem sidonModNeg_of_repCount_le_two {G : Finset F} (h2 : (2 : F) ≠ 0)
    (hrc : ∀ c : F, c ≠ 0 → repCount G c ≤ 2) : SidonModNeg G := by
  classical
  intro a ha b hb c hc d hd hsum
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnp1, hnp2, hns⟩ := hcon
  -- no-overlap distinctness
  have hac : a ≠ c := fun h => hnp1 h (by linear_combination hsum - h)
  have had : a ≠ d := fun h => hnp2 h (by linear_combination hsum - h)
  have hbc : b ≠ c := fun h => hnp2 (by linear_combination hsum - h) h
  have hbd : b ≠ d := fun h => hnp1 (by linear_combination hsum - h) h
  -- membership in the rep set of `a+b`
  set R := G.filter (fun z => a + b - z ∈ G) with hRdef
  have hmemR : ∀ {x y : F}, x ∈ G → y ∈ G → a + b - x = y → x ∈ R := by
    intro x y hx hy hxy; rw [hRdef, Finset.mem_filter]; exact ⟨hx, hxy ▸ hy⟩
  have hRa : a ∈ R := hmemR ha hb (by ring)
  have hRb : b ∈ R := hmemR hb ha (by ring)
  have hRc : c ∈ R := hmemR hc hd (by linear_combination hsum)
  have hRd : d ∈ R := hmemR hd hc (by linear_combination hsum)
  -- three distinct representations ⇒ repCount ≥ 3, contradicting `≤ 2`
  have hcard3 : 3 ≤ R.card := by
    by_cases hab : a = b
    · -- {a, c, d}
      have hcd : c ≠ d := by
        intro h; apply hac; have : (2 : F) * a = 2 * c := by linear_combination hsum + hab - h
        exact mul_left_cancel₀ h2 this
      have hsub : ({a, c, d} : Finset F) ⊆ R := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        exacts [hRa, hRc, hRd]
      have h3 : ({a, c, d} : Finset F).card = 3 := by
        rw [Finset.card_eq_three]; exact ⟨a, c, d, hac, had, hcd, rfl⟩
      calc 3 = ({a, c, d} : Finset F).card := h3.symm
        _ ≤ R.card := Finset.card_le_card hsub
    · -- {a, b, c}
      have hsub : ({a, b, c} : Finset F) ⊆ R := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        exacts [hRa, hRb, hRc]
      have h3 : ({a, b, c} : Finset F).card = 3 := by
        rw [Finset.card_eq_three]; exact ⟨a, b, c, hab, hac, hbc, rfl⟩
      calc 3 = ({a, b, c} : Finset F).card := h3.symm
        _ ≤ R.card := Finset.card_le_card hsub
  have hle := hrc (a + b) hns
  unfold repCount at hle
  rw [← hRdef] at hle
  omega

/-- **The rep-count characterization of Sidon-modulo-negation.**  For char `≠ 2` and a negation-closed
`G ∌ 0`, `SidonModNeg G ↔ ∀ c ≠ 0, repCount G c ≤ 2`.  Together with
`additiveEnergy_eq_iff_sidonModNeg`, this gives the triple equivalence
`E(G) = 3|G|² − 3|G|  ↔  SidonModNeg G  ↔  ∀ c ≠ 0, r(c) ≤ 2`. -/
theorem sidonModNeg_iff_repCount_le_two {G : Finset F} (h2 : (2 : F) ≠ 0)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    SidonModNeg G ↔ ∀ c : F, c ≠ 0 → repCount G c ≤ 2 := by
  refine ⟨fun hS c hc => ?_, sidonModNeg_of_repCount_le_two h2⟩
  by_cases hex : ∃ a ∈ G, ∃ b ∈ G, a + b = c
  · obtain ⟨a, ha, b, hb, rfl⟩ := hex
    have hrep := repCount_sidonModNeg hneg hS ha hb
    rw [if_neg hc] at hrep
    rw [hrep]; simpa using Finset.card_insert_le a {b}
  · -- no representation: repCount = 0
    push_neg at hex
    have : repCount G c = 0 := by
      unfold repCount; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy hcy; exact hex y hy (c - y) hcy (by ring)
    rw [this]; norm_num

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.sidonModNeg_of_repCount_le_two
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.sidonModNeg_iff_repCount_le_two
