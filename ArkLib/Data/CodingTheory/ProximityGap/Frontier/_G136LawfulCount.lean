/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G136EnergySolutionBijection

/-!
# G136 (part 2b + capstone): the lawful count and the rung-2 accident equivalence

The last step of the rung-2 chain.  The three normalized Mann families

```text
Fa = {(1,b,b)},   Fb = {(a,1,a)},   Fc = {(a,−a,−1)}
```

live inside the solution set with pairwise overlaps exactly `(1,1,1)`, `(1,−1,−1)`,
`(−1,1,−1)` and no triple point, so the lawful count is `3n − 3` and

```text
#solutions = 3n − 3 + #accidents.
```

**Capstone** (`rung2_anchor_iff_accidents`): composing with parts 2a and 3a, for any
multiplicatively closed `H ∌ 0` with `−1 ∈ H`, `#H = 2^30`, and `2^90 < q`:

```text
q·E₂(H) ≤ 3·q·(2^30)² + (2^30)⁴   ⟺   #accidents ≤ 3.
```

The production rung-2 anchor IS the statement that the certified prime admits at most
three accidents — fully machine-checked, no interpretive slack, replacing a BGK-face
character-sum problem by a finite Diophantine tolerance.

**Honest scope.**  The accident count at the certified primes is the wall.  CORE remains
OPEN.  Issue #466 (G136).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G136LawfulCount

open Finset
open ArkLib.ProximityGap.Frontier.G136EnergySolutionBijection
open ArkLib.ProximityGap.Frontier.G136AccidentTolerance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The three normalized Mann families inside the solution set. -/
noncomputable def lawful (H : Finset F) : Finset ((F × F) × F) :=
  H.image (fun b => ((1, b), b)) ∪ H.image (fun a => ((a, 1), a)) ∪
    H.image (fun a => ((a, -a), -1))

/-- The accident set: solutions beyond the Mann families. -/
noncomputable def accidents (H : Finset F) : Finset ((F × F) × F) :=
  solutions H \ lawful H

theorem lawful_subset (H : Finset F) (h1 : (1 : F) ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) : lawful H ⊆ solutions H := by
  intro p hp
  unfold lawful at hp
  unfold solutions
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨h1, hb⟩, hb⟩, by ring⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha, h1⟩, ha⟩, by ring⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨ha, hneg _ ha⟩, hneg _ h1⟩, by ring⟩

/-- **The lawful count**: `#lawful = 3·#H − 3`. -/
theorem card_lawful (H : Finset F) (h1 : (1 : F) ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) (h0 : (0 : F) ∉ H) (h2 : (2 : F) ≠ 0) :
    (lawful H).card = 3 * H.card - 3 := by
  classical
  have hm1 : (-1 : F) ∈ H := hneg _ h1
  have hne11 : (-1 : F) ≠ 1 := by
    intro h
    exact h2 (by linear_combination -h)
  unfold lawful
  set fA := H.image (fun b : F => (((1 : F), b), b)) with hfA
  set fB := H.image (fun a : F => ((a, (1 : F)), a)) with hfB
  set fC := H.image (fun a : F => ((a, -a), (-1 : F))) with hfC
  have hA : fA.card = H.card := by
    rw [hfA]
    exact Finset.card_image_of_injOn (fun a _ b _ hab => (Prod.ext_iff.mp hab).2)
  have hB : fB.card = H.card := by
    rw [hfB]
    exact Finset.card_image_of_injOn (fun a _ b _ hab => (Prod.ext_iff.mp hab).2)
  have hC : fC.card = H.card := by
    rw [hfC]
    exact Finset.card_image_of_injOn (fun a _ b _ hab =>
      (Prod.ext_iff.mp (Prod.ext_iff.mp hab).1).1)
  have hintAB : fA ∩ fB = ({(((1 : F), (1 : F)), (1 : F))} :
      Finset ((F × F) × F)) := by
    rw [hfA, hfB]
    ext p
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨b, hb, rfl⟩, ⟨a, _, ha⟩⟩
      have h1a : a = 1 := by
        have := (Prod.ext_iff.mp (Prod.ext_iff.mp ha).1).1
        simpa using this
      have hba : a = b := by
        have := (Prod.ext_iff.mp ha).2
        simpa using this
      rw [← hba, h1a]
    · rintro rfl
      exact ⟨⟨1, h1, rfl⟩, ⟨1, h1, rfl⟩⟩
  have hintABC : (fA ∪ fB) ∩ fC
      = ({(((1 : F), (-1 : F)), (-1 : F)), (((-1 : F), (1 : F)), (-1 : F))} :
          Finset ((F × F) × F)) := by
    rw [hfA, hfB, hfC]
    ext p
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_image,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hAB', ⟨a, ha, rfl⟩⟩
      rcases hAB' with ⟨b, _, hb⟩ | ⟨c, _, hc⟩
      · have ha1 : a = 1 := by
          have := (Prod.ext_iff.mp (Prod.ext_iff.mp hb).1).1
          simpa using this.symm
        left
        rw [ha1]
      · have hc1 : (1 : F) = -a := by
          have := (Prod.ext_iff.mp (Prod.ext_iff.mp hc).1).2
          simpa using this
        have ham1 : a = -1 := by linear_combination hc1
        right
        rw [ham1]
        norm_num
    · rintro (rfl | rfl)
      · exact ⟨Or.inl ⟨-1, hm1, by norm_num⟩, ⟨1, h1, by norm_num⟩⟩
      · exact ⟨Or.inr ⟨-1, hm1, by norm_num⟩, ⟨-1, hm1, by norm_num⟩⟩
  have hkeyAB := Finset.card_union_add_card_inter fA fB
  rw [hintAB, Finset.card_singleton] at hkeyAB
  have hkeyABC := Finset.card_union_add_card_inter (fA ∪ fB) fC
  rw [hintABC] at hkeyABC
  have hcard2 : ({(((1 : F), (-1 : F)), (-1 : F)), (((-1 : F), (1 : F)), (-1 : F))} :
      Finset ((F × F) × F)).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp only [Finset.mem_singleton]
    intro h
    exact hne11 (by
      have := (Prod.ext_iff.mp (Prod.ext_iff.mp h).1).1
      simpa using this.symm)
  rw [hcard2] at hkeyABC
  have h1le : 1 ≤ H.card := Finset.card_pos.mpr ⟨1, h1⟩
  omega

/-- **The accident law**: `#solutions = 3·#H − 3 + #accidents`. -/
theorem card_solutions_eq (H : Finset F) (h1 : (1 : F) ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) (h0 : (0 : F) ∉ H) (h2 : (2 : F) ≠ 0) :
    (solutions H).card = 3 * H.card - 3 + (accidents H).card := by
  have hsub := lawful_subset H h1 hneg
  have := Finset.card_sdiff_add_card_eq_card hsub
  unfold accidents
  rw [← card_lawful H h1 hneg h0 h2]
  omega

/-- **CAPSTONE: the rung-2 anchor is the accident tolerance.**  For multiplicatively closed
`H ∌ 0` with `−1 ∈ H`, `#H = 2^30`, and `2^90 < q`:
`q·E₂(H) ≤ 3·q·(2^30)² + (2^30)⁴ ⟺ #accidents ≤ 3`. -/
theorem rung2_anchor_iff_accidents (H : Finset F) {q : ℕ}
    (hq : 2 ^ 90 < q)
    (hcard : H.card = 2 ^ 30)
    (h1 : (1 : F) ∈ H) (hneg : ∀ x ∈ H, -x ∈ H) (h0 : (0 : F) ∉ H)
    (h2 : (2 : F) ≠ 0)
    (hmul : ∀ x ∈ H, ∀ u ∈ H, x * u ∈ H) (hinv : ∀ x ∈ H, x⁻¹ ∈ H) :
    q * Finset.addREnergy 2 H ≤ 3 * q * (2 ^ 30) ^ 2 + (2 ^ 30) ^ 4
      ↔ (accidents H).card ≤ 3 := by
  rw [addREnergy_two_eq_card_mul_solutions H h0 hmul hinv,
    card_solutions_eq H h1 hneg h0 h2, hcard]
  have hshape : q * (2 ^ 30 * (3 * 2 ^ 30 - 3 + (accidents H).card))
      = q * (3 * (2 ^ 30 : ℕ) ^ 2 - 3 * 2 ^ 30 + 2 ^ 30 * (accidents H).card) := by
    congr 1
    have : (3 * 2 ^ 30 - 3 : ℕ) + 3 = 3 * 2 ^ 30 := by norm_num
    have h30 : (2 : ℕ) ^ 30 * (3 * 2 ^ 30 - 3) = 3 * (2 ^ 30 : ℕ) ^ 2 - 3 * 2 ^ 30 := by
      have hexp : (2 : ℕ) ^ 30 * (3 * 2 ^ 30 - 3) + 2 ^ 30 * 3
          = 3 * (2 ^ 30 : ℕ) ^ 2 := by
        rw [← Nat.mul_add, this]
        ring
      omega
    rw [Nat.mul_add, h30]
  rw [hshape,
    anchor_iff_tolerance (q := q) (A := (accidents H).card) (n := 2 ^ 30)
      (by norm_num),
    production_accident_tolerance hq]

end ArkLib.ProximityGap.Frontier.G136LawfulCount

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G136LawfulCount.card_lawful
#print axioms ArkLib.ProximityGap.Frontier.G136LawfulCount.card_solutions_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G136LawfulCount.rung2_anchor_iff_accidents
