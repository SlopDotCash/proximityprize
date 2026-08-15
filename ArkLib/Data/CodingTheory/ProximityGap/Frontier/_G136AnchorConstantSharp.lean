/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G135CensusToSupBound

/-!
# G136 (part 0): the anchor constant `3` is sharp — the zero-sum plane lower bound

The cyclotomic accident reduction identifies the rung-2 anchor constant: beyond the two
diagonal families `(x,y;x,y)`, `(x,y;y,x)`, every negation-closed set carries the zero-sum
plane `(x,−x;z,−z)`.  This file proves the unconditional lower bound

```text
3·#G² − 3·#G ≤ E₂(G)      (G negation-closed, 0 ∉ G, 2 ≠ 0 in F)
```

by exhibiting the three families as pairwise disjoint subsets of the equal-sum pair set.
Consequently the rung-2 anchor `q·E₂ ≤ 3·q·n² + n⁴` is TIGHT: no constant below `3` can
work for the production subgroup (`−1 ∈ μ_{2^30}`), and the accident-free value
`E₂ = 3n² − 3n` is the exact minimum.

**Honest scope.**  Lower bound only; the anchor upper bound is the wall.  CORE remains
OPEN.  Issue #466 (G136 lane).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G136AnchorConstantSharp

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem vec_eq_iff {a b c d : F} :
    (![a, b] : Fin 2 → F) = ![c, d] ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem mem_pi2 {x y : F} {G : Finset F} (hx : x ∈ G) (hy : y ∈ G) :
    (![x, y] : Fin 2 → F) ∈ Fintype.piFinset (fun _ : Fin 2 => G) := by
  refine Fintype.mem_piFinset.mpr (fun i => ?_)
  fin_cases i
  · simpa using hx
  · simpa using hy

private theorem sum_pair (a b : F) : ∑ i, (![a, b] : Fin 2 → F) i = a + b := by
  simp [Fin.sum_univ_two]

/-- The identity family `(x,y; x,y)`. -/
noncomputable def famId (G : Finset F) : Finset ((Fin 2 → F) × (Fin 2 → F)) :=
  (G ×ˢ G).image (fun xy => (![xy.1, xy.2], ![xy.1, xy.2]))

/-- The swap family `(x,y; y,x)`, `x ≠ y`. -/
noncomputable def famSwap (G : Finset F) : Finset ((Fin 2 → F) × (Fin 2 → F)) :=
  ((G ×ˢ G).filter (fun xy => xy.1 ≠ xy.2)).image
    (fun xy => (![xy.1, xy.2], ![xy.2, xy.1]))

/-- The zero-sum family `(x,−x; z,−z)`, `z ∉ {x, −x}`. -/
noncomputable def famZero (G : Finset F) : Finset ((Fin 2 → F) × (Fin 2 → F)) :=
  ((G ×ˢ G).filter (fun xz => xz.2 ≠ xz.1 ∧ xz.2 ≠ -xz.1)).image
    (fun xz => (![xz.1, -xz.1], ![xz.2, -xz.2]))

theorem famId_subset (G : Finset F) : famId G ⊆ energySet G 2 := by
  intro y hy
  obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hy
  have h := Finset.mem_product.mp hxy
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨mem_pi2 h.1 h.2, mem_pi2 h.1 h.2⟩, rfl⟩

theorem famSwap_subset (G : Finset F) : famSwap G ⊆ energySet G 2 := by
  intro y hy
  obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hy
  have h := Finset.mem_product.mp (Finset.mem_filter.mp hxy).1
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨mem_pi2 h.1 h.2, mem_pi2 h.2 h.1⟩, ?_⟩
  rw [sum_pair, sum_pair]
  exact add_comm _ _

theorem famZero_subset (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G) :
    famZero G ⊆ energySet G 2 := by
  intro y hy
  obtain ⟨xz, hxz, rfl⟩ := Finset.mem_image.mp hy
  have h := Finset.mem_product.mp (Finset.mem_filter.mp hxz).1
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr
      ⟨mem_pi2 h.1 (hneg _ h.1), mem_pi2 h.2 (hneg _ h.2)⟩, ?_⟩
  rw [sum_pair, sum_pair]
  ring

theorem card_famId (G : Finset F) : (famId G).card = G.card ^ 2 := by
  unfold famId
  rw [Finset.card_image_of_injOn, Finset.card_product, sq]
  intro a _ b _ hab
  have h1 := (vec_eq_iff.mp (congrArg Prod.fst hab)).1
  have h2 := (vec_eq_iff.mp (congrArg Prod.fst hab)).2
  exact Prod.ext h1 h2

theorem card_famSwap (G : Finset F) : (famSwap G).card = G.card ^ 2 - G.card := by
  unfold famSwap
  rw [Finset.card_image_of_injOn]
  · -- card of the off-diagonal filter
    have hdiag : ((G ×ˢ G).filter (fun xy => xy.1 = xy.2)).card = G.card := by
      rw [show (G ×ˢ G).filter (fun xy => xy.1 = xy.2)
          = G.image (fun x => (x, x)) by
        ext xy
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
        constructor
        · rintro ⟨⟨h1, _⟩, heq⟩
          exact ⟨xy.1, h1, Prod.ext rfl heq⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨hx, hx⟩, rfl⟩]
      rw [Finset.card_image_of_injOn]
      intro a _ b _ hab
      exact (Prod.ext_iff.mp hab).1
    have htot := Finset.card_filter_add_card_filter_not
      (s := G ×ˢ G) (p := fun xy => xy.1 = xy.2)
    rw [Finset.card_product] at htot
    rw [sq]
    simp only [ne_eq]
    omega
  · intro a _ b _ hab
    have h1 := (vec_eq_iff.mp (congrArg Prod.fst hab)).1
    have h2 := (vec_eq_iff.mp (congrArg Prod.fst hab)).2
    exact Prod.ext h1 h2

theorem card_famZero (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G)
    (h0 : (0 : F) ∉ G) (h2 : (2 : F) ≠ 0) :
    (famZero G).card = G.card ^ 2 - 2 * G.card := by
  unfold famZero
  rw [Finset.card_image_of_injOn]
  · have hexp : (G ×ˢ G).filter (fun xz => xz.2 ≠ xz.1 ∧ xz.2 ≠ -xz.1)
        = G.biUnion (fun x => (G.filter (fun z => z ≠ x ∧ z ≠ -x)).image
            (Prod.mk x)) := by
      ext xz
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨hx, hz⟩, hc⟩
        exact ⟨xz.1, hx, xz.2, ⟨hz, hc⟩, rfl⟩
      · rintro ⟨x, hx, z, ⟨hz, hc⟩, rfl⟩
        exact ⟨⟨hx, hz⟩, hc⟩
    rw [hexp, Finset.card_biUnion]
    · have hper : ∀ x ∈ G,
          ((G.filter (fun z => z ≠ x ∧ z ≠ -x)).image (Prod.mk x)).card
            = G.card - 2 := by
        intro x hx
        rw [Finset.card_image_of_injOn (fun a _ b _ hab =>
          (Prod.ext_iff.mp hab).2)]
        have hxx : -x ≠ x := by
          intro h
          apply h0
          have h2x : x + x = 0 := by
            nth_rewrite 2 [← h]
            exact add_neg_cancel x
          have hmul : (2 : F) * x = 0 := by
            rw [two_mul]
            exact h2x
          rcases mul_eq_zero.mp hmul with hc | hc
          · exact absurd hc h2
          · rwa [hc] at hx
        have hset : G.filter (fun z => z ≠ x ∧ z ≠ -x)
            = G \ ({x, -x} : Finset F) := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        have hsub : ({x, -x} : Finset F) ⊆ G := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hx
          · exact hneg _ hx
        rw [hset, Finset.card_sdiff]
        congr 1
        rw [Finset.inter_eq_left.mpr hsub,
          Finset.card_insert_of_notMem
            (by simpa using fun h => hxx h.symm), Finset.card_singleton]
      rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul,
        Nat.mul_sub, sq, Nat.mul_comm G.card 2]
    · intro a _ b hb hab
      apply Finset.disjoint_left.mpr
      intro xz hxa hxb
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hxa
      obtain ⟨_, _, hbeq⟩ := Finset.mem_image.mp hxb
      exact hab ((Prod.ext_iff.mp hbeq).1.symm)
  · intro a _ b _ hab
    have h1 := (vec_eq_iff.mp (congrArg Prod.fst hab)).1
    have h2' := (vec_eq_iff.mp (congrArg Prod.snd hab)).1
    exact Prod.ext h1 h2'

/-- Pairwise disjointness of the three families. -/
theorem famId_disjoint_famSwap (G : Finset F) :
    Disjoint (famId G) (famSwap G) := by
  apply Finset.disjoint_left.mpr
  intro y hy1 hy2
  obtain ⟨xy, _, rfl⟩ := Finset.mem_image.mp hy1
  obtain ⟨ab, hab, heq⟩ := Finset.mem_image.mp hy2
  have hne := (Finset.mem_filter.mp hab).2
  have h1 := vec_eq_iff.mp (congrArg Prod.fst heq)
  have h2 := vec_eq_iff.mp (congrArg Prod.snd heq)
  exact hne (h1.1.trans h2.1.symm)

theorem famZero_disjoint_famId (G : Finset F) :
    Disjoint (famZero G) (famId G) := by
  apply Finset.disjoint_left.mpr
  intro y hy1 hy2
  obtain ⟨xz, hxz, rfl⟩ := Finset.mem_image.mp hy1
  obtain ⟨ab, _, heq⟩ := Finset.mem_image.mp hy2
  have hc := (Finset.mem_filter.mp hxz).2
  have h1 := vec_eq_iff.mp (congrArg Prod.fst heq)
  have h2 := vec_eq_iff.mp (congrArg Prod.snd heq)
  -- famId: v = w, so ![x,−x] = ![z,−z], giving z = x — excluded
  exact hc.1 (h2.1.symm.trans h1.1)

theorem famZero_disjoint_famSwap (G : Finset F) :
    Disjoint (famZero G) (famSwap G) := by
  apply Finset.disjoint_left.mpr
  intro y hy1 hy2
  obtain ⟨xz, hxz, rfl⟩ := Finset.mem_image.mp hy1
  obtain ⟨ab, _, heq⟩ := Finset.mem_image.mp hy2
  have hc := (Finset.mem_filter.mp hxz).2
  have h1 := vec_eq_iff.mp (congrArg Prod.fst heq)
  have h2 := vec_eq_iff.mp (congrArg Prod.snd heq)
  -- famSwap: v = ![a,b], w = ![b,a]; v = ![x,−x] gives a = x, b = −x;
  -- w = ![z,−z] gives z = b = −x — excluded
  exact hc.2 (h2.1.symm.trans h1.2)

/-- **The anchor constant `3` is sharp**: every negation-closed set away from `0` and `2`
carries at least `3·#G² − 3·#G` equal-sum pairs at rung `2`. -/
theorem three_sq_sub_three_le_addREnergy (G : Finset F)
    (hneg : ∀ x ∈ G, -x ∈ G) (h0 : (0 : F) ∉ G) (h2 : (2 : F) ≠ 0) :
    3 * G.card ^ 2 - 3 * G.card ≤ Finset.addREnergy 2 G := by
  have hsub : (famId G ∪ famSwap G) ∪ famZero G ⊆ energySet G 2 := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact famId_subset G hy
      · exact famSwap_subset G hy
    · exact famZero_subset G hneg hy
  have hd1 : Disjoint (famId G ∪ famSwap G) (famZero G) := by
    rw [Finset.disjoint_union_left]
    exact ⟨(famZero_disjoint_famId G).symm, (famZero_disjoint_famSwap G).symm⟩
  have hcard : ((famId G ∪ famSwap G) ∪ famZero G).card
      = G.card ^ 2 + (G.card ^ 2 - G.card) + (G.card ^ 2 - 2 * G.card) := by
    rw [Finset.card_union_of_disjoint hd1,
      Finset.card_union_of_disjoint (famId_disjoint_famSwap G),
      card_famId, card_famSwap, card_famZero G hneg h0 h2]
  have hle : ((famId G ∪ famSwap G) ∪ famZero G).card ≤ Finset.addREnergy 2 G := by
    rw [← card_energySet]
    exact Finset.card_le_card hsub
  have hn : G.card ≤ G.card ^ 2 := by
    rcases Nat.eq_zero_or_pos G.card with h | h
    · simp [h]
    · calc
        G.card = G.card * 1 := (Nat.mul_one _).symm
        _ ≤ G.card * G.card := Nat.mul_le_mul_left _ h
        _ = G.card ^ 2 := (sq G.card).symm
  omega

/-- **Coefficient-two anchor budgets are impossible at production size.**  The zero-sum
plane lower bound alone already forces the rung-2 energy strictly above a coefficient-`2`
Wick budget plus the full `n^4` DC allowance, for every `q ≥ 2^158` and `#G = 2^30`. -/
theorem coefficient_two_budget_fails_at_production (G : Finset F)
    (hneg : ∀ x ∈ G, -x ∈ G) (h0 : (0 : F) ∉ G) (h2 : (2 : F) ≠ 0)
    (hcard : G.card = 2 ^ 30) {q : ℕ} (hq : 2 ^ 158 ≤ q) :
    q * (2 * G.card ^ 2) + G.card ^ 4 < q * Finset.addREnergy 2 G := by
  have hlow := three_sq_sub_three_le_addREnergy G hneg h0 h2
  have hmul : q * (3 * G.card ^ 2 - 3 * G.card) ≤ q * Finset.addREnergy 2 G :=
    Nat.mul_le_mul_left q hlow
  have hstrict : q * (2 * G.card ^ 2) + G.card ^ 4
      < q * (3 * G.card ^ 2 - 3 * G.card) := by
    rw [hcard]
    have hgap : (2 ^ 30 : ℕ) ^ 4
        < q * ((2 ^ 30 : ℕ) ^ 2 - 3 * (2 ^ 30 : ℕ)) := by
      calc
        (2 ^ 30 : ℕ) ^ 4 < 2 ^ 158 := by norm_num
        _ ≤ q := hq
        _ = q * 1 := by rw [Nat.mul_one]
        _ ≤ q * ((2 ^ 30 : ℕ) ^ 2 - 3 * (2 ^ 30 : ℕ)) := by
          exact Nat.mul_le_mul_left q (by norm_num)
    calc
      q * (2 * (2 ^ 30 : ℕ) ^ 2) + (2 ^ 30 : ℕ) ^ 4
          < q * (2 * (2 ^ 30 : ℕ) ^ 2)
              + q * ((2 ^ 30 : ℕ) ^ 2 - 3 * (2 ^ 30 : ℕ)) := by
        exact Nat.add_lt_add_left hgap _
      _ = q * (3 * (2 ^ 30 : ℕ) ^ 2 - 3 * (2 ^ 30 : ℕ)) := by
        ring_nf
  exact lt_of_lt_of_le hstrict hmul

end ArkLib.ProximityGap.Frontier.G136AnchorConstantSharp

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G136AnchorConstantSharp.card_famId
#print axioms ArkLib.ProximityGap.Frontier.G136AnchorConstantSharp.card_famSwap
#print axioms ArkLib.ProximityGap.Frontier.G136AnchorConstantSharp.card_famZero
#print axioms
  ArkLib.ProximityGap.Frontier.G136AnchorConstantSharp.three_sq_sub_three_le_addREnergy
#print axioms
  ArkLib.ProximityGap.Frontier.G136AnchorConstantSharp.coefficient_two_budget_fails_at_production
