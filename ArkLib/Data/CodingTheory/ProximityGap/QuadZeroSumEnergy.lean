/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AddEnergyGroupRepBound

/-!
# The 4-term zero-sum count equals additive energy for symmetric sets (#389)

For the cubic (`k = 2`) supply ceiling the in-tree bridge is the Cauchy–Schwarz
inequality `T(G)² ≤ |G|·E(G)` (`zeroSumTriples_sq_le_card_energy_viaCoset`), where
`T(G) = #{(a,b,c) ∈ G³ : a+b+c = 0}` is the 3-term zero-sum count.  The *next* rate
(`k = 3`) supply object is the **4-term** zero-sum count
`Q(G) = #{((a,b),(c,d)) : a+b+c+d = 0}`.  Unlike the cubic case, this one is pinned
**exactly** — no Cauchy–Schwarz loss — for any set closed under negation:

> **`quadZeroSum_eq_additiveEnergy`** — if `−G = G` (every prize NTT subgroup `μ_n`
> with `n` even is symmetric, since `−1 = μ_n`'s order-2 element), then `Q(G) = E(G)`.

The proof is a reindexing: `E(G) = #{((a,b),(c,d)) : a+b = c+d}` (the standard energy
set); negating the second pair (a bijection of `(G×G)²`, using `−G = G`) turns the
condition `a+b = c+d` into `a+b+(−c)+(−d) = 0`.  Combined with the in-tree exact energy
`E(μ_n) = 3n²−3n` (`AdditiveEnergyCharacterization`, unconditional for `p > 2^n`) this
yields the **exact** 4-term supply value `Q(μ_n) = 3n²−3n`, the equality endpoint that
the cubic bridge only bounds.

Honest scope: an exact additive-combinatorics identity feeding the supply side of the
program.  It does not by itself pin `δ*` — the success-side interleaved list bound
remains the open beyond-Johnson question.  Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.AddEnergyGroupRepBound

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The ordered 4-term zero-sum count over pairs: `#{((a,b),(c,d)) ∈ (S×S)² : a+b+c+d = 0}`. -/
def quadZeroSum (S : Finset G) : ℕ :=
  (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
    (fun q => q.1.1 + q.1.2 + q.2.1 + q.2.2 = 0)).card

/-- The standard additive-energy set `{((a,b),(c,d)) ∈ (S×S)² : a+b = c+d}`. -/
def energyQuad (S : Finset G) : ℕ :=
  (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
    (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card

/-- Collapse a filtered product card into a sum of fiber cards over the left factor. -/
theorem card_filter_product_left {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (P' : Finset β) (f : α → β → Prop) [∀ a b, Decidable (f a b)] :
    ((P ×ˢ P').filter (fun z => f z.1 z.2)).card
      = ∑ a ∈ P, (P'.filter (fun b => f a b)).card := by
  classical
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.card_filter]

/-- `repCount S (a+b) = #{(c,d) ∈ S² : c+d = a+b}` — each `y ∈ S` with `(a+b)−y ∈ S`
pairs with `z := (a+b)−y ∈ S`. -/
theorem repCount_add_eq_pairCard (S : Finset G) (a b : G) :
    repCount S (a + b)
      = ((S ×ˢ S).filter (fun p => p.1 + p.2 = a + b)).card := by
  classical
  unfold repCount
  refine Finset.card_nbij' (fun y => (y, a + b - y)) (fun p => p.1) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy
    obtain ⟨hyS, hzS⟩ := hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hyS, hzS⟩, by abel⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hsum⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨h1, ?_⟩
    have hz : a + b - p.1 = p.2 := by rw [← hsum]; abel
    rw [hz]; exact h2
  · intro y hy; rfl
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨_, _⟩, hsum⟩ := hp
    have hz : a + b - p.1 = p.2 := by rw [← hsum]; abel
    ext <;> simp [hz]

/-- **The additive energy equals the energy-quad count** `#{((a,b),(c,d)) : a+b = c+d}`. -/
theorem additiveEnergy_eq_energyQuad (S : Finset G) :
    additiveEnergy S = energyQuad S := by
  classical
  unfold additiveEnergy energyQuad
  rw [card_filter_product_left (S ×ˢ S) (S ×ˢ S) (fun p q => p.1 + p.2 = q.1 + q.2)]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [repCount_add_eq_pairCard S a b]
  -- both sides: #{(c,d)∈S²: c+d = a+b}, modulo orientation of the equality
  refine Finset.card_nbij' id id ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, id_eq] at hp ⊢
    exact ⟨hp.1, hp.2.symm⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, id_eq] at hp ⊢
    exact ⟨hp.1, hp.2.symm⟩

/-- **The 4-term zero-sum count equals additive energy for symmetric sets.**  If
`−S = S` (e.g. any even-order NTT subgroup `μ_n`), then `Q(S) = E(S)`. -/
theorem quadZeroSum_eq_additiveEnergy (S : Finset G) (hsym : ∀ x ∈ S, -x ∈ S) :
    quadZeroSum S = additiveEnergy S := by
  classical
  rw [additiveEnergy_eq_energyQuad]
  unfold quadZeroSum energyQuad
  -- bijection: negate the second pair ((a,b),(c,d)) ↦ ((a,b),(-c,-d))
  refine Finset.card_nbij'
    (fun q => (q.1, (-q.2.1, -q.2.2)))
    (fun q => (q.1, (-q.2.1, -q.2.2))) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq ⊢
    obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, hsum⟩ := hq
    refine ⟨⟨⟨ha, hb⟩, hsym _ hc, hsym _ hd⟩, ?_⟩
    -- a+b+c+d=0  ⟹  a+b = -c + -d
    have : q.1.1 + q.1.2 = -q.2.1 + -q.2.2 := by
      rw [← sub_eq_zero, ← hsum]; abel
    exact this
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq ⊢
    obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, hsum⟩ := hq
    refine ⟨⟨⟨ha, hb⟩, hsym _ hc, hsym _ hd⟩, ?_⟩
    -- a+b = c+d  ⟹  a+b + -c + -d = 0
    have : q.1.1 + q.1.2 + -q.2.1 + -q.2.2 = 0 := by
      rw [hsum]; abel
    exact this
  · intro q _
    simp only [neg_neg, Prod.mk.eta]
  · intro q _
    simp only [neg_neg, Prod.mk.eta]

/-- The clean symmetric-set statement: `#{((a,b),(c,d)) : a+b+c+d=0} = E(S)`. -/
theorem quadZeroSum_eq_energy_symm (S : Finset G) (hsym : ∀ x ∈ S, -x ∈ S) :
    quadZeroSum S = additiveEnergy S :=
  quadZeroSum_eq_additiveEnergy S hsym

end ArkLib.ProximityGap.AddEnergyGroupRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AddEnergyGroupRepBound.quadZeroSum_eq_additiveEnergy
