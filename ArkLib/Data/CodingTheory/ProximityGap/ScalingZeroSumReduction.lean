/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CubicOrchardIdentity

/-!
# The scaling reduction for zero-sum triples on a smooth domain (#389)

The structural heart of the EXACT smooth-domain cubic list size: for a multiplicative
subgroup `G ≤ Fˣ` (a `Finset F` closed under `*` and `⁻¹`, with `0 ∉ G`), the count of
**ordered** zero-sum triples is `|G|` times a single pair count, because multiplying a
solution of `b + c = −a` by `a⁻¹` bijects it onto a solution of `b' + c' = −1`:

* **`zerosum_fiber_card_eq`** — for every `a ∈ G`, `#{(b,c)∈G² : b+c = −a} = #{(b,c)∈G² : b+c = −1}`.
* **`ordered_zerosum_sum_eq`** — `∑_{a∈G} #{(b,c)∈G² : b+c = −a} = |G| · M`,
  where the left side is exactly the ordered zero-sum triple count `T_ord`.
* **`pair_count_eq_shift`** — `M := #{(b,c)∈G² : b+c = −1} = #{y∈G : −(1+y) ∈ G}` (the
  single character-sum quantity the whole list size reduces to).

Combined with the diagonal correction and `÷6` (probe `probe_zerosum_triple_assembly.py`,
verified at 30 instances): the unordered zero-sum triple count — `= cubic_list_eq_zeroSum`'s
list size — is `(|G|·M − 3|G|·[−2∈G]) / 6`, an exact closed form on every smooth domain,
reduced to the one quantity `M` (evaluated to `(q−5)/4` on QR domains by `qr_shift_count`).
Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The scaling fiber equality**: multiplying by `a⁻¹` bijects `{b+c = −a}` onto
`{b+c = −1}` inside `G × G`, so all fibers of the ordered zero-sum count are equinumerous. -/
theorem zerosum_fiber_card_eq {G : Finset F}
    (hmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) (hinv : ∀ a ∈ G, a⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {a : F} (ha : a ∈ G) :
    ((G ×ˢ G).filter (fun p => p.1 + p.2 = -a)).card
      = ((G ×ˢ G).filter (fun p => p.1 + p.2 = -1)).card := by
  classical
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  refine Finset.card_bij'
    (fun p _ => (a⁻¹ * p.1, a⁻¹ * p.2))
    (fun p _ => (a * p.1, a * p.2))
    ?_ ?_ ?_ ?_
  · -- forward maps into the `−1` fiber
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨⟨hp1, hp2⟩, hsum⟩ := hp
    refine ⟨⟨hmul _ (hinv a ha) _ hp1, hmul _ (hinv a ha) _ hp2⟩, ?_⟩
    rw [← mul_add, hsum, mul_neg, inv_mul_cancel₀ ha0]
  · -- backward maps into the `−a` fiber
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨⟨hp1, hp2⟩, hsum⟩ := hp
    refine ⟨⟨hmul _ ha _ hp1, hmul _ ha _ hp2⟩, ?_⟩
    rw [← mul_add, hsum, mul_neg, mul_one]
  · -- left inverse
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨_, _⟩ := hp
    ext <;> simp [← mul_assoc, mul_inv_cancel₀ ha0]
  · -- right inverse
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨_, _⟩ := hp
    ext <;> simp [← mul_assoc, inv_mul_cancel₀ ha0]

open Classical in
/-- **The ordered zero-sum count factors**: `T_ord = ∑_{a∈G} #{b+c=−a} = |G| · M`. -/
theorem ordered_zerosum_sum_eq {G : Finset F}
    (hmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) (hinv : ∀ a ∈ G, a⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) :
    ∑ a ∈ G, ((G ×ˢ G).filter (fun p => p.1 + p.2 = -a)).card
      = G.card * ((G ×ˢ G).filter (fun p => p.1 + p.2 = -1)).card := by
  rw [Finset.sum_congr rfl (fun a ha => zerosum_fiber_card_eq hmul hinv h0 ha),
    Finset.sum_const, smul_eq_mul, mul_comm]

open Classical in
/-- **The pair count is the shift count**: `M = #{(b,c)∈G² : b+c=−1} = #{y∈G : −(1+y)∈G}`. -/
theorem pair_count_eq_shift {G : Finset F} :
    ((G ×ˢ G).filter (fun p => p.1 + p.2 = -1)).card
      = (G.filter (fun y => -(1 + y) ∈ G)).card := by
  classical
  refine Finset.card_bij' (fun p _ => p.1) (fun y _ => (y, -(1 + y))) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hsum⟩ := hp
    refine Finset.mem_filter.mpr ⟨hp1, ?_⟩
    rwa [show -(1 + p.1) = p.2 from by linear_combination -hsum]
  · intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyG, hsh⟩ := hy
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hyG, hsh⟩, by ring⟩
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨_, _⟩, hsum⟩ := hp
    ext
    · rfl
    · show -(1 + p.1) = p.2
      linear_combination -hsum
  · intro y hy
    rfl

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.zerosum_fiber_card_eq
#print axioms ProximityGap.PairRank.ordered_zerosum_sum_eq
#print axioms ProximityGap.PairRank.pair_count_eq_shift
