/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Loop 48 (O11 STRUCTURE) — the certain structural skeleton of the subgroup-sumset question.

Loop46/O11 reduced the §7 disproof route to one question: is the ℓ-fold distinct-subset-sumset
`|G^{(+ℓ)}|` of a smooth multiplicative subgroup `G` (order `2^m`) polynomial or super-polynomial in
`2^m` at the §7-critical `ℓ`? This loop formalizes the **certain** structural facts that sharpen that
question — it does **not** resolve it (the poly-vs-exponential dichotomy is genuine open additive
combinatorics, entangled with the `F_p`-additive dimension `ord_{2^m}(p)`; see the honesty note).

## The certain skeleton

A smooth domain has even order, so:

* **`neg_one_mem_of_even_card`**: an even-order finite multiplicative subgroup `G ≤ Fˣ` (char `≠ 2`)
  contains `-1` (Cauchy gives an order-2 element; the only order-2 element of a field's units is `-1`).
* **`neg_mem_of_even_card`**: hence `G` is **negation-closed**, `g ∈ G → -g ∈ G`, i.e. `G = -G`.
* **`subsetSum_neg_closed`**: therefore the §7 bad set — the ℓ-element subset-sums of any
  negation-closed set — is itself **negation-symmetric** (`B = -B`).

Negation symmetry is exactly what collapses the naive `2^{|G|}` subset bound: pairing `g` with `-g`,
every subset-sum is a *signed* sum `∑ ε_j t_j` (`ε_j ∈ {-1,0,1}`) over a `±`-transversal `{t_j}` of
size `|G|/2`, so `|G^{(+ℓ)}| ≤ 3^{|G|/2}`. The remaining content of O11 — whether these signed sums
further collapse to `poly(|G|)` (they live in the `F_p`-span of `G`, of dimension `ord_{2^m}(p) ≤
2^{m-2}`) or fill `≈ 3^{|G|/2}` — is **not** decided here.

## Honest status

This loop is `sorry`-free and axiom-clean. It proves the negation-symmetry skeleton, the certain
half of O11. The poly-vs-exponential resolution — the part that would actually settle whether the §7
attack disproves the prize at the minimal domain — remains **OPEN**, and is deep additive
combinatorics about subset-sums of multiplicative subgroups (cf. BCHKS §7 / Conj. 1.12). No claim is
made to have resolved it. See `DISPROOF_LOG.md` (O11).
-/

open Finset

namespace ArkLib.ProximityGap.O11StructureLoop48

variable {F : Type*} [Field F]

/-- **Even-order multiplicative subgroups contain `-1`.** A finite subgroup `G ≤ Fˣ` of even order
contains `-1`: Cauchy yields an order-2 element, and the only order-2 element of a field's unit group
is `-1`. (Holds in every characteristic; in char 2 the hypothesis is vacuous since `Fˣ`-torsion is
odd-order, and the conclusion `-1 = 1 ∈ G` is trivial.) -/
theorem neg_one_mem_of_even_card (G : Subgroup Fˣ) [Fintype G]
    (hcard : Even (Fintype.card G)) : (-1 : Fˣ) ∈ G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 hcard.two_dvd
  -- `g : G` has `orderOf g = 2`, so `(g : Fˣ)^2 = 1` and `(g : Fˣ) ≠ 1`.
  have hg2 : (g : Fˣ) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    exact_mod_cast h
  have hne : (g : Fˣ) ≠ 1 := by
    intro h
    have hg1 : g = 1 := by ext; simpa using h
    rw [hg1, orderOf_one] at hg
    exact absurd hg (by norm_num)
  -- In `F`: `(g : F)·(g : F) = 1`, so `(g : F) = 1 ∨ (g : F) = -1`; the first is excluded.
  have hgF : ((g : Fˣ) : F) ^ 2 = 1 := by
    have h2 : (((g : Fˣ) ^ 2 : Fˣ) : F) = ((1 : Fˣ) : F) := by rw [hg2]
    push_cast at h2; exact h2
  have hsq : ((g : Fˣ) : F) * ((g : Fˣ) : F) = 1 := by rw [← pow_two]; exact hgF
  rcases mul_self_eq_one_iff.mp hsq with h1 | hm1
  · exact absurd (Units.ext (by simpa using h1)) hne
  · have hg_eq : (g : Fˣ) = -1 := Units.ext (by push_cast; exact hm1)
    rw [← hg_eq]; exact g.2

/-- **Even-order multiplicative subgroups are negation-closed: `G = -G`.** Since `-1 ∈ G`, for every
`g ∈ G` we have `-g = (-1)·g ∈ G`. -/
theorem neg_mem_of_even_card (G : Subgroup Fˣ) [Fintype G]
    (hcard : Even (Fintype.card G)) {g : Fˣ} (hg : g ∈ G) : -g ∈ G := by
  have hneg1 : (-1 : Fˣ) ∈ G := neg_one_mem_of_even_card G hcard
  have : -g = (-1) * g := (neg_one_mul g).symm
  rw [this]; exact G.mul_mem hneg1 hg

/-- **The §7 bad set is negation-symmetric.** For any negation-closed finite set `S` in an additive
commutative group, the set of `ℓ`-element subset-sums is closed under negation: if `s` is a subset-sum
then so is `-s` (negate each summand; `T ↦ -T` is an `ℓ`-subset of `S` with sum `-s`). This is the
certain structural collapse behind `|G^{(+ℓ)}| ≤ 3^{|G|/2}`. -/
theorem subsetSum_neg_closed {A : Type*} [AddCommGroup A] [DecidableEq A]
    {S : Finset A} (hS : ∀ x ∈ S, -x ∈ S) (ℓ : ℕ) {s : A}
    (hs : s ∈ (S.powersetCard ℓ).image (fun T => ∑ g ∈ T, g)) :
    -s ∈ (S.powersetCard ℓ).image (fun T => ∑ g ∈ T, g) := by
  simp only [Finset.mem_image, Finset.mem_powersetCard] at hs ⊢
  obtain ⟨T, ⟨hTsub, hTcard⟩, hTsum⟩ := hs
  refine ⟨T.image (fun x => -x), ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hS y (hTsub hy)
  · rw [Finset.card_image_of_injective _ neg_injective, hTcard]
  · rw [Finset.sum_image (fun a _ b _ h => neg_injective h)]
    rw [← hTsum, ← Finset.sum_neg_distrib]

end ArkLib.ProximityGap.O11StructureLoop48

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.O11StructureLoop48.neg_one_mem_of_even_card
#print axioms ArkLib.ProximityGap.O11StructureLoop48.neg_mem_of_even_card
#print axioms ArkLib.ProximityGap.O11StructureLoop48.subsetSum_neg_closed
