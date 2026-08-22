/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumSecondMomentCollision

/-!
# Round 8 (Issue #232, ABF26) — MULTI-coordinate concentration via cosets: the strict
# generalization of Round 7's negation-symmetric construction.

Round 7 (`SubsetSumNegSymmConcentration.lean`, `negSymm_card_ge_choose`) concentrated the **first**
coordinate `e₁ = ∑ x` of the `(sum, sum-of-squares)` count `N2` to the single target `0`, with a
`q`-independent super-polynomial count `C(n/2, t)`, by using **negation-symmetric** sets
`P ∪ (−P)`. It explicitly left the **second** coordinate `e₂` (equivalently `p₂ = ∑ x²`) as the open
door — negation-symmetric families still spread `p₂` over the additive span of the pair-squares.

## What this round contributes — the coset construction concentrates `e₁, e₂, …, e_{N−1}` at once

The key observation: **negation symmetry is the `N = 2` case of a coset construction.** A
negation-symmetric set `P ∪ (−P)` is a union of cosets of the order-`2` subgroup `{±1} ≤ Fˣ`. The
general fact, proven here, is that for *any* finite multiplicative subgroup `H ≤ Fˣ` of order `N`:

  `∑_{x ∈ cH} xᵐ = cᵐ · ∑_{x ∈ H} xᵐ = 0`   for every `1 ≤ m ≤ N − 1`

(`cosetFinset_sum_pow_eq_zero`). The inner sum vanishes because `H` is the set of `N`-th roots of
unity, whose power sums `pₘ` vanish for `1 ≤ m < N` (Mathlib's `FiniteField.sum_subgroup_pow_eq_zero`,
the Newton/Vieta identity for the roots of `Xᴺ − 1`). Summed over a union of cosets, **all** the low
power sums `p₁, …, p_{N−1}` vanish simultaneously — hence (by Newton, char large) **all** the
elementary symmetric functions `e₁, …, e_{N−1}` vanish.

For `N ≥ 3` this concentrates **both** of the Round-7 `N2` coordinates `(e₁, e₂)` on the single
target `(0,0)`:

  `C(|T|, r) ≤ N2 (⋃_{c∈T} cH) (r·N) 0 0`   (`concentration_N2_choose`),

where `T` is a transversal of `r`-many disjoint cosets. This **walks through the open door Round 7
opened** — for the coset sub-family, `e₂` is concentrated too, `q`-independently. (The honest scope:
this is the **near-capacity** regime where impossibility was already known; the deep interior remains
a wall — see `Round8CosetWall.lean`, which proves the coset count collapses to polynomial there.)

The `N = 2` (order-`{±1}`) instance recovers exactly Round 7's negation-symmetric `e₁`-only result;
`N = 4` (order-`4` subgroup) concentrates `e₁, e₂, e₃`; in general order-`2ⁱ` cosets concentrate the
top `2ⁱ − 1` coordinates.

## Honest scope

* The coset power-sum vanishing and the count bound `C(|T|, r) ≤ #(target fiber)` are **exact and
  unconditional** (`sorry`-free, axiom-clean). They are a strict generalization of Round 7 to all
  coordinates `e₁, …, e_{N−1}`.
* This does **NOT** close the prize. The construction is super-polynomial only when many cosets fit
  in the agreement budget (`r` large), which forces `N` (hence the number `t = N−1` of killed power
  sums) to be small relative to `a` — the **near-capacity** regime. `Round8CosetWall.lean` formalizes
  the wall: at constant-fraction interior depth the coset count is polynomial. The deep interior
  needs *non-coset-aligned* subsets with `p₁ = … = p_t = 0`, a subgroup-restricted Weil/subset-sum
  count Mathlib cannot yet reach.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

set_option linter.style.longLine false


open Finset BigOperators

namespace ArkLib.ProximityGap.Round8CosetConcentration

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The subgroup-as-finset and its low power sums. -/

/-- The subgroup `H ≤ Fˣ`, realized as a `Finset F` via the coercion to `F`. -/
noncomputable def sgFinset (H : Subgroup Fˣ) [Fintype H] : Finset F :=
  Finset.univ.image (fun u : H => ((u : Fˣ) : F))

theorem sgFinset_card (H : Subgroup Fˣ) [Fintype H] :
    (sgFinset H).card = Fintype.card H := by
  classical
  unfold sgFinset
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    simp only at h
    exact Subtype.ext (Units.ext h)

/-- **Core power-sum vanishing for the subgroup-as-finset:** `∑_{x∈H} xᵐ = 0` for `1 ≤ m < |H|`.
The elements of `H` are the `|H|`-th roots of unity, the roots of `Xᴺ − 1`, whose power sums vanish
below the degree `N` (Newton's identity, `FiniteField.sum_subgroup_pow_eq_zero`). -/
theorem sgFinset_sum_pow_eq_zero (H : Subgroup Fˣ) [Fintype H] {m : ℕ}
    (hm : m ≠ 0) (hlt : m < Fintype.card H) :
    ∑ x ∈ sgFinset H, x ^ m = 0 := by
  classical
  unfold sgFinset
  rw [Finset.sum_image]
  · exact FiniteField.sum_subgroup_pow_eq_zero hm hlt
  · intro a _ b _ h
    simp only at h
    exact Subtype.ext (Units.ext h)

/-- A coset `c · H` (`c : Fˣ`) as a Finset of field elements. -/
noncomputable def cosetFinset (c : Fˣ) (H : Subgroup Fˣ) [Fintype H] : Finset F :=
  (sgFinset H).image (fun x => (c : F) * x)

/-- **Coset power-sum vanishing:** `∑_{x∈cH} xᵐ = cᵐ · ∑_{x∈H} xᵐ = 0` for `1 ≤ m < |H|`. Every
realized power sum of a coset of `H` (for `1 ≤ m < |H|`) is `0`: scaling factors out and the inner
subgroup sum vanishes. -/
theorem cosetFinset_sum_pow_eq_zero (c : Fˣ) (H : Subgroup Fˣ) [Fintype H] {m : ℕ}
    (hm : m ≠ 0) (hlt : m < Fintype.card H) :
    ∑ x ∈ cosetFinset c H, x ^ m = 0 := by
  classical
  unfold cosetFinset
  rw [Finset.sum_image]
  · simp_rw [mul_pow]
    rw [← Finset.mul_sum, sgFinset_sum_pow_eq_zero H hm hlt, mul_zero]
  · intro a _ b _ h
    simp only at h
    exact mul_left_cancel₀ (by exact_mod_cast c.ne_zero) h

/-! ## 2. Unions of cosets over a disjoint transversal. -/

variable (H : Subgroup Fˣ) [Fintype H]

/-- `cosetFinset c H` has card `= |H|` (the map `x ↦ c·x` is injective). -/
theorem cosetFinset_card (c : Fˣ) :
    (cosetFinset c H).card = Fintype.card H := by
  classical
  unfold cosetFinset
  rw [Finset.card_image_of_injOn, sgFinset_card]
  intro a _ b _ h
  simp only at h
  exact mul_left_cancel₀ (by exact_mod_cast c.ne_zero) h

/-- A coset is never empty: it contains `(c:F) * 1` (image of `1 ∈ H`). -/
theorem cosetFinset_nonempty (c : Fˣ) (hpos : 0 < Fintype.card H) :
    (cosetFinset c H).Nonempty := by
  rw [← Finset.card_pos, cosetFinset_card]
  exact hpos

/-- `0` is never in a coset (since `c ≠ 0` and every element of `sgFinset H` is a unit). -/
theorem zero_notMem_cosetFinset (c : Fˣ) : (0 : F) ∉ cosetFinset c H := by
  classical
  unfold cosetFinset
  rw [Finset.mem_image]
  rintro ⟨x, hx, hcx⟩
  rw [mul_eq_zero] at hcx
  rcases hcx with h | h
  · exact (by exact_mod_cast c.ne_zero : (c : F) ≠ 0) h
  · subst h
    unfold sgFinset at hx
    rw [Finset.mem_image] at hx
    obtain ⟨u, _, hu⟩ := hx
    exact (by exact_mod_cast (u : Fˣ).ne_zero : ((u : Fˣ) : F) ≠ 0) hu

variable {H}

/-- **Card of a union of cosets over a transversal subset.** If `P ⊆ T` and the cosets of `T` are
pairwise disjoint, then `|⋃_{c∈P} cH| = |P| · |H|`. -/
theorem biUnion_coset_card {T : Finset Fˣ}
    (hdisj : (T : Set Fˣ).Pairwise (fun c d => Disjoint (cosetFinset c H) (cosetFinset d H)))
    {P : Finset Fˣ} (hP : P ⊆ T) :
    (P.biUnion (fun c => cosetFinset c H)).card = P.card * Fintype.card H := by
  classical
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun c _ => cosetFinset_card H c)]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  · intro c hc d hd hcd
    exact hdisj (hP hc) (hP hd) hcd

/-- **Power-sum vanishing on a union of cosets.** For `1 ≤ m < |H|`, the union of cosets over a
pairwise-disjoint transversal subset has `∑ xᵐ = 0`. This is the multi-coordinate concentration:
*all* of `p₁, …, p_{|H|−1}` vanish on the union, hence all of `e₁, …, e_{|H|−1}`. -/
theorem biUnion_coset_sum_pow_eq_zero {T : Finset Fˣ}
    (hdisj : (T : Set Fˣ).Pairwise (fun c d => Disjoint (cosetFinset c H) (cosetFinset d H)))
    {P : Finset Fˣ} (hP : P ⊆ T) {m : ℕ} (hm : m ≠ 0) (hlt : m < Fintype.card H) :
    ∑ x ∈ P.biUnion (fun c => cosetFinset c H), x ^ m = 0 := by
  classical
  rw [Finset.sum_biUnion]
  · rw [Finset.sum_eq_zero]
    intro c _
    exact cosetFinset_sum_pow_eq_zero c H hm hlt
  · intro c hc d hd hcd
    exact hdisj (hP hc) (hP hd) hcd

/-- **Injectivity of `P ↦ ⋃_{c∈P} cH` on subsets of a pairwise-disjoint transversal.** Distinct
subsets of `T` give distinct unions (cosets are nonempty disjoint blocks: `c ∈ P` iff `cH ⊆` the
union). -/
theorem biUnion_coset_injOn {T : Finset Fˣ}
    (hdisj : (T : Set Fˣ).Pairwise (fun c d => Disjoint (cosetFinset c H) (cosetFinset d H)))
    (hpos : 0 < Fintype.card H) :
    Set.InjOn (fun P => P.biUnion (fun c => cosetFinset c H)) {P | P ⊆ T} := by
  classical
  intro P₁ hP₁ P₂ hP₂ heq
  simp only [Set.mem_setOf_eq] at hP₁ hP₂
  apply Finset.ext
  intro c
  have key : ∀ (P : Finset Fˣ), P ⊆ T → c ∈ T →
      (c ∈ P ↔ cosetFinset c H ⊆ P.biUnion (fun d => cosetFinset d H)) := by
    intro P hPsub hcT
    constructor
    · intro hcP
      exact Finset.subset_biUnion_of_mem (fun d => cosetFinset d H) hcP
    · intro hsub
      obtain ⟨y, hy⟩ := cosetFinset_nonempty H c hpos
      have hyU := hsub hy
      rw [Finset.mem_biUnion] at hyU
      obtain ⟨d, hdP, hyd⟩ := hyU
      by_contra hcP
      have hcd : c ≠ d := by
        rintro rfl; exact hcP hdP
      have hdis : Disjoint (cosetFinset c H) (cosetFinset d H) := hdisj hcT (hPsub hdP) hcd
      rw [Finset.disjoint_left] at hdis
      exact hdis hy hyd
  simp only at heq
  by_cases hcT : c ∈ T
  · rw [key P₁ hP₁ hcT, key P₂ hP₂ hcT, heq]
  · constructor
    · intro h; exact absurd (hP₁ h) hcT
    · intro h; exact absurd (hP₂ h) hcT

/-! ## 3. The headline concentration count and its `N2` form. -/

/-- **Multi-coordinate concentration count.** Let `H ≤ Fˣ` with `3 ≤ |H|` (so the first two power
sums `m = 1, 2` vanish on each coset), and `T` a transversal whose cosets are pairwise disjoint in
`F`. Then for every `r`, the number of `(r·|H|)`-subsets `S` of the union `⋃_{c∈T} cH` with both
`∑_{x∈S} x = 0` and `∑_{x∈S} x² = 0` is at least `C(|T|, r)`.

The map `P ↦ ⋃_{c∈P} cH` injects the `r`-subsets of `T` into this filtered family: each image has
card `r·|H|`, sum `0` (`m = 1 < |H|`), and sum-of-squares `0` (`m = 2 < |H|`), and the map is
injective on `r`-subsets by coset disjointness. -/
theorem concentration_count_choose {T : Finset Fˣ}
    (hdisj : (T : Set Fˣ).Pairwise (fun c d => Disjoint (cosetFinset c H) (cosetFinset d H)))
    (hcard : 3 ≤ Fintype.card H) (r : ℕ) :
    T.card.choose r ≤
      (((T.biUnion (fun c => cosetFinset c H)).powersetCard (r * Fintype.card H)).filter
        (fun S => (∑ x ∈ S, x = 0) ∧ (∑ x ∈ S, x ^ 2 = 0))).card := by
  classical
  have hpos : 0 < Fintype.card H := by omega
  rw [← Finset.card_powersetCard r T]
  apply Finset.card_le_card_of_injOn (fun P => P.biUnion (fun c => cosetFinset c H))
  · intro P hP
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hP
    obtain ⟨hPsub, hPcard⟩ := hP
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact Finset.biUnion_subset_biUnion_of_subset_left _ hPsub
    · rw [biUnion_coset_card hdisj hPsub, hPcard]
    · have := biUnion_coset_sum_pow_eq_zero hdisj hPsub (m := 1) (by norm_num) (by omega)
      simpa using this
    · exact biUnion_coset_sum_pow_eq_zero hdisj hPsub (m := 2) (by norm_num) (by omega)
  · intro P₁ hP₁ P₂ hP₂ heq
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hP₁ hP₂
    exact biUnion_coset_injOn hdisj hpos
      (Set.mem_setOf_eq ▸ hP₁.1) (Set.mem_setOf_eq ▸ hP₂.1) heq

/-- **The concentration count in Round-7 `N2` form.** With the same hypotheses, the Round-7
`(sum, sum-of-squares)` fiber count `N2` of the coset-union ground set `U = ⋃_{c∈T} cH`, at agreement
`r·|H|` and the **single** target `(c₁, c₂) = (0, 0)`, satisfies

  `C(|T|, r) ≤ N2 U (r·|H|) 0 0`.

This is the strict strengthening of Round 7's `negSymm_card_ge_choose`: that result concentrated only
the first coordinate `e₁`; here **both** coordinates `(e₁, e₂)` are concentrated on the single target
`(0,0)`, `q`-independently, with the field-independent super-polynomial count `C(|T|, r)`. -/
theorem concentration_N2_choose {T : Finset Fˣ}
    (hdisj : (T : Set Fˣ).Pairwise (fun c d => Disjoint (cosetFinset c H) (cosetFinset d H)))
    (hcard : 3 ≤ Fintype.card H) (r : ℕ) :
    T.card.choose r ≤
      Round7SecondMoment.N2 (T.biUnion (fun c => cosetFinset c H)) (r * Fintype.card H) 0 0 := by
  simpa only [Round7SecondMoment.N2] using concentration_count_choose hdisj hcard r

end ArkLib.ProximityGap.Round8CosetConcentration

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round8CosetConcentration.sgFinset_sum_pow_eq_zero
#print axioms ArkLib.ProximityGap.Round8CosetConcentration.cosetFinset_sum_pow_eq_zero
#print axioms ArkLib.ProximityGap.Round8CosetConcentration.biUnion_coset_sum_pow_eq_zero
#print axioms ArkLib.ProximityGap.Round8CosetConcentration.concentration_count_choose
#print axioms ArkLib.ProximityGap.Round8CosetConcentration.concentration_N2_choose
