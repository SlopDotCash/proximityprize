/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal

/-!
# The char-0 collision law for KKH26 subset sums (#357 S1, the unification keystone)

Three lanes of this repository hold the same mathematics in different clothes: the KKH26
bad-scalar census (`kkh26_stratified_count`: sums `λ_S = ∑_{a∈S} a` over subsets of `μ_s`),
the de Bruijn/Lam–Leung vanishing-sums classification (`LamLeungMultisetAntipodal`), and the
witness-layer balance count (`WitnessLayerCount`). This file is the **keystone of the S1
unification**: the *exact* collision law for subset sums of `2^k`-th roots of unity in
characteristic zero.

**The law** (`sum_eq_iff_freePart_eq`): for subsets `S, T` of the `2^k`-th roots,

  `∑_{z∈S} z = ∑_{z∈T} z   ⟺   freePart S = freePart T`,

where `freePart S = {z ∈ S : −z ∉ S}` is the antipodal-free part. Mechanism: antipodal
pairs inside `S` cancel (`sum_eq_sum_freePart`), and the multiset Lam–Leung classification
(`count_antipodal_of_sum_eq_zero`) shows *no other* collisions exist — the signed indicator
`1_S(z) − 1_S(−z)` is a complete invariant of the subset sum.

Consequences:
* `sum_injOn_antipodalFree` — the sum map is **injective on antipodal-free sets**: the
  engine that upgrades the in-tree stratified *lower bound* `kkh26_stratified_count` to an
  *exact census* in characteristic zero (the distinct subset-sum values over `r`-subsets
  biject with realizable free parts: `∑_j 2^{r−2j}·C(s/2, r−2j)` exactly).
* **The mod-p surplus is genuinely char-p**: the probes' measured violations of census
  exactness over `F_p` (`genlaw` falsifier: +11/+54 spurious words at `n = 64`, the O134
  surplus) are now *provably* not combinatorial — every char-0 collision is antipodal, so
  any extra `F_p` collision must come from the characteristic (`p ∣ N(λ−λ')` resultant
  arithmetic). The unification predicts the surplus mechanism, as the S1 falsifier demanded.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- [KKH26] ePrint 2026/782 Lemma 1; `KKH26StratifiedSpread.lean`;
  `LamLeungMultisetAntipodal.lean` (the O108 multiset upgrade); issue #357 (S1).
-/

set_option linter.unusedSectionVars false

open Finset BigOperators

namespace ProximityGap.KKH26CharZeroCollisionLaw

open LamLeungMultisetAntipodal

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- The antipodal-free part of a finite set: the elements whose negation is absent. -/
def freePart (S : Finset L) : Finset L := S.filter (fun z => -z ∉ S)

/-- The paired part of a finite set: the elements whose negation is also present. -/
def pairedPart (S : Finset L) : Finset L := S.filter (fun z => -z ∈ S)

theorem mem_freePart {S : Finset L} {z : L} :
    z ∈ freePart S ↔ z ∈ S ∧ -z ∉ S := by
  simp [freePart]

/-- The paired part sums to zero: it is negation-closed, and `∑ = −∑` forces `∑ = 0` in
characteristic zero. -/
theorem sum_pairedPart_eq_zero (S : Finset L) :
    ∑ z ∈ pairedPart S, z = 0 := by
  have hclosed : ∀ z : L, z ∈ pairedPart S ↔ -z ∈ pairedPart S := by
    intro z
    simp only [pairedPart, Finset.mem_filter, neg_neg]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  have hre : ∑ z ∈ pairedPart S, z = ∑ z ∈ pairedPart S, -z := by
    refine Finset.sum_equiv (Equiv.neg L) ?_ ?_
    · intro z
      simpa using hclosed z
    · intro z _
      simp [Equiv.neg_apply]
  have h2sum : (2 : L) * ∑ z ∈ pairedPart S, z = 0 := by
    have hneg : ∑ z ∈ pairedPart S, -z = -∑ z ∈ pairedPart S, z :=
      Finset.sum_neg_distrib (fun z => z)
    rw [hneg] at hre
    linear_combination hre
  rcases mul_eq_zero.mp h2sum with h | h
  · exact absurd h two_ne_zero
  · exact h

/-- **Pair cancellation:** the sum of a finite set equals the sum of its antipodal-free
part. -/
theorem sum_eq_sum_freePart (S : Finset L) :
    ∑ z ∈ S, z = ∑ z ∈ freePart S, z := by
  have hdisj : Disjoint (freePart S) (pairedPart S) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [mem_freePart] at hz
    simp only [pairedPart, Finset.mem_filter] at hz'
    exact hz.2 hz'.2
  have hsplit : freePart S ∪ pairedPart S = S := by
    ext z
    simp only [freePart, pairedPart, Finset.mem_union, Finset.mem_filter]
    by_cases h : -z ∈ S <;> simp [h]
  conv_lhs => rw [← hsplit]
  rw [Finset.sum_union hdisj, sum_pairedPart_eq_zero S, add_zero]

/-- **THE COLLISION LAW (S1 keystone).** In characteristic zero, two subsets of the
`2^k`-th roots of unity (`k ≥ 1`) have equal sums **iff** their antipodal-free parts
coincide. All collisions are antipodal-pair bookkeeping; none are arithmetic. -/
theorem sum_eq_iff_freePart_eq {k : ℕ} (hk : 1 ≤ k) {S T : Finset L}
    (hS : ∀ z ∈ S, z ^ (2 ^ k) = 1) (hT : ∀ z ∈ T, z ^ (2 ^ k) = 1) :
    ∑ z ∈ S, z = ∑ z ∈ T, z ↔ freePart S = freePart T := by
  constructor
  · -- the hard direction: Lam–Leung balance kills every non-antipodal collision
    intro hsum
    set M : Multiset L := S.val + T.val.map (fun z => -z) with hM
    have hMroots : ∀ z ∈ M, z ^ (2 ^ k) = 1 := by
      intro z hz
      rw [hM, Multiset.mem_add] at hz
      rcases hz with hz | hz
      · exact hS z hz
      · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
        have hy1 := hT y hy
        have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [h2k, pow_mul, neg_sq, ← pow_mul, ← h2k]
        exact hy1
    have hSs : S.val.sum = ∑ z ∈ S, z := by
      rw [Finset.sum_eq_multiset_sum, Multiset.map_id']
    have hTs : T.val.sum = ∑ z ∈ T, z := by
      rw [Finset.sum_eq_multiset_sum, Multiset.map_id']
    have hMsum : M.sum = 0 := by
      rw [hM, Multiset.sum_add]
      have hneg : (T.val.map (fun z => -z)).sum = -(T.val.sum) := by
        rw [← Finset.sum_eq_multiset_sum, hTs]
        exact Finset.sum_neg_distrib (fun z => z)
      rw [hneg, hSs, hTs, hsum]
      ring
    have hbal := count_antipodal_of_sum_eq_zero hMroots hMsum
    have hcount : ∀ z : L, M.count z
        = (if z ∈ S then 1 else 0) + (if -z ∈ T then 1 else 0) := by
      intro z
      rw [hM, Multiset.count_add]
      congr 1
      · by_cases h : z ∈ S
        · rw [if_pos h]
          exact Multiset.count_eq_one_of_mem S.nodup h
        · rw [if_neg h]
          exact Multiset.count_eq_zero_of_notMem h
      · have hcm : (T.val.map (fun z => -z)).count z = T.val.count (-z) := by
          have hinj : Function.Injective (fun z : L => -z) := neg_injective
          have h := Multiset.count_map_eq_count' (fun z : L => -z) T.val hinj (-z)
          simpa [neg_neg] using h
        rw [hcm]
        by_cases h : -z ∈ T
        · rw [if_pos h]
          exact Multiset.count_eq_one_of_mem T.nodup h
        · rw [if_neg h]
          exact Multiset.count_eq_zero_of_notMem h
    have hbal' : ∀ z : L,
        (if z ∈ S then 1 else 0) + (if -z ∈ T then 1 else 0)
          = (if -z ∈ S then 1 else 0) + (if z ∈ T then 1 else 0) := by
      intro z
      have h1 := hbal z
      rw [hcount z, hcount (-z), neg_neg] at h1
      omega
    ext z
    rw [mem_freePart, mem_freePart]
    have hz := hbal' z
    by_cases h1 : z ∈ S <;> by_cases h2 : -z ∈ S <;>
      by_cases h3 : z ∈ T <;> by_cases h4 : -z ∈ T <;>
      simp only [h1, h2, h3, h4, if_true, if_false, not_true, not_false_iff] at hz ⊢ <;>
      first
        | tauto
        | omega
  · -- the easy direction: pair cancellation on both sides
    intro hfree
    rw [sum_eq_sum_freePart S, sum_eq_sum_freePart T, hfree]

/-- **Injectivity on antipodal-free sets:** distinct antipodal-free subsets of the
`2^k`-th roots have distinct sums — the engine that upgrades `kkh26_stratified_count`
to an exact census in characteristic zero. -/
theorem sum_injOn_antipodalFree {k : ℕ} (hk : 1 ≤ k) {S T : Finset L}
    (hS : ∀ z ∈ S, z ^ (2 ^ k) = 1) (hT : ∀ z ∈ T, z ^ (2 ^ k) = 1)
    (hSfree : freePart S = S) (hTfree : freePart T = T)
    (hsum : ∑ z ∈ S, z = ∑ z ∈ T, z) : S = T := by
  have h := (sum_eq_iff_freePart_eq hk hS hT).mp hsum
  rwa [hSfree, hTfree] at h

/-! ## Source audit -/

#print axioms sum_pairedPart_eq_zero
#print axioms sum_eq_sum_freePart
#print axioms sum_eq_iff_freePart_eq
#print axioms sum_injOn_antipodalFree

end ProximityGap.KKH26CharZeroCollisionLaw
