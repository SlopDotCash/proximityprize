/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reindex

/-!
# BCIKS20 Appendix A.4 — the value-multiset ↔ (i₁, λ) bijection bricks (toward `RestrictedFaaDiBrunoMatch`)

This file builds the combinatorial bijection underlying `RestrictedFaaDiBrunoMatch` (P2Close.lean)
brick-by-brick, on top of the proven zero/positive-part reindex (`P2Reindex.lean`).

A value multiset `m` (a bag of `card m` orders, summing to its degree) splits canonically as
`replicate (zeroCount m) 0 + positivePart m`.  The zero entries contribute `b 0` factors (= `α₀`
powers in the assembled-series application), and the positive part is the genuine partition `λ`.
These bricks isolate the entropy-free combinatorial content; the algebraic `W`/`ξ`/`ζ` clearing and
the `B_coeff`/Y-Hasse matching are layered on later.
-/

namespace BCIKS20.HenselNumerator

open ArkLib.PowerSeriesComposition

/-- **Zero-entry product extraction.**  For any value multiset `m` and family `b : ℕ → M`, the
product `∏_{j∈m} b j` factors as `(b 0)^{(# zero entries)} · ∏_{j∈positivePart m} b j`.

In the assembled-series application (`b j = coeff j βHenselAssembled`), this peels the `α₀ = b 0`
contributions of the zero orders, leaving the genuine partition product over the positive part. -/
theorem prod_map_eq_zero_pow_mul_positivePart {M : Type*} [CommMonoid M]
    (m : Multiset ℕ) (b : ℕ → M) :
    (m.map b).prod = (b 0) ^ (zeroCount m) * ((positivePart m).map b).prod := by
  conv_lhs => rw [← replicate_zero_add_positivePart m]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]

/-- **Per-term split.**  A single weighted value-multiset term `countPerms m • ∏ b` rewrites, via
the zero/positive split, into the binomial-placement factor times the positive-part partition term:

  `countPerms m • (∏_{j∈m} b j)
     = (C(z+|λ|, z) · countPerms λ) • ((b 0)^z · ∏_{j∈λ} b j)`,  with `λ = positivePart m`, `z = zeroCount m`.

Combines `countPerms_eq_choose_zeroCount_mul_positivePart` (scalar) with
`prod_map_eq_zero_pow_mul_positivePart` (product). -/
theorem countPerms_smul_prod_split {M : Type*} [CommSemiring M]
    (m : Multiset ℕ) (b : ℕ → M) :
    (m.countPerms) • ((m.map b).prod)
      = ((zeroCount m + (positivePart m).card).choose (zeroCount m) * (positivePart m).countPerms)
          • ((b 0) ^ (zeroCount m) * ((positivePart m).map b).prod) := by
  rw [countPerms_eq_choose_zeroCount_mul_positivePart m,
    prod_map_eq_zero_pow_mul_positivePart m b]

/-- The index-list `(List.range L.length).map (L.getD · 0) = L`. -/
private theorem list_range_map_getD (L : List ℕ) :
    (List.range L.length).map (fun j => L.getD j 0) = L := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem L 0 (by simpa using h2)]

/-- **Value-multiset realizability.**  Every multiset `m` of cardinality `i` and sum `c` arises as
`valueMultiset (range i) l` for some weak composition `l ∈ finsuppAntidiag (range i) c` — i.e. it
lies in the index set of the restricted Faà-di-Bruno inner sum.  (Realize `m` by assigning its
element list to the indices `0..i-1`.)  This is the surjectivity needed for the reindex's inverse. -/
theorem mem_image_valueMultiset_of_card_sum {i c : ℕ} (m : Multiset ℕ)
    (hcard : m.card = i) (hsum : m.sum = c) :
    m ∈ (Finset.finsuppAntidiag (Finset.range i) c).image (valueMultiset (Finset.range i)) := by
  classical
  set L : List ℕ := m.toList with hL
  have hLlen : L.length = i := by rw [hL, Multiset.length_toList, hcard]
  have hsupp : ∀ j, (fun j => L.getD j 0) j ≠ 0 → j ∈ Finset.range i := by
    intro j hj
    rw [Finset.mem_range]
    by_contra hji
    exact hj (List.getD_eq_default L 0 (by omega))
  set l : ℕ →₀ ℕ := Finsupp.onFinset (Finset.range i) (fun j => L.getD j 0) hsupp with hl
  have hlapp : ∀ j ∈ Finset.range i, l j = L.getD j 0 := fun j _ => Finsupp.onFinset_apply
  -- The core fact: mapping the index list through `L.getD · 0` reconstructs `m`.
  have hmap : (Finset.range i).val.map (fun j => L.getD j 0) = m := by
    rw [Finset.range_val, ← hLlen, ← Multiset.coe_range, Multiset.map_coe, list_range_map_getD,
      hL, Multiset.coe_toList]
  refine Finset.mem_image.mpr ⟨l, ?_, ?_⟩
  · rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finsupp.support_onFinset_subset⟩
    rw [Finset.sum_congr rfl hlapp]
    show ((Finset.range i).val.map (fun j => L.getD j 0)).sum = c
    rw [hmap, hsum]
  · show (Finset.range i).val.map (fun j => l j) = m
    rw [Multiset.map_congr rfl (fun j hj => hlapp j (Finset.mem_val.mp hj)), hmap]

/-- Cardinality and sum of a realized value multiset. -/
private theorem card_sum_of_mem_image {i c : ℕ} {m : Multiset ℕ}
    (hm : m ∈ (Finset.finsuppAntidiag (Finset.range i) c).image (valueMultiset (Finset.range i))) :
    m.card = i ∧ m.sum = c := by
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hm
  rw [Finset.mem_finsuppAntidiag] at hl
  exact ⟨by rw [valueMultiset_card, Finset.card_range],
    by rw [valueMultiset_sum]; exact hl.1⟩

/-- `positivePart` of a no-zero multiset with zero-padding strips exactly the padding. -/
private theorem positivePart_add_replicate_zero (s : Multiset ℕ) (h0 : (0 : ℕ) ∉ s) (k : ℕ) :
    positivePart (s + Multiset.replicate k 0) = s := by
  have hs : s.filter (fun n => n ≠ 0) = s :=
    Multiset.filter_eq_self.mpr (fun a ha => by rintro rfl; exact h0 ha)
  have hr : (Multiset.replicate k 0).filter (fun n => n ≠ 0) = 0 :=
    Multiset.filter_eq_nil.mpr (fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; simp)
  rw [positivePart, Multiset.filter_add, hs, hr, add_zero]

/-- **Inner-sum reindex (the combinatorial heart of the bijection).**  For `T > 0`, the guarded
value-multiset inner sum re-indexes over the partitions `λ` of `c` with at most `i` parts and no
part equal to `T`:

  `∑_{m : card i, sum c} [T∉m] · countPerms m • ∏ b
     = ∑_{λ ⊢ c, |λ|≤i, T∉λ} (C(i,|λ|)·countPerms λ) • ((b 0)^{i-|λ|} · ∏_{j∈λ} b j)`.

Bijection `m ↦ positivePart m` (inverse `λ ↦ λ.parts + (i−|λ|) zeros`), with the term equality from
`countPerms_smul_prod_split` (and `zeroCount m = i − |λ|`, `C(i,zeroCount) = C(i,|λ|)`). -/
theorem innerSum_reindex {M : Type*} [CommSemiring M] (i c T : ℕ) (hT : 0 < T) (b : ℕ → M) :
    ∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) c).image (valueMultiset (Finset.range i)),
        (if T ∈ m then (0 : M) else (m.countPerms) • ((m.map b).prod))
      = ∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter
                  (fun lam => lam.parts.card ≤ i ∧ T ∉ lam.parts),
          ((i.choose lam.parts.card) * lam.parts.countPerms)
            • ((b 0) ^ (i - lam.parts.card) * (lam.parts.map b).prod) := by
  classical
  set S := (Finset.finsuppAntidiag (Finset.range i) c).image (valueMultiset (Finset.range i)) with hS
  -- guard → filter
  have hguard : (∑ m ∈ S, (if T ∈ m then (0 : M)
        else (m.countPerms) • ((m.map b).prod)))
      = ∑ m ∈ S.filter (fun m => ¬ (T ∈ m)), (m.countPerms) • ((m.map b).prod) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun m _ => by by_cases h : T ∈ m <;> simp [h])
  rw [hguard]
  refine Finset.sum_bij'
    (fun m hm => (⟨positivePart m,
        fun {n} hn => Nat.pos_of_ne_zero (fun h => zero_notMem_positivePart m (h ▸ hn)),
        by rw [positivePart_sum]
           exact (card_sum_of_mem_image (Finset.mem_filter.mp hm).1).2⟩ : Nat.Partition c))
    (fun lam _ => lam.parts + Multiset.replicate (i - lam.parts.card) 0)
    ?_ ?_ ?_ ?_ ?_
  · -- forward lands in the partition filter
    intro m hm
    obtain ⟨hmS, hmT⟩ := Finset.mem_filter.mp hm
    have hcard := (card_sum_of_mem_image hmS).1
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · -- |positivePart m| ≤ i
      have : (positivePart m).card ≤ m.card :=
        Multiset.card_le_card (Multiset.filter_le _ _)
      rw [hcard] at this; exact this
    · -- T ∉ positivePart m
      exact fun h => hmT (Multiset.mem_of_le (Multiset.filter_le _ _) h)
  · -- inverse lands in S.filter
    intro lam hlam
    obtain ⟨_, hcardle, hTnotin⟩ := Finset.mem_filter.mp hlam
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · -- λ.parts + zeros ∈ S
      apply mem_image_valueMultiset_of_card_sum
      · rw [Multiset.card_add, Multiset.card_replicate, Nat.add_sub_cancel' hcardle]
      · rw [Multiset.sum_add, Multiset.sum_replicate, smul_zero, add_zero]; exact lam.parts_sum
    · -- T ∉ λ.parts + zeros
      rw [Multiset.mem_add]
      rintro (h | h)
      · exact hTnotin h
      · exact (Nat.pos_iff_ne_zero.mp hT) (Multiset.eq_of_mem_replicate h)
  · -- left inverse: positivePart m + (i − |pp|) zeros = m
    intro m hm
    have hcard := (card_sum_of_mem_image (Finset.mem_filter.mp hm).1).1
    have hz : i - (positivePart m).card = zeroCount m := by
      rw [← hcard, ← zeroCount_add_positivePart_card m, Nat.add_sub_cancel]
    show positivePart m + Multiset.replicate (i - (positivePart m).card) 0 = m
    rw [hz, add_comm]
    exact replicate_zero_add_positivePart m
  · -- right inverse: positivePart (λ.parts + zeros) = λ  (as partitions)
    intro lam hlam
    have h0 : (0 : ℕ) ∉ lam.parts := fun h => Nat.lt_irrefl 0 (lam.parts_pos h)
    apply Nat.Partition.ext
    exact positivePart_add_replicate_zero lam.parts h0 (i - lam.parts.card)
  · -- value equality
    intro m hm
    have hcard := (card_sum_of_mem_image (Finset.mem_filter.mp hm).1).1
    have hpple : (positivePart m).card ≤ i := by
      have h := Multiset.card_le_card (Multiset.filter_le (fun n => n ≠ 0) m)
      rw [hcard] at h; exact h
    have hz : zeroCount m = i - (positivePart m).card := by
      rw [← hcard, ← zeroCount_add_positivePart_card m, Nat.add_sub_cancel]
    have hchoose : (zeroCount m + (positivePart m).card).choose (zeroCount m)
        = i.choose (positivePart m).card := by
      rw [zeroCount_add_positivePart_card, hcard, hz, Nat.choose_symm hpple]
    rw [countPerms_smul_prod_split m b, hchoose, hz]

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.prod_map_eq_zero_pow_mul_positivePart
#print axioms BCIKS20.HenselNumerator.countPerms_smul_prod_split
#print axioms BCIKS20.HenselNumerator.mem_image_valueMultiset_of_card_sum
#print axioms BCIKS20.HenselNumerator.innerSum_reindex
