/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Smooth-domain fiber counts for the power map, by pure root counting

The last elementary ingredient of the Theorem-Q chain (`QuotientPerPrimeInstantiation.md`;
companions `ValueSpreadSecondMoment.lean`, `QuotientDeepCore.lean`): on a full set `H` of
`n`-th roots of unity (`|H| = n`), the power map `x ↦ x^m` (`m ∣ n`, `n = s·m`) is exactly
`m`-to-1 onto the full set of `s`-th roots of unity. Hence the `m`-power preimage of an
`r`-subset `S` of the small domain has exactly `r·m` points — the agreement count of the
deep-quotient bad scalars.

No group theory is used: each fiber has `≤ m` elements (roots of `X^m − y`), the small domain
has `≤ s` elements (roots of `X^s − 1`), and `|H| = n = s·m` forces every inequality tight.
-/

namespace ArkLib.ProximityGap.SmoothFiberCount

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- Any fiber of the `m`-power map inside a set of field elements has at most `m` points
(`m ≥ 1`): they are roots of `X^m − C y`. -/
theorem fiber_card_le (H : Finset F) (y : F) {m : ℕ} (hm : 1 ≤ m) :
    (H.filter fun x => x ^ m = y).card ≤ m := by
  classical
  have hne : ((X : F[X]) ^ m - C y) ≠ 0 := by
    intro hz
    have hdeg := natDegree_X_pow_sub_C (n := m) (r := y)
    rw [hz] at hdeg
    simp only [natDegree_zero] at hdeg
    omega
  have hsub : (H.filter fun x => x ^ m = y) ⊆ ((X : F[X]) ^ m - C y).roots.toFinset := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨_, hxy⟩
    rw [Multiset.mem_toFinset, mem_roots hne]
    simp [IsRoot, hxy]
  calc (H.filter fun x => x ^ m = y).card
      ≤ ((X : F[X]) ^ m - C y).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card ((X : F[X]) ^ m - C y).roots := Multiset.toFinset_card_le _
    _ ≤ ((X : F[X]) ^ m - C y).natDegree := card_roots' _
    _ ≤ m := by rw [natDegree_X_pow_sub_C]

/-- **Exact fiber count on a full root-of-unity domain.** If `H` consists of `n`-th roots of
unity with `|H| = n = s·m` (`s, m ≥ 1`), then for every subset `S` of the image domain, the
`m`-power preimage has exactly `m·|S|` points, provided every element of `S` is an `s`-th root
of unity that is actually attained — which is automatic: the image of `H` is the full `s`-th
root set. We state the two halves separately. -/
theorem image_pow_eq_nthRoots (H : Finset F) {n s m : ℕ}
    (hroots : ∀ x ∈ H, x ^ n = 1) (hcard : H.card = n)
    (hnsm : n = s * m) (hs : 1 ≤ s) (hm : 1 ≤ m) :
    (H.image fun x => x ^ m) = ((X : F[X]) ^ s - 1).roots.toFinset ∧
      ∀ y ∈ H.image fun x => x ^ m, (H.filter fun x => x ^ m = y).card = m := by
  classical
  have hsne : ((X : F[X]) ^ s - 1) ≠ 0 := by
    intro hz
    have hdeg := natDegree_X_pow_sub_C (n := s) (r := (1 : F))
    rw [C_1, hz] at hdeg
    simp only [natDegree_zero] at hdeg
    omega
  -- the image lands in the s-th roots
  have himg_sub : (H.image fun x => x ^ m) ⊆ ((X : F[X]) ^ s - 1).roots.toFinset := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rw [Multiset.mem_toFinset, mem_roots hsne]
    have : (x ^ m) ^ s = 1 := by
      rw [← pow_mul, mul_comm, ← hnsm]
      exact hroots x hx
    simp [IsRoot, this]
  -- the s-th roots number at most s
  have hG_le : ((X : F[X]) ^ s - 1).roots.toFinset.card ≤ s := by
    calc ((X : F[X]) ^ s - 1).roots.toFinset.card
        ≤ Multiset.card ((X : F[X]) ^ s - 1).roots := Multiset.toFinset_card_le _
      _ ≤ ((X : F[X]) ^ s - 1).natDegree := card_roots' _
      _ ≤ s := by rw [← C_1, natDegree_X_pow_sub_C]
  -- partition |H| over the image fibers
  have hpartition : ∑ y ∈ H.image (fun x => x ^ m), (H.filter fun x => x ^ m = y).card
      = n := by
    rw [← hcard]
    exact (Finset.card_eq_sum_card_image (fun x => x ^ m) H).symm
  -- every fiber ≤ m forces ≥ s fibers, hence image = all s-th roots and each fiber = m
  have himg_ge : s ≤ (H.image fun x => x ^ m).card := by
    by_contra hlt
    push Not at hlt
    have hsum_lt : ∑ y ∈ H.image (fun x => x ^ m), (H.filter fun x => x ^ m = y).card
        < s * m := by
      calc ∑ y ∈ H.image (fun x => x ^ m), (H.filter fun x => x ^ m = y).card
          ≤ ∑ _y ∈ H.image (fun x => x ^ m), m :=
            Finset.sum_le_sum fun y _ => fiber_card_le H y hm
        _ = (H.image fun x => x ^ m).card * m := by rw [Finset.sum_const, smul_eq_mul]
        _ < s * m := by
            exact Nat.mul_lt_mul_of_lt_of_le hlt le_rfl hm
    rw [hpartition, hnsm] at hsum_lt
    exact lt_irrefl _ hsum_lt
  have himg_eq : (H.image fun x => x ^ m) = ((X : F[X]) ^ s - 1).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le himg_sub ?_
    exact hG_le.trans himg_ge
  refine ⟨himg_eq, ?_⟩
  -- tightness: if some fiber were < m, the total would fall short of n
  intro y₀ hy₀
  by_contra hne
  have hy₀_lt : (H.filter fun x => x ^ m = y₀).card < m :=
    lt_of_le_of_ne (fiber_card_le H y₀ hm) hne
  have himg_card : (H.image fun x => x ^ m).card ≤ s := himg_eq ▸ hG_le
  have hsum_lt : ∑ y ∈ H.image (fun x => x ^ m), (H.filter fun x => x ^ m = y).card
      < s * m := by
    have hsplit := Finset.add_sum_erase (H.image fun x => x ^ m)
      (fun y => (H.filter fun x => x ^ m = y).card) hy₀
    calc ∑ y ∈ H.image (fun x => x ^ m), (H.filter fun x => x ^ m = y).card
        = (H.filter fun x => x ^ m = y₀).card
            + ∑ y ∈ (H.image fun x => x ^ m).erase y₀,
                (H.filter fun x => x ^ m = y).card := hsplit.symm
      _ < m + ∑ y ∈ (H.image fun x => x ^ m).erase y₀,
                (H.filter fun x => x ^ m = y).card :=
          Nat.add_lt_add_right hy₀_lt _
      _ ≤ m + ((H.image fun x => x ^ m).erase y₀).card * m := by
          refine Nat.add_le_add_left ?_ _
          calc ∑ y ∈ (H.image fun x => x ^ m).erase y₀, (H.filter fun x => x ^ m = y).card
              ≤ ∑ _y ∈ (H.image fun x => x ^ m).erase y₀, m :=
                Finset.sum_le_sum fun y _ => fiber_card_le H y hm
            _ = ((H.image fun x => x ^ m).erase y₀).card * m := by
                rw [Finset.sum_const, smul_eq_mul]
      _ ≤ m + (s - 1) * m := by
          refine Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _
          have := Finset.card_erase_of_mem hy₀
          omega
      _ = s * m := by
          obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
          simp
          ring
  rw [hpartition, hnsm] at hsum_lt
  exact lt_irrefl _ hsum_lt

/-- **The agreement count of the deep-quotient construction.** On a full `n`-th-root domain
(`|H| = n = s·m`), the `m`-power preimage of any `S` inside the image has exactly `m·|S|`
points — the `r·m = (ρ + 1/s)·n` agreement count of Theorem Q's bad scalars. -/
theorem preimage_card_eq (H : Finset F) {n s m : ℕ}
    (hroots : ∀ x ∈ H, x ^ n = 1) (hcard : H.card = n)
    (hnsm : n = s * m) (hs : 1 ≤ s) (hm : 1 ≤ m)
    (S : Finset F) (hS : S ⊆ H.image fun x => x ^ m) :
    (H.filter fun x => x ^ m ∈ S).card = m * S.card := by
  classical
  obtain ⟨-, hfib⟩ := image_pow_eq_nthRoots H hroots hcard hnsm hs hm
  have hsplit : (H.filter fun x => x ^ m ∈ S)
      = S.biUnion fun y => H.filter fun x => x ^ m = y := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hxH, hxS⟩
      exact ⟨x ^ m, hxS, hxH, rfl⟩
    · rintro ⟨y, hyS, hxH, hxy⟩
      exact ⟨hxH, hxy ▸ hyS⟩
  rw [hsplit, Finset.card_biUnion ?disj]
  · rw [Finset.sum_congr rfl fun y hy => hfib y (hS hy), Finset.sum_const, smul_eq_mul,
      mul_comm]
  case disj =>
    intro y₁ h₁ y₂ h₂ hne
    refine Finset.disjoint_left.mpr fun x hx₁ hx₂ => hne ?_
    rcases Finset.mem_filter.mp hx₁ with ⟨-, e₁⟩
    rcases Finset.mem_filter.mp hx₂ with ⟨-, e₂⟩
    exact e₁ ▸ e₂ ▸ rfl

end ArkLib.ProximityGap.SmoothFiberCount

