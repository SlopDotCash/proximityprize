/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.A5CensusValue
import ArkLib.Data.CodingTheory.ProximityGap.CosetAugmentation

/-!
# Coset stripping: removing a contained coset preserves qualification and census value

Campaign #357. The executable form of the coset augmentation law at the exponent level:

> **`strip_coset`** — if a qualifying exponent set's reduction contains a full coset
> `{x, x+q, x+h, x+q+h}` of the order-4 subgroup, then removing the four preimages yields
> a qualifying set of size `|A| − 4` with the **same census value** (the coset's four
> `g`-powers cancel pairwise) — for every prime and every primitive root at once.

Iterating this step under the (named, probe-true) *contains-a-coset* hypothesis collapses
every `a ≡ 0 (mod 4)` row of the depth-1 census table onto the `a = 4` row — the
conditional half of the measured `census(8) = census(4) = (n/2−1)²` duality, with the
hypothesis reduced (issue thread) to a scale-uniform ℤ[i]-collision case analysis.

## References

* Probes `probe_8set_coset_structure.py`, `probe_coset_core_conjecture.py`; issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.WindowTwoLayer

variable {m : ℕ}

/-- **Coset stripping.** Removing the preimages of a contained coset from a qualifying
exponent set preserves qualification, drops the size by four, and preserves the census
value at every prime simultaneously. -/
theorem strip_coset (hm : 2 ≤ m) {A : Finset ℕ} (hsub : A ⊆ Finset.range (2 ^ m))
    (hzero : e2Folded m A = 0) {x : ZMod (2 ^ m)}
    (hx : x ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)))
    (hxq : x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
      ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)))
    (hxh : x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
      ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)))
    (hxqh : x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
      ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))) :
    ∃ A' : Finset ℕ, A' ⊆ Finset.range (2 ^ m) ∧ A'.card + 4 = A.card ∧
      e2Folded m A' = 0 ∧
      ∀ {p : ℕ} [Fact p.Prime] (g : ZMod p), IsPrimitiveRoot g (2 ^ m) →
        ∑ i ∈ A, g ^ i = ∑ i ∈ A', g ^ i := by
  classical
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hm1 : 1 ≤ m := by omega
  -- abbreviations for the two generators
  set cq : ZMod (2 ^ m) := ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) with hcq
  set ch : ZMod (2 ^ m) := ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) with hch
  -- the subgroup facts
  have hQQ : 2 ^ (m - 2) + 2 ^ (m - 2) = 2 ^ (m - 1) := by
    have h := pow_succ 2 (m - 2)
    rw [show m - 2 + 1 = m - 1 by omega] at h
    omega
  have hqq : cq + cq = ch := by rw [hcq, hch, ← Nat.cast_add, hQQ]
  have hh2 : ch + ch = 0 := by rw [hch]; exact zmod_half_add_half hm1
  -- the four coset offsets are pairwise distinct
  have hvals : ∀ k : ℕ, 0 < k → k < 2 ^ m → ((k : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
    intro k h0 hk hc
    rw [ZMod.natCast_eq_zero_iff] at hc
    exact absurd (Nat.le_of_dvd h0 hc) (by omega)
  have hQH : 2 ^ (m - 2) < 2 ^ (m - 1) ∧ 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m :=
    ⟨Nat.pow_lt_pow_right (by norm_num) (by omega), by
      have h := pow_succ 2 (m - 1)
      rw [Nat.sub_add_cancel hm1] at h
      omega⟩
  obtain ⟨hQltH, hHH⟩ := hQH
  have hqne : cq ≠ 0 := hvals _ (pow_pos (by norm_num) _) (by omega)
  have hhne : ch ≠ 0 := hvals _ (pow_pos (by norm_num) _) (by omega)
  have hqhne : cq + ch ≠ 0 := by
    rw [hcq, hch, ← Nat.cast_add]
    exact hvals _ (by positivity) (by omega)
  have hqh : cq ≠ ch := by
    intro hc
    rw [hcq, hch] at hc
    have := congrArg ZMod.val hc
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  -- extract the four distinct preimages
  have hpre : ∀ {y : ZMod (2 ^ m)},
      y ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) → ∃ i ∈ A, ((i : ℕ) : ZMod (2 ^ m)) = y :=
    fun hy => by
      obtain ⟨i, hi, hcast⟩ := Multiset.mem_map.mp hy
      exact ⟨i, hi, hcast⟩
  obtain ⟨i₁, hi₁, hc₁⟩ := hpre hx
  obtain ⟨i₂, hi₂, hc₂⟩ := hpre hxq
  obtain ⟨i₃, hi₃, hc₃⟩ := hpre hxh
  obtain ⟨i₄, hi₄, hc₄⟩ := hpre hxqh
  -- pairwise distinct preimages (their casts differ)
  have n12 : i₁ ≠ i₂ := fun hc => hqne (by
    have hcast := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
    linear_combination hc₁ - hc₂ - hcast)
  have n13 : i₁ ≠ i₃ := fun hc => hhne (by
    have hcast := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
    linear_combination hc₁ - hc₃ - hcast)
  have n14 : i₁ ≠ i₄ := fun hc => hqhne (by
    have hcast := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
    linear_combination hc₁ - hc₄ - hcast)
  have n23 : i₂ ≠ i₃ := fun hc => hqh (by
    have hcast := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
    linear_combination -hc₂ + hc₃ + hcast)
  have n24 : i₂ ≠ i₄ := fun hc => hhne (by
    have hcast := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
    linear_combination hc₂ - hc₄ - hcast)
  have n34 : i₃ ≠ i₄ := fun hc => hqne (by
    have hcast := congrArg (Nat.cast : ℕ → ZMod (2 ^ m)) hc
    linear_combination hc₃ - hc₄ - hcast)
  -- the stripped set
  set A' : Finset ℕ := (((A.erase i₁).erase i₂).erase i₃).erase i₄ with hA'
  have hmem₂ : i₂ ∈ A.erase i₁ := Finset.mem_erase.mpr ⟨Ne.symm n12, hi₂⟩
  have hmem₃ : i₃ ∈ (A.erase i₁).erase i₂ :=
    Finset.mem_erase.mpr ⟨Ne.symm n23, Finset.mem_erase.mpr ⟨Ne.symm n13, hi₃⟩⟩
  have hmem₄ : i₄ ∈ ((A.erase i₁).erase i₂).erase i₃ :=
    Finset.mem_erase.mpr ⟨Ne.symm n34, Finset.mem_erase.mpr
      ⟨Ne.symm n24, Finset.mem_erase.mpr ⟨Ne.symm n14, hi₄⟩⟩⟩
  -- multiset-level memberships
  have hm₁ : i₁ ∈ A.val := hi₁
  have hm₂ : i₂ ∈ A.val.erase i₁ := by
    have := hmem₂
    rwa [Finset.mem_def, Finset.erase_val] at this
  have hm₃ : i₃ ∈ (A.val.erase i₁).erase i₂ := by
    have := hmem₃
    rwa [Finset.mem_def, Finset.erase_val, Finset.erase_val] at this
  have hm₄ : i₄ ∈ ((A.val.erase i₁).erase i₂).erase i₃ := by
    have := hmem₄
    rwa [Finset.mem_def, Finset.erase_val, Finset.erase_val, Finset.erase_val] at this
  -- the val decomposition
  have hval : A.val = i₁ ::ₘ i₂ ::ₘ i₃ ::ₘ i₄ ::ₘ A'.val := by
    rw [hA']
    simp only [Finset.erase_val]
    rw [Multiset.cons_erase hm₄, Multiset.cons_erase hm₃, Multiset.cons_erase hm₂,
      Multiset.cons_erase hm₁]
  have hmap : A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))
      = x ::ₘ (x + cq) ::ₘ (x + ch) ::ₘ (x + cq + ch) ::ₘ
          A'.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) := by
    rw [hval]
    simp only [Multiset.map_cons]
    rw [hc₁, hc₂, hc₃, hc₄]
  refine ⟨A', fun i hi => hsub (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)))), ?_, ?_, ?_⟩
  · -- cardinality
    have p1 : 0 < A.card := Finset.card_pos.mpr ⟨i₁, hi₁⟩
    have p2 : 0 < (A.erase i₁).card := Finset.card_pos.mpr ⟨i₂, hmem₂⟩
    have p3 : 0 < ((A.erase i₁).erase i₂).card := Finset.card_pos.mpr ⟨i₃, hmem₃⟩
    have p4 : 0 < (((A.erase i₁).erase i₂).erase i₃).card :=
      Finset.card_pos.mpr ⟨i₄, hmem₄⟩
    have e1 := Finset.card_erase_of_mem hi₁
    have e2 := Finset.card_erase_of_mem hmem₂
    have e3 := Finset.card_erase_of_mem hmem₃
    have e4 := Finset.card_erase_of_mem hmem₄
    rw [hA']
    omega
  · -- qualification of the stripped set
    have hb := (e2Folded_eq_zero_iff_balanced_cast hm1 A).mp hzero
    rw [hmap] at hb
    exact (e2Folded_eq_zero_iff_balanced_cast hm1 A').mpr
      ((balanced_pairSums_coset_augment hh2 hqq x _).mp hb)
  · -- the census value is preserved: the four coset powers cancel pairwise
    intro p _ g hg
    have h1 : ∑ i ∈ A, g ^ i
        = ((A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))).map (fun w => g ^ w.val)).sum := by
      rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
      congr 1
      exact Multiset.map_congr rfl fun i _ => (pow_val_cast hg i).symm
    have h2 : ∑ i ∈ A', g ^ i
        = ((A'.val.map (Nat.cast : ℕ → ZMod (2 ^ m))).map (fun w => g ^ w.val)).sum := by
      rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
      congr 1
      exact Multiset.map_congr rfl fun i _ => (pow_val_cast hg i).symm
    rw [h1, h2, hmap]
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [hch, pow_val_add_half hm1 hg x, pow_val_add_half hm1 hg (x + cq)]
    ring

/-! ## Source audit -/

#print axioms strip_coset

end ArkLib.ProximityGap.WindowTwoLayer
