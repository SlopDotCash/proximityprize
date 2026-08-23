/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRCubicSupplyLower

/-!
# The EXACT orbit count: distinct zero-sum QR triples = 6 x the sum-zero 3-subsets (#389)

`QRCubicSupplyLower` bounded the distinct-entry zero-sum triples by `27`x the sum-zero
`3`-subsets (fiber `≤ 27`).  This file pins the orbit factor **exactly to `6`**: a
distinct-entry triple is one of the `3! = 6` orderings of its underlying `3`-set
(`perm_of_three`), so the orbit map `(a,b,c) ↦ {a,b,c}` is `6`-to-`1`:

> **`qrDistinctTriples_card_eq`** — `#{distinct (a,b,c) ∈ (QR*)³ : a+b+c=0}
> = 6 · #{T ⊆ QR* : |T|=3, ∑T = 0}`.

Combined with the exact ordered count `qr_zeroSum_ordered_eq` (`= #QR*·M`) and the
degenerate count (`≤ 3·#QR*`, `qrDegenerate_card_le`), this brackets the unordered
cubic-word list size (`= cubicSupply`):
`(#QR*·M − 3·#QR*)/6 ≤ #{sum-zero 3-subsets} ≤ #QR*·M / 6`, i.e. `Θ(n²)` with the
exact leading constant `(q−1)(q−5)/48`.  Issue #389.
-/
open Finset
namespace ProximityGap.PairRank
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem image_tripleSet_eq :
    (qrDistinctTriples (F := F)).image tripleSet = qrSumZeroSubsets := by
  apply Finset.Subset.antisymm image_tripleSet_subset
  intro T hT
  rw [qrSumZeroSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hT
  obtain ⟨⟨hsub, hcard⟩, hsum⟩ := hT
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
  rw [Finset.mem_image]
  refine ⟨(x, y, z), ?_, rfl⟩
  rw [qrDistinctTriples, Finset.mem_filter, mem_qrZeroSumTriples]
  refine ⟨⟨hsub (by simp), hsub (by simp), hsub (by simp), ?_⟩, hxy, hxz, hyz⟩
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton] at hsum
  linear_combination hsum

theorem perm_of_three {x y z a b c : F}
    (ha : a = x ∨ a = y ∨ a = z) (hb : b = x ∨ b = y ∨ b = z)
    (hc : c = x ∨ c = y ∨ c = z) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ((a, b, c) = (x, y, z)) ∨ ((a, b, c) = (x, z, y)) ∨ ((a, b, c) = (y, x, z)) ∨
    ((a, b, c) = (y, z, x)) ∨ ((a, b, c) = (z, x, y)) ∨ ((a, b, c) = (z, y, x)) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      | exact absurd rfl hab
      | exact absurd rfl hac
      | exact absurd rfl hbc

theorem fiber_card_eq_six (T : Finset F) (hT : T ∈ qrSumZeroSubsets (F := F)) :
    ((qrDistinctTriples (F := F)).filter (fun t => tripleSet t = T)).card = 6 := by
  classical
  rw [qrSumZeroSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hT
  obtain ⟨⟨hsub, hcard⟩, hsum⟩ := hT
  obtain ⟨x, y, z, hxy, hxz, hyz, hTeq⟩ := Finset.card_eq_three.mp hcard
  have hx : x ∈ qrStar (F := F) := hsub (by rw [hTeq]; simp)
  have hy : y ∈ qrStar (F := F) := hsub (by rw [hTeq]; simp)
  have hz : z ∈ qrStar (F := F) := hsub (by rw [hTeq]; simp)
  have hsum0 : x + y + z = 0 := by
    rw [hTeq, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton] at hsum
    linear_combination hsum
  set perms : Finset (F × F × F) :=
    {(x, y, z), (x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)} with hperms
  have heq : (qrDistinctTriples (F := F)).filter (fun t => tripleSet t = T) = perms := by
    ext t
    simp only [Finset.mem_filter, hperms, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, htS⟩
      rw [qrDistinctTriples, Finset.mem_filter, mem_qrZeroSumTriples] at ht
      obtain ⟨_, hd1, hd2, hd3⟩ := ht
      have hmem : ∀ w, w ∈ tripleSet t → w = x ∨ w = y ∨ w = z := by
        intro w hw; rw [htS, hTeq] at hw
        simpa [Finset.mem_insert, Finset.mem_singleton] using hw
      have h1 := hmem t.1 (by simp [tripleSet])
      have h2 := hmem t.2.1 (by simp [tripleSet])
      have h3 := hmem t.2.2 (by simp [tripleSet])
      exact perm_of_three h1 h2 h3 hd1 hd2 hd3
    · intro hcases
      have mem_dist : ∀ a b c : F, a ∈ qrStar (F := F) → b ∈ qrStar (F := F) →
          c ∈ qrStar (F := F) → a + b + c = 0 → a ≠ b → a ≠ c → b ≠ c →
          (a, b, c) ∈ qrDistinctTriples (F := F) := by
        intro a b c hca hcb hcc hcsum hab hac hbc
        rw [qrDistinctTriples, Finset.mem_filter, mem_qrZeroSumTriples]
        exact ⟨⟨hca, hcb, hcc, hcsum⟩, hab, hac, hbc⟩
      have set_eq : ∀ a b c : F, ({a, b, c} : Finset F) = ({x, y, z} : Finset F) →
          tripleSet (a, b, c) = T := fun a b c h => by rw [hTeq]; exact h
      rcases hcases with h|h|h|h|h|h <;> subst h
      · refine ⟨mem_dist x y z hx hy hz hsum0 hxy hxz hyz, set_eq _ _ _ ?_⟩
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
      · refine ⟨mem_dist x z y hx hz hy (by linear_combination hsum0) hxz hxy (Ne.symm hyz),
          set_eq _ _ _ ?_⟩
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
      · refine ⟨mem_dist y x z hy hx hz (by linear_combination hsum0) (Ne.symm hxy) hyz hxz,
          set_eq _ _ _ ?_⟩
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
      · refine ⟨mem_dist y z x hy hz hx (by linear_combination hsum0) hyz (Ne.symm hxy)
          (Ne.symm hxz), set_eq _ _ _ ?_⟩
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
      · refine ⟨mem_dist z x y hz hx hy (by linear_combination hsum0) (Ne.symm hxz)
          (Ne.symm hyz) hxy, set_eq _ _ _ ?_⟩
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
      · refine ⟨mem_dist z y x hz hy hx (by linear_combination hsum0) (Ne.symm hyz)
          (Ne.symm hxz) (Ne.symm hxy), set_eq _ _ _ ?_⟩
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
  rw [heq, hperms]
  rw [Finset.card_insert_of_notMem (by
        simp [Prod.mk.injEq, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]),
      Finset.card_insert_of_notMem (by
        simp [Prod.mk.injEq, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]),
      Finset.card_insert_of_notMem (by
        simp [Prod.mk.injEq, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]),
      Finset.card_insert_of_notMem (by
        simp [Prod.mk.injEq, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]),
      Finset.card_insert_of_notMem (by
        simp [Prod.mk.injEq, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]),
      Finset.card_singleton]

theorem qrDistinctTriples_card_eq :
    (qrDistinctTriples (F := F)).card = 6 * (qrSumZeroSubsets (F := F)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
        (f := tripleSet) (t := qrSumZeroSubsets (F := F))
        (fun t ht => image_tripleSet_subset (Finset.mem_image_of_mem _ ht))]
  rw [Finset.sum_congr rfl (fun T hT => fiber_card_eq_six T hT), Finset.sum_const,
    smul_eq_mul, Nat.mul_comm]
end ProximityGap.PairRank
