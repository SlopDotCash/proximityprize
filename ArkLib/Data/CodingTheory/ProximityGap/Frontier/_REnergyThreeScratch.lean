/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import Mathlib.Tactic

/-! Scratch: the forward tuple-lift for #444's char-0 E₃ = rEnergy identification.
`count_antipodal_of_sum_eq_zero` (in-tree, multiset form, `[CharZero]`, 2^k-roots) lifted to a
`Fin m → L` tuple: a zero-sum tuple of 2^k-th roots is fiber-balanced. The forward partner of the
already-char-free converse `E3NegSymConverse.sum_eq_zero_of_fiber_balanced`. -/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset

namespace REnergyThreeScratch

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L]

open LamLeungMultisetAntipodal (count_antipodal_of_sum_eq_zero)

/-- **Zero-sum tuple of 2^k-th roots ⟹ fiber-balanced** (forward, char 0). Lifts the multiset
`count_antipodal_of_sum_eq_zero` along `M = (univ.val).map c`. -/
theorem fiber_balanced_of_sum_eq_zero {m k : ℕ} (c : Fin m → L)
    (hroot : ∀ i, (c i) ^ (2 ^ k) = 1) (hsum : ∑ i, c i = 0) :
    ∀ z : L, (Finset.univ.filter (fun i => c i = z)).card
           = (Finset.univ.filter (fun i => c i = -z)).card := by
  classical
  set M : Multiset L := (Finset.univ.val).map c with hM
  have hMsum : M.sum = 0 := by
    have hms : M.sum = ∑ i, c i := by rw [hM]; rfl
    rw [hms]; exact hsum
  have hMroot : ∀ z ∈ M, z ^ (2 ^ k) = 1 := by
    intro z hz
    rw [hM, Multiset.mem_map] at hz
    obtain ⟨i, _, hi⟩ := hz
    rw [← hi]; exact hroot i
  have hcount : ∀ z : L, M.count z = (Finset.univ.filter (fun i => c i = z)).card := by
    intro z
    rw [hM, Multiset.count_map]
    simp only [Finset.filter]
    congr 1
    apply Multiset.filter_congr
    intro a _
    exact eq_comm
  intro z
  have := count_antipodal_of_sum_eq_zero hMroot hMsum z
  rw [hcount z, hcount (-z)] at this
  exact this

open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)

/-- The explicit `Fin 6 → L` glue of two `Fin 3` tuples (second negated). `![…]` form keeps every
sum/membership reduction a `fin_cases`, with no `Fin (3+3)` unification or `⟨k,_⟩` index friction. -/
private def glue (v w : Fin 3 → L) : Fin 6 → L :=
  ![v 0, v 1, v 2, -(w 0), -(w 1), -(w 2)]

private theorem glue_sum (v w : Fin 3 → L) : ∑ i, glue v w i = (∑ i, v i) - ∑ i, w i := by
  simp only [glue, Fin.sum_univ_six, Fin.sum_univ_three]
  simp [Matrix.cons_val]
  ring

/-- **`rEnergy G 3` counts zero-sum 6-tuples** (neg-closed `G`). The relation energy `#{(v,w) : Σv=Σw}`
bijects with `#{c : Σc = 0}` via `(v,w) ↦ glue v w` (first 3 = `v`, last 3 = `−w`). -/
theorem rEnergy_three_eq_zeroSumCount (G : Finset L) (hneg : ∀ z ∈ G, -z ∈ G) :
    rEnergy G 3
      = ((Fintype.piFinset (fun _ : Fin 6 => G)).filter (fun c => ∑ i, c i = 0)).card := by
  classical
  have hre : rEnergy G 3
      = (((Fintype.piFinset (fun _ : Fin 3 => G)) ×ˢ (Fintype.piFinset (fun _ : Fin 3 => G))).filter
          (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card := by
    rw [rEnergy, ← Finset.sum_product', ← Finset.card_filter]
  rw [hre]
  refine Finset.card_nbij'
    (fun p => glue p.1 p.2)
    (fun c => (![c 0, c 1, c 2], ![-(c 3), -(c 4), -(c 5)]))
    ?_ ?_ ?_ ?_
  · -- forward: glue v w is in G and zero-sum
    rintro ⟨v, w⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset] at hp
    obtain ⟨⟨hv, hw⟩, hsum⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp only [glue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val] <;>
        first
          | exact hv _
          | exact hneg _ (hw _)
    · rw [glue_sum, hsum]; ring
  · -- backward: the split (with negated tail) lands in the product-filter
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hc
    obtain ⟨hcG, hcsum⟩ := hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset]
    refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_⟩
    · fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val] <;> exact hcG _
    · fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val] <;> exact hneg _ (hcG _)
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val]
      have h6 : ∑ i, c i = c 0 + c 1 + c 2 + c 3 + c 4 + c 5 := Fin.sum_univ_six c
      rw [h6] at hcsum; linear_combination hcsum
  · -- left inverse: split ∘ glue = id
    rintro ⟨v, w⟩ _
    ext i
    · fin_cases i <;> simp [glue]
    · fin_cases i <;> simp [glue]
  · -- right inverse: glue ∘ split = id
    intro c _
    funext i
    fin_cases i <;> simp [glue]

end REnergyThreeScratch

#print axioms REnergyThreeScratch.fiber_balanced_of_sum_eq_zero

#print axioms REnergyThreeScratch.rEnergy_three_eq_zeroSumCount
