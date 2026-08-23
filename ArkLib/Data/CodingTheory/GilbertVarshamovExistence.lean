/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentReduction

/-!
# The Gilbert–Varshamov existence bound

There exists a code with minimum distance `≥ d` and at least `q^n / V(d−1)` codewords:

  `q^n ≤ |C| · V(d−1)`.

Greedy/maximal-code argument: take a maximum-cardinality code `C` with minimum distance `≥ d`; by
maximality every word is within `d−1` of some codeword (otherwise it could be added), so the
radius-`(d−1)` balls cover the whole space, giving `q^n ≤ |C|·V(d−1)`.  This is the existence
(lower-bound) counterpart to the GV covering bound.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Gilbert–Varshamov existence bound.** There is a code with minimum distance `≥ d` and at least
`q^n / V(d−1)` codewords: `q^n ≤ |C| · V(d−1)`. -/
theorem gv_existence (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : Finset (ι → F), (∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → d ≤ hammingDist c c')
      ∧ Fintype.card F ^ Fintype.card ι
        ≤ C.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ d - 1)).card := by
  classical
  haveI : DecidablePred (fun C : Finset (ι → F) =>
      ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → d ≤ hammingDist c c') := fun _ => Classical.propDecidable _
  set Valid : Finset (Finset (ι → F)) :=
    univ.filter (fun C => ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → d ≤ hammingDist c c') with hV
  have hne : Valid.Nonempty := ⟨∅, by simp [hV]⟩
  obtain ⟨C, hCmem, hCmax⟩ := Valid.exists_max_image Finset.card hne
  rw [hV, mem_filter] at hCmem
  have hCvalid := hCmem.2
  refine ⟨C, hCvalid, ?_⟩
  have hcover : ∀ x : ι → F, ∃ c ∈ C, hammingDist x c ≤ d - 1 := by
    intro x
    by_cases hxC : x ∈ C
    · exact ⟨x, hxC, by simp⟩
    · by_contra hcon
      push_neg at hcon
      have hins : insert x C ∈ Valid := by
        rw [hV, mem_filter]
        refine ⟨mem_univ _, ?_⟩
        intro a ha b hb hab
        rw [mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · have := hcon b hb; omega
        · rw [hammingDist_comm]; have := hcon a ha; omega
        · exact hCvalid a ha b hb hab
      have hlt : C.card < (insert x C).card :=
        Finset.card_lt_card (Finset.ssubset_insert hxC)
      have := hCmax (insert x C) hins
      omega
  have hsubset : (univ : Finset (ι → F))
      ⊆ C.biUnion (fun c => univ.filter (fun w => hammingDist w c ≤ d - 1)) := by
    intro x _
    obtain ⟨c, hc, hcx⟩ := hcover x
    rw [mem_biUnion]
    exact ⟨c, hc, mem_filter.mpr ⟨mem_univ _, hcx⟩⟩
  calc Fintype.card F ^ Fintype.card ι = (univ : Finset (ι → F)).card := by
        rw [card_univ, Fintype.card_fun]
    _ ≤ (C.biUnion (fun c => univ.filter (fun w => hammingDist w c ≤ d - 1))).card :=
        Finset.card_le_card hsubset
    _ ≤ ∑ c ∈ C, (univ.filter (fun w => hammingDist w c ≤ d - 1)).card :=
        Finset.card_biUnion_le
    _ = ∑ c ∈ C, (univ.filter (fun w : ι → F => hammingDist w 0 ≤ d - 1)).card :=
        Finset.sum_congr rfl (fun c _ => ball_card_center_indep c (d - 1))
    _ = C.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ d - 1)).card := by
        rw [Finset.sum_const, smul_eq_mul]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.gv_existence
