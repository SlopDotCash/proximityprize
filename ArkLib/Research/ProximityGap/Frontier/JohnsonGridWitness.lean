/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ListScalarExtension
import Mathlib.Algebra.Field.ZMod

/-! # Eight lines at the length-sixteen Johnson radius

Index the nonzero residues modulo 17 by a four-by-four grid. The received value
at each site is its row index. Four constant polynomials explain its rows and four
slope-one polynomials explain its columns. These eight words persist under any
field embedding and at every nonempty interleaving width. -/

namespace ProximityGap.JohnsonGridWitness

open Polynomial Finset Code

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private abbrev Site := Fin 4 × Fin 4

/-- The sixteen evaluation points, in column-major order. -/
def domain : (Fin 4 × Fin 4) ↪ ZMod 17 :=
  ⟨fun ij => 1 + (ij.1.val : ZMod 17) + 4 * (ij.2.val : ZMod 17), by decide⟩

private def center (ij : Site) : ZMod 17 := ij.1.val

private def word : Fin 4 ⊕ Fin 4 → Site → ZMod 17
  | .inl a, _ => a.val
  | .inr b, ij => domain ij - (1 + 4 * (b.val : ZMod 17))

private theorem distinct : Function.Injective word := by decide

private theorem close : ∀ a, hammingDist center (word a) ≤ 12 := by decide

private theorem codeword (a : Fin 4 ⊕ Fin 4) : word a ∈ ReedSolomon.code domain 2 := by
  cases a with
  | inl c =>
    exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (C (c.val : ZMod 17))
      (by simp) (by intro i; simp [word])
  | inr c =>
    apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
      (X - C (1 + 4 * (c.val : ZMod 17)))
    · exact (natDegree_sub_le ..).trans_lt (max_lt (by rw [natDegree_X]; decide)
        (by rw [natDegree_C]; decide))
    · intro i
      simp [word]

private theorem scalar_eight_le :
    (8 : ℕ∞) ≤ Code.Lambda (ReedSolomon.code domain 2 : Set (Site → ZMod 17)) (12 / 16) := by
  have mem : (↑(univ.image word) : Set (Site → ZMod 17)) ⊆
      Code.closeCodewordsRel (ReedSolomon.code domain 2 : Set (Site → ZMod 17)) center
        ((12 : ℕ) / (Fintype.card Site : ℝ)) := by
    intro w hw
    obtain ⟨a, _, rfl⟩ := mem_image.mp hw
    refine Code.mem_closeCodewordsRel_iff.mpr ⟨codeword a, ?_⟩
    simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
    exact div_le_div_of_nonneg_right (by exact_mod_cast close a) (by positivity)
  have bound := Code.encard_le_Lambda_of_subset_closeCodewordsRel mem
  rw [Set.encard_coe_eq_coe_finsetCard, card_image_of_injective _ distinct, card_univ] at bound
  simpa [Site, Fintype.card_sum, Fintype.card_prod] using bound

variable {F : Type*} [Field F]

/-- The sixteen grid points after embedding the prime field. -/
def extension_domain (f : ZMod 17 →+* F) : (Fin 4 × Fin 4) ↪ F :=
  domain.trans ⟨f, f.injective⟩

/-- Every field extension and every nonempty width preserve the eight codewords. -/
theorem eight_le (f : ZMod 17 →+* F) (κ : Type*) [Nonempty κ] :
    (8 : ℕ∞) ≤ Code.Lambda
      (interleavedCodeSet (κ := κ) (ReedSolomon.code (extension_domain f) 2 :
        Set ((Fin 4 × Fin 4) → F))) (12 / 16) := by
  apply (scalar_eight_le.trans (ListScalarExtension.lambda_le f domain 2 (12 / 16))).trans
  let rep : F → κ → F := fun x _ => x
  let C : Set (Site → F) := ReedSolomon.code (extension_domain f) 2
  have maps : ∀ c ∈ C, rep ∘ c ∈ interleavedCodeSet (κ := κ) C := by
    intro c hc j
    exact hc
  exact Code.Lambda_le_of_injective_comp (e := rep)
    (fun _ _ h => congrFun h (Classical.arbitrary κ)) maps _

/-- The same bound for any characteristic-17 evaluation map with the grid coordinates. -/
theorem eight_le_of_coordinates (κ : Type*) [Nonempty κ] (D : (Fin 4 × Fin 4) ↪ F)
    [CharP F 17] (coords : ∀ ij, D ij = 1 + (ij.1.val : F) + 4 * (ij.2.val : F)) :
    (8 : ℕ∞) ≤ Code.Lambda (interleavedCodeSet (κ := κ)
      (ReedSolomon.code D 2 : Set ((Fin 4 × Fin 4) → F))) (12 / 16) := by
  let f : ZMod 17 →+* F := ZMod.castHom (dvd_refl 17) F
  have h : D = extension_domain f := by
    ext ij
    rw [coords]
    change _ = f (1 + (ij.1.val : ZMod 17) + 4 * (ij.2.val : ZMod 17))
    simp only [map_add, map_mul, map_one, map_natCast, map_ofNat]
  rw [h]
  exact eight_le f κ

end ProximityGap.JohnsonGridWitness
