/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Basic.RelDistTranslation

/-!
# Coset decomposition of the "far" set (toward T4.17, #82)

For a linear code `C` (submodule of `ι → F`), the set of words far from `C`,
`{w | δ < δᵣ(w, C)}`, is a union of cosets of `C` (since `δᵣ(·, C)` is constant on cosets —
`relDistFromCode_eq_of_sub_mem`). Hence its cardinality is `|C|` times the number of *far cosets*:

  `#{w far} = |C| · #{far cosets}`.

This reduces the CS25 complete-CA-breakdown covering bound `#{w far} < |A|^n / |F|` (T4.17) to a
statement about the number of far cosets — equivalently, a lower bound on the number of cosets met
by the Hamming ball `B(0, δn)` (the syndrome count).
-/

open Finset
open scoped NNReal ENNReal Classical

namespace Code

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A coset `{w | w - w₀ ∈ C}` of a linear code `C` has cardinality `|C|`. -/
theorem coset_card (C : Submodule F (ι → F)) (w₀ : ι → F) :
    (univ.filter (fun w : ι → F => w - w₀ ∈ C)).card = Fintype.card C := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun w => ⟨w.1 - w₀, w.2⟩
      invFun := fun c => ⟨c.1 + w₀, by simpa using c.2⟩
      left_inv := fun w => by simp
      right_inv := fun c => by simp }

/-- **Coset decomposition of the far set.** The number of words far from a linear code `C`
(`¬ δᵣ(w, C) ≤ δ`) is `|C|` times the number of distinct cosets of far words. -/
theorem card_far_eq_mul (C : Submodule F (ι → F)) (δ : ℝ≥0) :
    (univ.filter (fun w : ι → F => ¬ relDistFromCode w (C : Set (ι → F)) ≤ δ)).card
      = Fintype.card C
        * ((univ.filter (fun w : ι → F => ¬ relDistFromCode w (C : Set (ι → F)) ≤ δ)).image
            (fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C))).card := by
  classical
  set S : Finset (ι → F) :=
    univ.filter (fun w : ι → F => ¬ relDistFromCode w (C : Set (ι → F)) ≤ δ) with hS
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C))
      (t := S.image (fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C)))
      (fun w hw => Finset.mem_image_of_mem _ hw)]
  have hfib : ∀ b ∈ S.image (fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C)),
      (S.filter (fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C) = b)).card
        = Fintype.card C := by
    intro b hb
    obtain ⟨w₀, hw₀S, hw₀⟩ := Finset.mem_image.mp hb
    have hw₀far : ¬ relDistFromCode w₀ (C : Set (ι → F)) ≤ δ := by simpa [hS] using hw₀S
    -- the fiber over `b = ⟦w₀⟧` within `S` is exactly the coset `{w | w - w₀ ∈ C}`
    have hset : S.filter (fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C) = b)
        = univ.filter (fun w : ι → F => w - w₀ ∈ C) := by
      ext w
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, ← hw₀,
        Submodule.Quotient.eq]
      constructor
      · rintro ⟨_, hmem⟩; exact hmem
      · intro hmem
        refine ⟨?_, hmem⟩
        rw [Code.relDistFromCode_eq_of_sub_mem C hmem]; exact hw₀far
    rw [hset, coset_card]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **General coset decomposition.** For any predicate `p` on the distance-to-code, the set
`{w | p (δᵣ(w, C))}` is a union of cosets (since `δᵣ(·, C)` is constant on cosets), so its
cardinality is `|C|` times the number of distinct cosets it contains. Generalizes
`card_far_eq_mul` (take `p := (¬ · ≤ δ)`). -/
theorem card_coset_pred_eq_mul (C : Submodule F (ι → F)) (p : ENNReal → Prop) :
    (univ.filter (fun w : ι → F => p (relDistFromCode w (C : Set (ι → F))))).card
      = Fintype.card C
        * ((univ.filter (fun w : ι → F => p (relDistFromCode w (C : Set (ι → F))))).image
            (fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C))).card := by
  classical
  set S : Finset (ι → F) :=
    univ.filter (fun w : ι → F => p (relDistFromCode w (C : Set (ι → F)))) with hS
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C))
      (t := S.image (fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C)))
      (fun w hw => Finset.mem_image_of_mem _ hw)]
  have hfib : ∀ b ∈ S.image (fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C)),
      (S.filter (fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C) = b)).card
        = Fintype.card C := by
    intro b hb
    obtain ⟨w₀, hw₀S, hw₀⟩ := Finset.mem_image.mp hb
    have hw₀p : p (relDistFromCode w₀ (C : Set (ι → F))) := by simpa [hS] using hw₀S
    have hset : S.filter (fun w => (Submodule.Quotient.mk w : (ι → F) ⧸ C) = b)
        = univ.filter (fun w : ι → F => w - w₀ ∈ C) := by
      ext w
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, ← hw₀,
        Submodule.Quotient.eq]
      constructor
      · rintro ⟨_, hmem⟩; exact hmem
      · intro hmem
        refine ⟨?_, hmem⟩
        rw [Code.relDistFromCode_eq_of_sub_mem C hmem]; exact hw₀p
    rw [hset, coset_card]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]

end Code
