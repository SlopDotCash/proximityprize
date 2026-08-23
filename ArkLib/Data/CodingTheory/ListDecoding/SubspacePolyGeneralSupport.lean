/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyRecursion
import ArkLib.ToMathlib.LinearizedRecursionStep

/-!
# BKR06 linearized-support theorem (general dimension)

**The subspace polynomial of any finite `𝔽_q`-subspace `W ⊆ K` is q-power-supported** — it is a
genuine linearized polynomial `∑ aᵢ X^{q^i}`.  BKR06's linearized-support property in full
generality, by induction on `|W|` using the subspace recursion
`s_{V'⊕𝔽_q·u} = ∏_{c∈F}(s_{V'} - C(s_{V'}(ι c·u)))` and the q-power-support closure
`isQPowSupported_prod_eval_smul`.
-/

open Polynomial BigOperators

namespace BKR06

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra F K]

/-- **BKR06 linearized-support theorem (general dimension).** The subspace polynomial of any
finite `𝔽_q`-subspace `W ⊆ K` is q-power-supported. -/
theorem isQPowSupported_subspacePoly :
    ∀ (n : ℕ) (W : Submodule F K) [Fintype W], Fintype.card W = n →
      ArkLib.LinearizedKernel.IsQPowSupported (F := F) (subspacePoly (subFinset W)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ hcard
    by_cases hW : W = ⊥
    · subst hW
      have hb : subspacePoly (subFinset (⊥ : Submodule F K)) = (X : K[X]) := by
        have h0 : subFinset (⊥ : Submodule F K) = {0} := by
          ext x; simp [mem_subFinset, Submodule.mem_bot]
        rw [h0]; simp [subspacePoly, Finset.prod_singleton]
      rw [hb]
      exact ArkLib.LinearizedKernel.isQPowSupported_X
    · obtain ⟨W', u, hu_mem, hW'W, hu_notin, hdecomp, _hdisj⟩ := exists_line_decomp W hW
      let incl : W' → W := fun x => ⟨x.1, hW'W x.2⟩
      have hincl_inj : Function.Injective incl := by
        intro a b h
        apply Subtype.ext
        exact congrArg (Subtype.val : W → K) h
      haveI : Finite W' := Finite.of_injective incl hincl_inj
      haveI : Fintype W' := Fintype.ofFinite W'
      have hcard_lt : Fintype.card W' < Fintype.card W := by
        apply Fintype.card_lt_of_injective_not_surjective incl hincl_inj
        intro hsurj
        obtain ⟨x, hx⟩ := hsurj ⟨u, hu_mem⟩
        apply hu_notin
        have hxu : (x : K) = u := congrArg (Subtype.val : W → K) hx
        rw [← hxu]; exact x.2
      have hu_eval : (subspacePoly (subFinset W')).eval u ≠ 0 := by
        intro hev
        exact hu_notin (mem_subFinset.mp ((subspacePoly_isRoot_iff (subFinset W') u).mp hev))
      rw [subspacePoly_subFinset_recursion W W' u hdecomp hu_notin]
      exact ArkLib.LinearizedKernel.isQPowSupported_prod_eval_smul
        (ih (Fintype.card W') (hcard ▸ hcard_lt) W' rfl) u hu_eval

/-- The subspace polynomial of any finite `𝔽_q`-subspace is q-power-supported (clean form). -/
theorem isQPowSupported_subspacePoly' (W : Submodule F K) [Fintype W] :
    ArkLib.LinearizedKernel.IsQPowSupported (F := F) (subspacePoly (subFinset W)) :=
  isQPowSupported_subspacePoly (Fintype.card W) W rfl

end BKR06

-- Axiom audit.
#print axioms BKR06.isQPowSupported_subspacePoly'
