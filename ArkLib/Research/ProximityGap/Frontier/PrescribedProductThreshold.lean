/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.AgreementSubsetListPacking
import ArkLib.Research.ProximityGap.Frontier.ListScalarExtension
import ArkLib.Research.ProximityGap.Frontier.PrescribedProductList

/-! # An exact list-radius criterion from two binomial inequalities -/
set_option autoImplicit false
namespace ProximityGap.PrescribedProductThreshold
open Code

/-- For every nonempty interleaving, there is a sharp cutoff at n−(k+1+a) errors
when the interpolation packing and the common-product list straddle the budget.
The lower count uses the smaller field containing the evaluation points. -/
theorem list_threshold {I K E : Type*} [Fintype I] [Nonempty I]
    [Field K] [Fintype K] [Field E] (D : I ↪ K) (f : K →+* E)
    (H : Subgroup Kˣ) [Fintype H] (z : I → H) (hz : ∀ i, D i = ((z i : Kˣ) : K))
    (a k B m : ℕ) (hm : 0 < m) (hk : 0 < k) (ht : k+1+a ≤ Fintype.card I)
    (hu : (Fintype.card I).choose k / (k+2+a).choose k ≤ B)
    (hl : (Fintype.card H * Fintype.card K ^ a) * B < (Fintype.card I).choose (k+1+a))
    (δ : ℝ) :
    let D' := D.trans ⟨f, f.injective⟩
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D' k : Set (I → E))) δ ≤ B
      ↔ δ < ((Fintype.card I - (k+1+a) : ℕ) : ℝ) / (Fintype.card I : ℝ) := by
  classical
  dsimp only
  let D' := D.trans ⟨f, f.injective⟩
  let C : Set (I → E) := ReedSolomon.code D' k
  let d := ((Fintype.card I - (k+1+a) : ℕ) : ℝ) / (Fintype.card I : ℝ)
  constructor
  · intro safe
    by_contra! h
    have hscalar := PrescribedProductList.exceeds_budget_deeper D H z hz a hk hl
    have hext := hscalar.trans_le (ListScalarExtension.lambda_le f D k d)
    let e := fun v : E => fun _ : Fin m => v
    have hinj : Function.Injective e := fun _ _ h => congrFun h ⟨0,hm⟩
    have hdiag : Lambda C d ≤ Lambda (interleavedCodeSet (κ := Fin m) C) d :=
      Lambda_le_of_injective_comp (C := C) (D := interleavedCodeSet (κ := Fin m) C)
        hinj (fun _ hc _ => hc) _
    exact (not_lt_of_ge safe) ((hext.trans_le hdiag).trans_le (Lambda_mono h))
  · intro h
    apply (AgreementSubsetListPacking.interleaved_lambda_le_choose_div D' k (k+2+a) m δ
      (by omega) ?_).trans
    · exact_mod_cast hu
    · have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
      rw [lt_div_iff₀ hn, Nat.cast_sub ht] at h
      push_cast at *
      linarith

#print axioms list_threshold
end ProximityGap.PrescribedProductThreshold
