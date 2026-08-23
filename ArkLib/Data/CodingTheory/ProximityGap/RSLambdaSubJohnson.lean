/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListBound
import ArkLib.Data.CodingTheory.ProximityLeaves2
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# The sub-Johnson `Λ` bound for Reed–Solomon codes (#389, the LD⇒MCA input)

The in-tree `Λ` bounds for RS codes are gated on the **Johnson condition**
(`Lambda_le_of_johnson_condition`, `a² > n(k−1)`).  Below the Johnson radius that bound is
vacuous.  This file lands the **sub-Johnson** `Λ` bound, valid at every radius, by pushing
`rsCode_subJohnson_list_card_le` (the Deza–Frankl list bound) through the distance↔agreement
bridge:

> **`rsCode_Lambda_subJohnson_le`** — for `k ≤ a` and `a ≤ (1−δ)·n`,
> ```
> Λ(rsCode dom k, δ) ≤ C(n,k) / C(a,k).
> ```

This is exactly the `Λ(C,δ) ≤ L` hypothesis that ABF26 **Theorem 5.1**
(`linear_listSize_to_epsMCA_gcxk25`, the LD⇒MCA bridge) consumes — now available **below
Johnson** for explicit RS codes, where the Johnson-gated bound does not apply.  It is the
list-decoding side of the proximity challenge fed directly into the MCA side.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap CodeGeometry ListDecodable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Distance→agreement on the close-codeword set: a codeword within relative radius `δ` of `f`
agrees with `f` on at least the integer target `a ≤ (1−δ)·n`.  Kept free of `classical` so every
`DecidableEq`-dependent term uses the ambient instance. -/
theorem mem_filter_of_closeCodewordsRel (dom : Fin n ↪ F) {k a : ℕ} {δ : ℝ}
    (hn : 0 < Fintype.card (Fin n))
    (ha : (a : ℝ) ≤ (1 - δ) * (Fintype.card (Fin n) : ℝ)) {f c : Fin n → F}
    (hc : c ∈ closeCodewordsRel
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) f δ) :
    c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧ a ≤ (agreeSet c f).card := by
  obtain ⟨hcC, hball⟩ := hc
  refine ⟨hcC, ?_⟩
  rw [relHammingBall, Set.mem_setOf_eq] at hball
  -- hball : (↑(Code.relHammingDist f c) : ℝ) ≤ δ
  have hcf : (hammingDist c f : ℝ) / (Fintype.card (Fin n) : ℝ) ≤ δ := by
    have heq : (hammingDist c f : ℝ) / (Fintype.card (Fin n) : ℝ)
        = ((Code.relHammingDist f c : ℚ≥0) : ℝ) := by
      simp only [Code.relHammingDist, hammingDist_comm c f]
      push_cast
      ring
    rw [heq]
    convert hball using 3 <;> exact Subsingleton.elim _ _
  have hagree : (1 - δ) * (Fintype.card (Fin n) : ℝ) ≤ (agree c f : ℝ) :=
    (relHammingDist_le_iff_agree_ge c f hn).mp hcf
  have : (a : ℝ) ≤ ((agreeSet c f).card : ℝ) := le_trans ha hagree
  exact_mod_cast this

omit [NeZero n] in
open Classical in
/-- **The sub-Johnson `Λ` bound**: `Λ(rsCode dom k, δ) ≤ C(n,k)/C(a,k)` whenever `k ≤ a` and the
integer agreement target `a` is below the radius-`δ` agreement line `(1−δ)·n`.  Valid at every
radius — in particular below the Johnson radius, where `Lambda_le_of_johnson_condition` is
vacuous.  This is the LD⇒MCA (ABF26 T5.1) list-size input for explicit RS codes. -/
theorem rsCode_Lambda_subJohnson_le (dom : Fin n ↪ F) {k a : ℕ} {δ : ℝ}
    (hk : 1 ≤ k) (hka : k ≤ a) (hn : 0 < Fintype.card (Fin n))
    (ha : (a : ℝ) ≤ (1 - δ) * (Fintype.card (Fin n) : ℝ)) :
    Lambda ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ (n.choose k / a.choose k : ℕ∞) := by
  refine Lambda_le_of_forall_ncard_le fun f => ?_
  set L := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ a ≤ (agreeSet c f).card) with hL
  have hsub : closeCodewordsRel
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) f δ
      ⊆ (↑L : Set (Fin n → F)) := by
    intro c hc
    rw [Finset.mem_coe, hL, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, mem_filter_of_closeCodewordsRel dom hn ha hc⟩
  have hLfin : (closeCodewordsRel
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) f δ).ncard ≤ L.card := by
    rw [← Set.ncard_coe_finset L]
    exact Set.ncard_le_ncard hsub L.finite_toSet
  have hLbound : L.card ≤ n.choose k / a.choose k :=
    rsCode_subJohnson_list_card_le_div dom hk hka f
  calc (((closeCodewordsRel
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) f δ).ncard : ℕ) : ℕ∞)
      ≤ (L.card : ℕ∞) := by exact_mod_cast hLfin
    _ ≤ (n.choose k / a.choose k : ℕ∞) := by exact_mod_cast hLbound

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.mem_filter_of_closeCodewordsRel
#print axioms ProximityGap.Ownership.rsCode_Lambda_subJohnson_le
