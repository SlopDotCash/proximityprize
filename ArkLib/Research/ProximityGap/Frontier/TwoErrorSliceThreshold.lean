/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceCount
import ArkLib.Research.ProximityGap.Frontier.FourRateList128

/-! # Exact half-rate list threshold from the two-error slice certificate -/

namespace ProximityGap.TwoErrorSlice

open Finset Code

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F]

omit [Nonempty I] in
/-- An arbitrary scalar received word is covered uniformly up to the first bad
Hamming step. -/
theorem scalar_upper (D : I ↪ F) (cert : PenaltyBound D) (hn : Fintype.card I=128)
    (δ : ℝ) (hδ : δ < 63/128) : Lambda (ReedSolomon.code D 64 : Set (I → F)) δ ≤
      (361269899996423739323753777598085 : ℕ) := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro W T hT
  have hm (j : T) := mem_closeCodewordsRel_iff.mp (hT j.val j.property)
  choose P hdeg hval using fun j : T => ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hm j).1
  have hin : Function.Injective P := by
    intro i j he
    apply Subtype.ext
    funext x
    rw [← hval i x,← hval j x,he]
  let E (j : T) := univ.filter fun x => j.val x ≠ W x
  have hsize (j : T) : (E j).card ≤ 62 := by
    have h := (hm j).2
    rw [relHammingDist_coe,hammingDist_comm,hn] at h
    have h' : (hammingDist j.val W : ℝ) < 63 := by
      norm_num at h
      linarith
    change hammingDist j.val W ≤ 62
    exact Nat.le_of_lt_succ (by exact_mod_cast h')
  have bound := family_bound D cert hn P hin W univ E (fun i _ x => by simp [E,hval])
    (fun i _ => hdeg i) (fun i _ => hsize i)
  simpa only [card_univ,Fintype.card_coe] using bound

/-- Every positive width has the same first bad error count in the indicated
budget window. The group elements index an arbitrary enumeration of the domain. -/
theorem half_threshold [Fintype F] (D : I ↪ F) (cert : PenaltyBound D) (hn : Fintype.card I=128)
    (H : Subgroup Fˣ) [Fintype H] (z : I → H) (hz : ∀ i, D i=((z i : Fˣ) : F))
    (B : ℕ) (upper : 361269899996423739323753777598085 ≤ B)
    (lower : Fintype.card H * B < Nat.choose 128 65) (pairs : (B+1).choose 2 ≤ Nat.card F)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D 64 : Set (I → F))) δ ≤
      (B : ℕ∞) ↔ δ < 63/128 := by
  constructor
  · intro good
    by_contra! bad
    have hs := PrescribedProductList.exceeds_budget D H z hz (k := 64) (B := B)
      (by decide) (by rw [hn]; exact lower)
    rw [hn] at hs
    norm_num only [Nat.reduceAdd,Nat.reduceSub,Nat.cast_ofNat] at hs
    let diag : F → Fin m → F := fun x _ => x
    have hi : Function.Injective diag := fun _ _ he => congrFun he ⟨0,hm⟩
    have hd := Lambda_le_of_injective_comp (e := diag) hi
      (C := (ReedSolomon.code D 64 : Set (I → F)))
      (D := interleavedCodeSet (κ := Fin m) (ReedSolomon.code D 64 : Set (I → F)))
      (fun _ hx _ => hx) δ
    exact (not_lt_of_ge (hd.trans good)) (hs.trans_le (Lambda_mono bad))
  · intro hδ
    have h := scalar_upper D cert hn δ hδ
    exact InterleavedListProjection.interleaved_le_of_scalar_le (ReedSolomon.code D 64) δ B pairs
      (h.trans (by exact_mod_cast upper))

end ProximityGap.TwoErrorSlice

#print axioms ProximityGap.TwoErrorSlice.scalar_upper
#print axioms ProximityGap.TwoErrorSlice.half_threshold
