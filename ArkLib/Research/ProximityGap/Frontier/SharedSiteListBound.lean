/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank

/-! # A shortened Johnson bound for lists with prescribed common evaluations

Codewords in a single affine evaluation slice already agree with each other
at every prescribed site. Removing these sites reduces their pairwise
agreement bound even if the received center takes different values there.
-/
namespace ProximityGap.SharedSiteListBound

open Code Finset
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F]

/-- Codewords whose columns have prescribed values on a set of sites. -/
def slice (D : I ↪ F) (k width : ℕ) (J : Finset I) (v : I → Fin width → F) :
    Set (I → Fin width → F) :=
  {w ∈ interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F)) | ∀ x ∈ J, w x = v x}

omit [Nonempty I] in
/-- Counting after restriction to the complement agrees with set subtraction. -/
theorem card_on_complement (S J : Finset I) :
    (S.subtype (fun x => x ∈ Jᶜ)).card = (S \ J).card := by
  classical
  rw [Finset.card_subtype]
  congr 1
  ext x
  simp

/-- A closed ball intersected with an affine slice contains at most the number
of remaining sites when shortening enters the strict Johnson range. -/
theorem lambda_le (D : I ↪ F) (k width t : ℕ) (J : Finset I) (v : I → Fin width → F)
    (δ : ℝ) (hδ : δ*(Fintype.card I : ℝ) < (Fintype.card I : ℝ)-t+1)
    (ht : J.card < t) (hstrict : (Fintype.card I-J.card)*(k-1-J.card) < (t-J.card)^2) :
    Lambda (slice D k width J v) δ ≤ ((Fintype.card I-J.card : ℕ) : ℕ∞) := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro y T hT
  let w (i : ↥T) := i.val
  let supp (i : ↥T) := univ.filter fun x => w i x = y x
  have close (i : ↥T) := mem_closeCodewordsRel_iff.mp (hT i.val i.property)
  have large (i : ↥T) : t ≤ (supp i).card := by
    have hd := (close i).2
    have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    rw [relHammingDist_coe, hammingDist_comm, div_le_iff₀ hn] at hd
    have he : (agree (w i) y : ℝ) + (hammingDist (w i) y : ℝ) = Fintype.card I := by
      exact_mod_cast agree_add_hammingDist
    change (hammingDist (w i) y : ℝ) ≤ _ at hd
    have hr : t < agree (w i) y + 1 := by
      exact_mod_cast (show (t : ℝ) < (agree (w i) y : ℝ) + 1 by linarith)
    exact Nat.le_of_lt_succ hr
  let outside (i : ↥T) := (supp i).subtype (fun x => x ∈ Jᶜ)
  have outsize (i : ↥T) : t-J.card ≤ (outside i).card := by
    rw [show (outside i).card = _ from card_on_complement _ _]
    exact (Nat.sub_le_sub_right (large i) _).trans (Finset.le_card_sdiff _ _)
  choose S hsub hcard using fun i => Finset.exists_subset_card_eq (outsize i)
  have pair : Pairwise fun i j => (S i ∩ S j).card ≤ k-1-J.card := by
    intro i j hij
    let E := univ.filter fun x => w i x = w j x
    have hcommon : J ⊆ E := by
      intro x hx
      exact mem_filter.mpr ⟨mem_univ _,((close i).1.2 x hx).trans ((close j).1.2 x hx).symm⟩
    have hp := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet (close i).1.1 (close j).1.1
      (fun he => hij (Subtype.ext he))
    have hle : S i ∩ S j ⊆ E.subtype (fun x => x ∈ Jᶜ) := by
      intro x hx
      obtain ⟨hi,hj⟩ := mem_inter.mp hx
      have hi' : x.val ∈ supp i := mem_subtype.mp (hsub i hi)
      have hj' : x.val ∈ supp j := mem_subtype.mp (hsub j hj)
      exact mem_subtype.mpr (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi').2.trans (mem_filter.mp hj').2.symm⟩)
    have hc := card_le_card hle
    rw [card_on_complement, card_sdiff_of_subset hcommon] at hc
    change E.card < k at hp
    omega
  have h := card_le_universe_of_equal_card_pair_inter_le S (Fintype.card I-J.card) (t-J.card)
    (k-1-J.card) (by rw [Fintype.card_coe, card_compl]) (by omega) hcard pair (by omega)
  simpa using h

private theorem production {k e width s : ℕ} (D : Fin 1073741824 ↪ F)
    (J : Finset (Fin 1073741824)) (v : Fin 1073741824 → Fin width → F) (hJ : J.card = s)
    (ht : s < 1073741824-e) (hs : (1073741824-s)*(k-1-s) < (1073741824-e-s)^2) :
    Lambda (slice D k width J v) ((e : ℝ)/1073741824) ≤ ((1073741824-s : ℕ) : ℕ∞) := by
  have he : e ≤ 1073741824 := by omega
  have h := lambda_le D k width (1073741824-e) J v ((e : ℝ)/1073741824)
    (by rw [Fintype.card_fin, Nat.cast_sub he]; push_cast; linarith)
    (hJ ▸ ht) (by simpa only [Fintype.card_fin, hJ] using hs)
  simpa only [Fintype.card_fin, hJ] using h

/-- At the first open low-rate Hamming counts on the first named prime,
even one prescribed column keeps the closed list strictly below the budget.
The bound holds over every field on every evaluation domain of this size. -/
theorem first_open_low_rates (D : Fin 1073741824 ↪ F) (width : ℕ) (x : Fin 1073741824)
    (v : Fin 1073741824 → Fin width → F) :
    Lambda (slice D 134217728 width {x} v) (694116763/1073741824) ≤ 1073741823 ∧
    Lambda (slice D 67108864 width {x} v) (805306371/1073741824) ≤ 1073741823 := by
  constructor
  · exact production (k := 134217728) (e := 694116763) D _ v (Finset.card_singleton _) (by decide) (by decide)
  · exact production (k := 67108864) (e := 805306371) D _ v (Finset.card_singleton _) (by decide) (by decide)

/-- A common split vanishing factor of degree `2^23-1` keeps both low-rate
affine slices below the first-prime budget over the indicated larger balls. -/
theorem common_fiber_low_rates (D : Fin 1073741824 ↪ F) (width : ℕ)
    (J : Finset (Fin 1073741824)) (hJ : J.card = 8388607) (v : Fin 1073741824 → Fin width → F) :
    Lambda (slice D 134217728 width J v) (699221467/1073741824) ≤ 1065353217 ∧
    Lambda (slice D 67108864 width J v) (815237616/1073741824) ≤ 1065353217 := by
  constructor
  · exact production (k := 134217728) (e := 699221467) D _ v hJ (by decide) (by decide)
  · exact production (k := 67108864) (e := 815237616) D _ v hJ (by decide) (by decide)

/-- The base locus of the five cropped power-fiber witnesses has `2^26-1`
sites. Every list sharing their evaluations there remains below the first-prime
budget even when its messages span a larger space than the five witnesses. -/
theorem cropped_power_base (D : Fin 1073741824 ↪ F) (width : ℕ)
    (J : Finset (Fin 1073741824)) (hJ : J.card = 67108863) (v : Fin 1073741824 → Fin width → F) :
    Lambda (slice D 134217728 width J v) (746721448/1073741824) ≤ 1006632961 :=
  production (k := 134217728) (e := 746721448) D _ v hJ (by decide) (by decide)

#print axioms lambda_le
#print axioms first_open_low_rates
#print axioms common_fiber_low_rates
#print axioms cropped_power_base
end ProximityGap.SharedSiteListBound
