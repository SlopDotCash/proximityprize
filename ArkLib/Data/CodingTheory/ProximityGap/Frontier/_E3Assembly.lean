/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3StrataCount
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3Shape21Scratch
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3SubsetCount
import Mathlib.Tactic

/-! Scratch: the final E₃ strata assembly. Combines the three per-image-size multiplicities
(`image_count_two`=20, `image_count_four`=360, `image_count_six`=720) with the neg-closed subset
count (`negClosed_subset_count`=C(h,i)) over `negSymCount_partition_negClosed`, then closes via
`strata_sum_eq_closed`, yielding `negSymCount G 6 = 15·|G|³ − 45·|G|² + 40·|G|`. -/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset

namespace E3Assembly

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

open ArkLib.ProximityGap.Frontier.E3StrataCount
  (negSymCount image_count_two image_count_six negSymCount_partition_negClosed strata_sum_eq_closed
   balanced_image_neg_closed negClosed_card_even)
open E3Shape21Scratch (image_count_four)
open E3SubsetCount (negClosed_subset_count)

/-- The per-`S` image-count summand of the strata partition. -/
@[reducible] def imgCount (G S : Finset F) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin 6 => G)).filter
    (fun c => (∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                     = (Finset.univ.filter (fun i => c i = -z)).card)
            ∧ Finset.image c Finset.univ = S)).card

/-- `x ≠ 0` in a negation-closed `G` with `0 ∉ G` forces `x ≠ -x` (char ≠ 2). -/
private theorem ne_neg_of_mem {G : Finset F} (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    {x : F} (hx : x ∈ G) : x ≠ -x := by
  intro h
  have hx0 : x ≠ 0 := fun hh => h0 (hh ▸ hx)
  have : (2 : F) * x = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact h2 h'
  · exact hx0 h'

/-- **Size-2 stratum dispatch.** A neg-closed 2-subset `S ⊆ G` is `{x,-x}`; its image-count is `20`. -/
theorem count_two (G S : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hSG : S ⊆ G) (hSneg : ∀ z ∈ S, -z ∈ S) (hScard : S.card = 2) :
    imgCount G S = 20 := by
  classical
  obtain ⟨x, hxS⟩ : ∃ x, x ∈ S := Finset.card_pos.mp (by rw [hScard]; norm_num)
  have hnxS : -x ∈ S := hSneg x hxS
  have hxnx : x ≠ -x := ne_neg_of_mem h2 h0 (hSG hxS)
  have hSeq : S = {x, -x} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro z hz
      rcases Finset.mem_insert.mp hz with h | h
      · exact h ▸ hxS
      · exact (Finset.mem_singleton.mp h) ▸ hnxS
    · rw [hScard, Finset.card_insert_of_notMem (by simp [hxnx]), Finset.card_singleton]
  rw [hSeq]
  exact image_count_two G x hxnx (hSG hxS) (hSG hnxS)

/-- **Size-6 stratum dispatch.** A neg-closed 6-subset `S ⊆ G` has image-count `720`. -/
theorem count_six (G S : Finset F) (hSG : S ⊆ G) (hSneg : ∀ z ∈ S, -z ∈ S) (hScard : S.card = 6) :
    imgCount G S = 720 := image_count_six G S hSG hScard hSneg

/-- **Size-4 stratum dispatch.** A neg-closed 4-subset `S ⊆ G` is `{x,-x,y,-y}`; image-count `360`. -/
theorem count_four (G S : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hSG : S ⊆ G) (hSneg : ∀ z ∈ S, -z ∈ S) (hScard : S.card = 4) :
    imgCount G S = 360 := by
  classical
  obtain ⟨x, hxS⟩ : ∃ x, x ∈ S := Finset.card_pos.mp (by rw [hScard]; norm_num)
  have hnxS : -x ∈ S := hSneg x hxS
  have hxnx : x ≠ -x := ne_neg_of_mem h2 h0 (hSG hxS)
  -- {x,-x} neg-closed; S' = S \ {x,-x} has card 2 and is neg-closed
  have hpairsub : ({x, -x} : Finset F) ⊆ S := by
    intro z hz; rcases Finset.mem_insert.mp hz with h | h
    · exact h ▸ hxS
    · exact (Finset.mem_singleton.mp h) ▸ hnxS
  have hpaircard : ({x, -x} : Finset F).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hxnx]), Finset.card_singleton]
  set S' := S \ {x, -x} with hS'def
  have hS'card : S'.card = 2 := by
    have hinter : ({x, -x} : Finset F) ∩ S = {x, -x} := Finset.inter_eq_left.mpr hpairsub
    rw [hS'def, Finset.card_sdiff, hinter, hScard, hpaircard]
  have hpairneg : ∀ z ∈ ({x, -x} : Finset F), -z ∈ ({x, -x} : Finset F) := by
    intro z hz; rcases Finset.mem_insert.mp hz with h | h
    · subst h; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rw [Finset.mem_singleton.mp h, neg_neg]; exact Finset.mem_insert_self _ _
  have hS'neg : ∀ z ∈ S', -z ∈ S' := by
    intro z hz
    rw [hS'def, Finset.mem_sdiff] at hz ⊢
    refine ⟨hSneg z hz.1, fun hc => hz.2 ?_⟩
    have := hpairneg (-z) hc; rwa [neg_neg] at this
  obtain ⟨y, hyS'⟩ : ∃ y, y ∈ S' := Finset.card_pos.mp (by rw [hS'card]; norm_num)
  have hnyS' : -y ∈ S' := hS'neg y hyS'
  have hyS : y ∈ S := (Finset.mem_sdiff.mp hyS').1
  have hnyS : -y ∈ S := (Finset.mem_sdiff.mp hnyS').1
  have hynp : y ∉ ({x, -x} : Finset F) := (Finset.mem_sdiff.mp hyS').2
  have hnynp : -y ∉ ({x, -x} : Finset F) := (Finset.mem_sdiff.mp hnyS').2
  have hxy : x ≠ y := fun h => hynp (h ▸ Finset.mem_insert_self _ _)
  have hmxy : -x ≠ y := fun h => hynp (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hxy' : x ≠ -y := fun h => hnynp (h ▸ Finset.mem_insert_self _ _)
  have hmxy' : -x ≠ -y := fun h => hnynp (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hy : y ≠ -y := ne_neg_of_mem h2 h0 (hSG hyS)
  have hSeq : S = {x, -x, y, -y} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro z hz
      rcases Finset.mem_insert.mp hz with h | h
      · exact h ▸ hxS
      rcases Finset.mem_insert.mp h with h | h
      · exact h ▸ hnxS
      rcases Finset.mem_insert.mp h with h | h
      · exact h ▸ hyS
      · exact (Finset.mem_singleton.mp h) ▸ hnyS
    · rw [hScard]
      rw [Finset.card_insert_of_notMem (by simp [hxnx, hxy, hxy']),
          Finset.card_insert_of_notMem (by simp [hmxy, hmxy']),
          Finset.card_insert_of_notMem (by simp [hy]), Finset.card_singleton]
  rw [hSeq]
  exact image_count_four G x y hxnx hy hxy hxy' hmxy hmxy'
    (hSG hxS) (hSG hnxS) (hSG hyS) (hSG hnyS)

/-- **Off-stratum dispatch.** A balanced 6-tuple over `G` (`0 ∉ G`, char ≠ 2) has image of even
card in `{2,4,6}` (neg-closed, nonzero, ≤ 6); so for `S` of any other card the image-count is `0`. -/
theorem count_zero (G S : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hc2 : S.card ≠ 2) (hc4 : S.card ≠ 4) (hc6 : S.card ≠ 6) :
    imgCount G S = 0 := by
  classical
  rw [imgCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc
  rw [Fintype.mem_piFinset] at hc
  rintro ⟨hbal, himg⟩
  have h0img : (0 : F) ∉ Finset.image c Finset.univ := by
    intro hh; rw [Finset.mem_image] at hh; obtain ⟨i, _, hi⟩ := hh; exact h0 (hi ▸ hc i)
  have hnegimg : ∀ z ∈ Finset.image c Finset.univ, -z ∈ Finset.image c Finset.univ :=
    fun z hz => balanced_image_neg_closed c hbal hz
  have heven : Even (Finset.image c Finset.univ).card :=
    negClosed_card_even _ h2 h0img hnegimg
  have hle : (Finset.image c Finset.univ).card ≤ 6 := by
    calc (Finset.image c Finset.univ).card ≤ (Finset.univ : Finset (Fin 6)).card :=
          Finset.card_image_le
      _ = 6 := by simp
  have hge : 1 ≤ (Finset.image c Finset.univ).card :=
    Finset.card_pos.mpr ⟨c 0, Finset.mem_image_of_mem c (Finset.mem_univ 0)⟩
  rw [himg] at heven hle hge
  obtain ⟨k, hk⟩ := heven
  omega

/-- `360 · C(h,2) = 180 · h(h−1)` (the (2,1)-stratum cardinality in non-`choose` form). -/
theorem stratum21_card (h : ℕ) : 360 * Nat.choose h 2 = 180 * (h * (h - 1)) := by
  have hdf : Nat.descFactorial h 2 = h * (h - 1) := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]
    simp only [Nat.sub_zero, Nat.mul_one]; ring
  have hdvd : 2 ∣ Nat.descFactorial h 2 := by
    have h2f : (2 : ℕ) = Nat.factorial 2 := rfl
    rw [h2f]; exact Nat.factorial_dvd_descFactorial h 2
  obtain ⟨q, hq⟩ := hdvd
  have hch : Nat.choose h 2 = q := by
    rw [Nat.choose_eq_descFactorial_div_factorial, hq]
    have : Nat.factorial 2 = 2 := rfl
    rw [this]; omega
  rw [hch, ← hdf, hq]; ring

/-- **The char-0 E₃ producer.** For a negation-closed `G ⊆ F` avoiding `0` (char ≠ 2), the count
of negation-symmetric (antipodally count-balanced) 6-tuples over `G` is the exact closed form
`15·|G|³ − 45·|G|² + 40·|G|`. (Over `ℤ` since the polynomial dips below the additive identity.)
This is `E₃(μ_n)` — the 6th period moment input of the r=2 cross-step rung — assembled from the
three per-image multiplicities (20/360/720) and the neg-closed subset count `C(|G|/2, i)`. -/
theorem negSymCount_eq_closed (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ z ∈ G, -z ∈ G) :
    (negSymCount G 6 : ℤ)
      = 15 * (G.card : ℤ) ^ 3 - 45 * (G.card : ℤ) ^ 2 + 40 * (G.card : ℤ) := by
  classical
  obtain ⟨h, hGc⟩ := negClosed_card_even G h2 h0 hneg
  -- The integer value of the count, via partition + per-stratum dispatch + subset counts.
  have hval : negSymCount G 6
      = 20 * Nat.choose h 1 + 360 * Nat.choose h 2 + 720 * Nat.choose h 3 := by
    rw [negSymCount_partition_negClosed]
    -- per-`S` summand = the indicator sum, by dispatch
    have disp : ∀ S ∈ G.powerset.filter (fun S => ∀ z ∈ S, -z ∈ S),
        (((Fintype.piFinset (fun _ : Fin 6 => G)).filter
            (fun c => ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                             = (Finset.univ.filter (fun i => c i = -z)).card)).filter
          (fun c => Finset.image c Finset.univ = S)).card
        = (if S.card = 2 * 1 then 20 else 0) + (if S.card = 2 * 2 then 360 else 0)
          + (if S.card = 2 * 3 then 720 else 0) := by
      intro S hS
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      obtain ⟨hSG, hSneg⟩ := hS
      have heq : (((Fintype.piFinset (fun _ : Fin 6 => G)).filter
            (fun c => ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                             = (Finset.univ.filter (fun i => c i = -z)).card)).filter
          (fun c => Finset.image c Finset.univ = S)).card = imgCount G S := by
        unfold imgCount; rw [Finset.filter_filter]
      rw [heq]
      by_cases hk2 : S.card = 2
      · rw [count_two G S h2 h0 hSG hSneg hk2]; split_ifs <;> omega
      by_cases hk4 : S.card = 4
      · rw [count_four G S h2 h0 hSG hSneg hk4]; split_ifs <;> omega
      by_cases hk6 : S.card = 6
      · rw [count_six G S hSG hSneg hk6]; split_ifs <;> omega
      · rw [count_zero G S h2 h0 hk2 hk4 hk6]; split_ifs <;> omega
    rw [Finset.sum_congr rfl disp, Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- each indicator sum = multiplicity · #{neg-closed 2j-subsets} = multiplicity · C(h,j)
    have sumite : ∀ (j c : ℕ),
        (∑ S ∈ G.powerset.filter (fun S => ∀ z ∈ S, -z ∈ S), if S.card = 2 * j then c else 0)
        = c * Nat.choose h j := by
      intro j c
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      congr 1
      rw [Finset.filter_filter, negClosed_subset_count G h2 h0 hneg j]
      congr 1; omega
    rw [sumite 1 20, sumite 2 360, sumite 3 720]
  -- arithmetic: 20·C(h,1) + 360·C(h,2) + 720·C(h,3) = 15(2h)³ − 45(2h)² + 40(2h), and 2h = |G|
  rw [hval]
  have hc1 : Nat.choose h 1 = h := Nat.choose_one_right h
  have hGz : (G.card : ℤ) = 2 * (h : ℤ) := by rw [hGc]; push_cast; ring
  rw [hGz, ← strata_sum_eq_closed h]
  -- goal: ↑(20·C(h,1) + 360·C(h,2) + 720·C(h,3)) = 20·↑h + 180·(↑h·(↑h−1)) + 720·↑C(h,3)
  have hsub : ((h * (h - 1) : ℕ) : ℤ) = (h : ℤ) * ((h : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos h with rfl | hp
    · simp
    · rw [Nat.cast_mul, Nat.cast_sub hp, Nat.cast_one]
  have h21z : (360 : ℤ) * (Nat.choose h 2 : ℤ) = 180 * ((h : ℤ) * ((h : ℤ) - 1)) := by
    rw [← hsub]; exact_mod_cast stratum21_card h
  push_cast [hc1]
  linarith [h21z]

end E3Assembly

#print axioms E3Assembly.count_two
#print axioms E3Assembly.count_six
#print axioms E3Assembly.count_four
#print axioms E3Assembly.count_zero
#print axioms E3Assembly.negSymCount_eq_closed
