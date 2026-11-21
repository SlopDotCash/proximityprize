/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-!
# Twelve-term squarefree signed relations in the production subgroups

Six-subsets of the first half of each power orbit give more subsets than field
residues. After cancellation, a collision gives a nonempty zero-sum subset of
the actual power orbit, with at most twelve elements and at most one element
from each antipodal pair. Balanced integer occupancy bounds the number of
unordered pairs of six-subsets with equal sums.
-/

set_option autoImplicit false
open Finset

namespace ArkLib.ProximityGap.Frontier.ProductionHalfSubsetRelations

abbrev halfSize : ℕ := 2^29
abbrev fullSize : ℕ := 2^30

variable {F : Type*} [Field F] [DecidableEq F]

/-- Consecutive powers of the specified generator. -/
def window (g : F) (m : ℕ) : Finset F := (range m).image (g ^ ·)

private theorem half_card {g : F} (hg : orderOf g = fullSize) :
    (window g halfSize).card = halfSize := by
  have hsize : fullSize = 2*halfSize := rfl
  rw [window, card_image_of_injOn, card_range]
  intro i hi j hj hij
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  exact pow_injOn_Iio_orderOf (by change i < orderOf g; rw [hg]; omega)
    (by change j < orderOf g; rw [hg]; omega) hij

omit [DecidableEq F] in
private theorem half_neg {g : F} (hg : orderOf g = fullSize) : g^halfSize = -1 := by
  have hs : (g^halfSize)^2 = 1 := by
    rw [← pow_mul]
    change g ^ fullSize = 1
    rw [← hg, pow_orderOf_eq_one]
  rcases sq_eq_one_iff.mp hs with hp | hp
  · have hdiv := orderOf_dvd_of_pow_eq_one hp
    rw [hg] at hdiv
    exact False.elim ((by decide : ¬fullSize ∣ halfSize) hdiv)
  · exact hp

private theorem window_signs {g : F} (hg : orderOf g = fullSize)
    {a : F} (ha : a ∈ window g halfSize) :
    a ∈ window g fullSize ∧ -a ∈ window g fullSize ∧ -a ∉ window g halfSize := by
  have hsize : fullSize = 2*halfSize := rfl
  obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
  have hi' := mem_range.mp hi
  have hpower : g^(halfSize+i) = -(g^i) := by rw [pow_add, half_neg hg, neg_one_mul]
  refine ⟨mem_image.mpr ⟨i, mem_range.mpr (by omega), rfl⟩,
    mem_image.mpr ⟨halfSize+i, mem_range.mpr (by omega), hpower⟩, ?_⟩
  intro hn
  obtain ⟨j, hj, hjp⟩ := mem_image.mp hn
  have hj' := mem_range.mp hj
  have he := pow_injOn_Iio_orderOf (x := g)
    (show j < orderOf g by rw [hg]; omega)
    (show halfSize+i < orderOf g by rw [hg]; omega) (hjp.trans hpower.symm)
  omega

/-- A finite zero-sum subset of the named power orbit with distinct antipodal classes. -/
def ShortZero (g : F) : Prop :=
  ∃ U : Finset F, U.Nonempty ∧ U.card ≤ 12 ∧ U ⊆ window g fullSize ∧
    (∀ x ∈ U, -x ∉ U) ∧ ∑ x ∈ U, x = 0

theorem shortZero_of_card [Fintype F] {g : F} (hg : orderOf g = fullSize)
    (hbig : Fintype.card F < halfSize.choose 6) : ShortZero g := by
  classical
  let W := window g halfSize
  let X := W.powersetCard 6
  have hcard : (univ : Finset F).card < X.card := by
    simpa [X, W, half_card hg] using hbig
  obtain ⟨S, hS, T, hT, hne, he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun A : Finset F => ∑ a ∈ A, a) hcard (fun _ _ => mem_univ _)
  obtain ⟨hSW, hSc⟩ := mem_powersetCard.mp hS
  obtain ⟨hTW, hTc⟩ := mem_powersetCard.mp hT
  let A := S \ T
  let B := T \ S
  have hA : A ⊆ W := fun _ hx => hSW (mem_sdiff.mp hx).1
  have hB : B ⊆ W := fun _ hx => hTW (mem_sdiff.mp hx).1
  have hAB : Disjoint A B := disjoint_left.mpr (fun _ ha hb => (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1)
  have hABsum : ∑ x ∈ A, x = ∑ x ∈ B, x := sum_sdiff_eq_sum_sdiff_iff.mpr he
  have hAn : A.Nonempty := by
    by_contra hn
    have hsub : S ⊆ T := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hn)
    exact hne (eq_of_subset_of_card_le hsub (by omega))
  have hAdB : Disjoint A (B.image (- ·)) := by
    apply disjoint_left.mpr
    intro x hx hnx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hnx
    exact (window_signs hg (hB hv)).2.2 (hA hx)
  refine ⟨A ∪ B.image (- ·), hAn.mono subset_union_left, ?_, ?_, ?_, ?_⟩
  · rw [card_union_of_disjoint hAdB, card_image_of_injective _ neg_injective]
    have ha : A.card ≤ S.card := card_le_card sdiff_subset
    have hb : B.card ≤ T.card := card_le_card sdiff_subset
    omega
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact (window_signs hg (hA hx)).1
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact (window_signs hg (hB hv)).2.1
  · intro x hx hn
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hn with hn | hn
    · exact (window_signs hg (hA hx)).2.2 (hA hn)
    · obtain ⟨v, hv, heq⟩ := mem_image.mp hn
      exact disjoint_left.mp hAB hx ((neg_injective heq) ▸ hv)
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact disjoint_left.mp hAB (by simpa using hn) hv
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      obtain ⟨w, hw, heq⟩ := mem_image.mp hn
      have hred : -w = v := by simpa using heq
      exact (window_signs hg (hB hw)).2.2 (hred ▸ hB hv)
  · rw [sum_union hAdB, sum_image (fun _ _ _ _ h => neg_injective h)]
    change (∑ x ∈ A, x) + (∑ x ∈ B, -x) = 0
    rw [Finset.sum_neg_distrib (fun x : F => x), hABsum, add_neg_cancel]

theorem six_subset_count : halfSize.choose 6 =
    33257280773621061829797459504797335680374626320384 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- The number of unordered distinct six-subset pairs with equal sums, counted in each residue. -/
noncomputable def collisions [Fintype F] (g : F) : ℕ :=
  ∑ y : F, (((window g halfSize).powersetCard 6).filter (fun S => (∑ x ∈ S, x) = y)).card.choose 2

private theorem twice_choose (x : ℕ) : 2*(x.choose 2 : ℤ) = (x:ℤ)*((x:ℤ)-1) := by
  cases x with
  | zero => norm_num
  | succ x =>
    have h := Nat.choose_succ_right_eq (x+1) 1
    simp only [Nat.choose_one_right, Nat.add_sub_cancel] at h
    have hc : (((x+1).choose 2 : ℕ):ℤ)*2 = ((x:ℤ)+1)*x := by exact_mod_cast h
    push_cast
    linarith

private theorem binomial_tangent (x k : ℕ) :
    k*x ≤ x.choose 2 + (k+1).choose 2 := by
  have hx := twice_choose x
  have hk := twice_choose (k+1)
  push_cast at hk
  apply Int.ofNat_le.mp
  push_cast
  by_cases h : (x:ℤ) ≤ (k:ℤ)
  · nlinarith [mul_nonneg (show 0 ≤ (k:ℤ)-x by omega) (show 0 ≤ (k:ℤ)+1-x by omega)]
  · nlinarith [mul_nonneg (show 0 ≤ (x:ℤ)-k by omega) (show 0 ≤ (x:ℤ)-k-1 by omega)]

/-- Integer occupancy tangent, sharp when all fiber sizes equal either k or k+1. -/
theorem occupancy [Fintype F] (g : F) (hg : orderOf g = fullSize) (k : ℕ) :
    k*(halfSize.choose 6) ≤ collisions g + Fintype.card F * (k+1).choose 2 := by
  let X := (window g halfSize).powersetCard 6
  let load (y : F) := (X.filter (fun S => (∑ x ∈ S, x) = y)).card
  have htot : ∑ y, load y = halfSize.choose 6 := by
    simpa [load, X, half_card hg] using
      (sum_card_fiberwise_eq_card_filter X (univ : Finset F) (fun S => ∑ x ∈ S, x))
  have h := Finset.sum_le_sum (s := (univ : Finset F))
    (fun y _ => binomial_tangent (load y) k)
  have hcoll : (∑ y, (load y).choose 2) = collisions g := rfl
  simpa only [← Finset.mul_sum, htot, Finset.sum_add_distrib, hcoll, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Nat.cast_id] using h

open ArkLib.ProximityGap
local instance : Fact PrizeShapePrimeP30.P.Prime := ⟨PrizeShapePrimeP30.prime_P⟩
local instance : Fact PrizeShapePrimeP30Second.P.Prime := ⟨PrizeShapePrimeP30Second.prime_P⟩

/-- The actual subgroup of the first prime has a squarefree antipodal relation of length ≤ 12. -/
theorem first_shortZero : ShortZero PrizeShapePrimeP30.g := by
  apply shortZero_of_card PrizeShapePrimeP30.orderOf_g
  rw [ZMod.card, six_subset_count]
  decide +kernel

/-- The actual subgroup of the second prime has a squarefree antipodal relation of length ≤ 12. -/
theorem second_shortZero : ShortZero PrizeShapePrimeP30Second.g := by
  apply shortZero_of_card PrizeShapePrimeP30Second.orderOf_g
  rw [ZMod.card, six_subset_count]
  decide +kernel

theorem first_collision_count :
    1496951086932726722611412637498967365981178400075686 ≤ collisions PrizeShapePrimeP30.g := by
  have h := occupancy _ PrizeShapePrimeP30.orderOf_g 91
  rw [six_subset_count, ZMod.card, Nat.choose_eq_descFactorial_div_factorial] at h
  norm_num [PrizeShapePrimeP30.P, Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  omega

theorem second_collision_count :
    740250537494205522170478776785203642930465897184245 ≤ collisions PrizeShapePrimeP30Second.g := by
  have h := occupancy _ PrizeShapePrimeP30Second.orderOf_g 45
  rw [six_subset_count, ZMod.card, Nat.choose_eq_descFactorial_div_factorial] at h
  norm_num [PrizeShapePrimeP30Second.P, Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  omega

/-- Unordered pairs of distinct six-subsets of the half-window with the same field sum. -/
noncomputable def pairs [Fintype F] (g : F) : Finset (Sym2 (Finset F)) :=
  univ.biUnion fun y : F =>
    ((((window g halfSize).powersetCard 6).filter (fun S => (∑ x ∈ S, x) = y)).offDiag.image
      Sym2.mk.uncurry)

private theorem pair_card [Fintype F] (g : F) : (pairs g).card = collisions g := by
  classical
  unfold pairs
  rw [card_biUnion]
  · simp [Sym2.card_image_offDiag, collisions]
  · intro y _ z _ hyz
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨⟨A,B⟩, hab, rfl⟩ := mem_image.mp hp
    obtain ⟨⟨U,V⟩, huv, he⟩ := mem_image.mp hq
    obtain ⟨ha, hb, _⟩ := mem_offDiag.mp hab
    obtain ⟨hu, _, _⟩ := mem_offDiag.mp huv
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hyz ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hu).2)
    · exact hyz ((mem_filter.mp hb).2.symm.trans (mem_filter.mp hu).2)

private theorem pair_rep [Fintype F] (g : F) {p : Sym2 (Finset F)} (hp : p ∈ pairs g) :
    ∃ A B : Finset F, p = s(A,B) ∧ A ⊆ window g halfSize ∧ B ⊆ window g halfSize ∧
      A.card = 6 ∧ B.card = 6 ∧ A ≠ B ∧ (∑ x ∈ A, x) = ∑ x ∈ B, x := by
  obtain ⟨y, _, hy⟩ := mem_biUnion.mp hp
  obtain ⟨⟨A,B⟩, hab, rfl⟩ := mem_image.mp hy
  obtain ⟨ha, hb, hn⟩ := mem_offDiag.mp hab
  obtain ⟨ha, he⟩ := mem_filter.mp ha
  obtain ⟨hb, hf⟩ := mem_filter.mp hb
  obtain ⟨ha, hca⟩ := mem_powersetCard.mp ha
  obtain ⟨hb, hcb⟩ := mem_powersetCard.mp hb
  exact ⟨_, _, rfl, ha, hb, hca, hcb, hn, he.trans hf.symm⟩

/-- Cancel the intersection of a pair of subsets, independently of its ordering. -/
def reduce {α : Type*} [DecidableEq α] : Sym2 (Finset α) → Sym2 (Finset α) :=
  Sym2.lift ⟨fun A B => s(A\B,B\A), fun _ _ => Sym2.eq_swap⟩

private def common {α : Type*} [DecidableEq α] : Sym2 (Finset α) → Finset α :=
  Sym2.lift ⟨(· ∩ ·), inter_comm⟩

private theorem reconstruct {α : Type*} [DecidableEq α] (p : Sym2 (Finset α)) :
    (reduce p).map (· ∪ common p) = p := by
  induction p using Sym2.inductionOn with
  | _ A B =>
    change s(A \ B ∪ A ∩ B, B \ A ∪ A ∩ B) = s(A,B)
    rw [sdiff_union_inter A B, inter_comm A B, sdiff_union_inter B A]

/-- Actual distinct reduced relations counted up to reversal. -/
noncomputable def reducedPairs [Fintype F] (g : F) : Finset (Sym2 (Finset F)) :=
  (pairs g).image reduce

private theorem depth_ge_two {A B : Finset F} (hca : A.card = 6) (hcb : B.card = 6)
    (hne : A ≠ B) (hs : (∑ x ∈ A, x) = ∑ x ∈ B, x) : 2 ≤ (A\B).card := by
  have he : (A\B).card = (B\A).card := by rw [card_sdiff, card_sdiff, inter_comm A B, hca, hcb]
  by_contra! hlo
  interval_cases hh : (A\B).card
  · have hsub := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hh)
    exact hne (eq_of_subset_of_card_le hsub (by omega))
  · obtain ⟨a, ha⟩ := card_eq_one.mp hh
    obtain ⟨b, hb⟩ := card_eq_one.mp he.symm
    have hs' : (∑ x ∈ A\B, x) = ∑ x ∈ B\A, x := sum_sdiff_eq_sum_sdiff_iff.mpr hs
    simp [ha, hb] at hs'
    subst b
    have h1 : a ∈ A\B := by simp [ha]
    have h2 : a ∈ B\A := by simp [hb]
    exact (mem_sdiff.mp h1).2 (mem_sdiff.mp h2).1

private theorem fiber_cap [Fintype F] (g : F) (hg : orderOf g = fullSize)
    (lower : ℕ) (hdepth : ∀ A B : Finset F, A ⊆ window g halfSize → B ⊆ window g halfSize →
      A.card = 6 → B.card = 6 → A ≠ B → (∑ x ∈ A, x) = (∑ x ∈ B, x) → lower ≤ (A\B).card)
    {P : Sym2 (Finset F)} (hP : P ∈ reducedPairs g) :
    ∃ d, lower ≤ d ∧ d ≤ 6 ∧
      ((pairs g).filter (reduce · = P)).card ≤ (halfSize-2*d).choose (6-d) := by
  classical
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hP
  obtain ⟨A, B, rfl, hA, hB, hca, hcb, hne, hs⟩ := pair_rep g hp
  let U := A\B
  let V := B\A
  have huv : U.card = V.card := by
    simp only [U, V, card_sdiff, inter_comm A B, hca, hcb]
  have hdis : Disjoint U V := disjoint_left.mpr (fun _ hu hv => (mem_sdiff.mp hu).2 (mem_sdiff.mp hv).1)
  let Z := window g halfSize \ (U ∪ V)
  have hZ : Z.card = halfSize-2*U.card := by
    have hh : U ∪ V ⊆ window g halfSize :=
      union_subset (fun _ hx => hA (mem_sdiff.mp hx).1) (fun _ hx => hB (mem_sdiff.mp hx).1)
    dsimp only [Z]
    rw [card_sdiff_of_subset hh, half_card hg, card_union_of_disjoint hdis, ← huv, two_mul]
  refine ⟨U.card, hdepth A B hA hB hca hcb hne hs, (card_le_card sdiff_subset).trans hca.le, ?_⟩
  rw [← hZ, ← card_powersetCard]
  apply card_le_card_of_injOn common
  · intro q hq
    obtain ⟨hq, he⟩ := mem_filter.mp hq
    obtain ⟨S,T,rfl,hS,_,hcS,hcT,_,_⟩ := pair_rep g hq
    change s(S\T,T\S) = s(U,V) at he
    change S ∩ T ∈ Z.powersetCard (6-U.card)
    obtain hh | hh := Sym2.eq_iff.mp he <;> obtain ⟨h1,h2⟩ := hh
    all_goals
      apply mem_powersetCard.mpr
      constructor
      · intro x hx
        obtain ⟨hsx,htx⟩ := mem_inter.mp hx
        refine mem_sdiff.mpr ⟨hS hsx, ?_⟩
        simp [← h1, ← h2, hsx, htx]
      · have hcs := card_sdiff_add_card_inter S T
        rw [h1, hcS] at hcs
        omega
  · intro p hp q hq he
    obtain ⟨_, hpr⟩ := mem_filter.mp hp
    obtain ⟨_, hqr⟩ := mem_filter.mp hq
    rw [← reconstruct p, ← reconstruct q, hpr, hqr, he]

private theorem lift_bound (d : ℕ) (hlo : 2 ≤ d) (hhi : d ≤ 6) :
    (halfSize-2*d).choose (6-d) ≤ 3461531097175924400622048913653795 := by
  interval_cases d <;> rw [Nat.choose_eq_descFactorial_div_factorial] <;> decide +kernel

/-- Every unordered collision reduces to a class with at most this many six-subset lifts. -/
theorem collisions_le_reduced [Fintype F] (g : F) (hg : orderOf g = fullSize) :
    collisions g ≤ (reducedPairs g).card * 3461531097175924400622048913653795 := by
  rw [← pair_card, card_eq_sum_card_image reduce (pairs g)]
  calc
    _ ≤ ∑ _ ∈ reducedPairs g, 3461531097175924400622048913653795 := by
      apply sum_le_sum
      intro z hz
      obtain ⟨d, hd, hu, hc⟩ := fiber_cap g hg 2
        (fun _ _ _ _ hca hcb hn hs => depth_ge_two hca hcb hn hs) hz
      exact hc.trans (lift_bound d hd hu)
    _ = _ := by simp

theorem first_reduced_count : 432453456262174845 ≤ (reducedPairs PrizeShapePrimeP30.g).card := by
  have h := collisions_le_reduced _ PrizeShapePrimeP30.orderOf_g
  have hc := first_collision_count
  omega

theorem second_reduced_count : 213850610239537011 ≤ (reducedPairs PrizeShapePrimeP30Second.g).card := by
  have h := collisions_le_reduced _ PrizeShapePrimeP30Second.orderOf_g
  have hc := second_collision_count
  omega

/-- Two-subsets of the antipode-free half have distinct sums under the weak Sidon hypothesis. -/
def PairSumInjective (g : F) : Prop :=
  Set.InjOn (fun A : Finset F => ∑ x ∈ A, x)
    (((window g halfSize).powersetCard 2 : Finset (Finset F)) : Set (Finset F))

/-- Weak Sidon on the full subgroup gives injectivity on two-subsets of its half. -/
theorem pairSumInjective_of_weakSidon (g : F) (hg : orderOf g = fullSize)
    (h : ∀ a ∈ window g fullSize, ∀ b ∈ window g fullSize, ∀ c ∈ window g fullSize,
      ∀ d ∈ window g fullSize, a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ a+b = 0) : PairSumInjective g := by
  intro S hS T hT he
  obtain ⟨hs, hcS⟩ := mem_powersetCard.mp hS
  obtain ⟨ht, hcT⟩ := mem_powersetCard.mp hT
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hcS
  obtain ⟨c,d,hcd,rfl⟩ := card_eq_two.mp hcT
  have ha := window_signs hg (hs (mem_insert_self a _))
  have hb := window_signs hg (hs (mem_insert_of_mem (mem_singleton_self b)))
  have hc := window_signs hg (ht (mem_insert_self c _))
  have hd := window_signs hg (ht (mem_insert_of_mem (mem_singleton_self d)))
  have heq : a+b = c+d := by simpa [hab, hcd] using he
  rcases h a ha.1 b hb.1 c hc.1 d hd.1 heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | hz
  · rfl
  · exact pair_comm _ _
  · have hneg : -a = b := by linear_combination -hz
    exact (ha.2.2 (hneg ▸ hs (mem_insert_of_mem (mem_singleton_self b)))).elim

private theorem depth_ge_three {g : F} (hinj : PairSumInjective g) {A B : Finset F}
    (hA : A ⊆ window g halfSize) (hB : B ⊆ window g halfSize)
    (hca : A.card = 6) (hcb : B.card = 6) (hne : A ≠ B)
    (hs : (∑ x ∈ A, x) = ∑ x ∈ B, x) : 3 ≤ (A\B).card := by
  have hlo := depth_ge_two hca hcb hne hs
  by_contra! h
  have htwo : (A\B).card = 2 := by omega
  have he : (A\B).card = (B\A).card := by rw [card_sdiff, card_sdiff, inter_comm A B, hca, hcb]
  have eq := hinj (mem_powersetCard.mpr ⟨sdiff_subset.trans hA, htwo⟩)
    (mem_powersetCard.mpr ⟨sdiff_subset.trans hB, he.symm.trans htwo⟩)
    (sum_sdiff_eq_sum_sdiff_iff.mpr hs)
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < (A\B).card)
  exact (mem_sdiff.mp hx).2 (mem_sdiff.mp (eq ▸ hx)).1

private theorem lift_bound_sidon (d : ℕ) (hlo : 3 ≤ d) (hhi : d ≤ 6) :
    (halfSize-2*d).choose (6-d) ≤ 25790416476305785593266120 := by
  interval_cases d <;> rw [Nat.choose_eq_descFactorial_div_factorial] <;> decide +kernel

/-- The sharper reduction multiplicity when the two-subset sums are injective. -/
theorem collisions_le_reduced_of_pairSumInjective [Fintype F] (g : F)
    (hg : orderOf g = fullSize) (hi : PairSumInjective g) :
    collisions g ≤ (reducedPairs g).card * 25790416476305785593266120 := by
  rw [← pair_card, card_eq_sum_card_image reduce (pairs g)]
  calc
    _ ≤ ∑ _ ∈ reducedPairs g, 25790416476305785593266120 := by
      apply sum_le_sum
      intro z hz
      obtain ⟨d, hd, hu, hc⟩ := fiber_cap g hg 3
        (fun _ _ hA hB hca hcb hn hs => depth_ge_three hi hA hB hca hcb hn hs) hz
      exact hc.trans (lift_bound_sidon d hd hu)
    _ = _ := by simp

theorem first_reduced_count_of_pairSumInjective (hi : PairSumInjective PrizeShapePrimeP30.g) :
    58042920257143118257788465 ≤ (reducedPairs PrizeShapePrimeP30.g).card := by
  have h := collisions_le_reduced_of_pairSumInjective _ PrizeShapePrimeP30.orderOf_g hi
  have hc := first_collision_count
  omega

theorem second_reduced_count_of_pairSumInjective (hi : PairSumInjective PrizeShapePrimeP30Second.g) :
    28702542984301541995609681 ≤ (reducedPairs PrizeShapePrimeP30Second.g).card := by
  have h := collisions_le_reduced_of_pairSumInjective _ PrizeShapePrimeP30Second.orderOf_g hi
  have hc := second_collision_count
  omega

#print axioms pairSumInjective_of_weakSidon
#print axioms first_reduced_count_of_pairSumInjective
#print axioms second_reduced_count_of_pairSumInjective

#print axioms collisions_le_reduced
#print axioms first_reduced_count
#print axioms second_reduced_count

#print axioms shortZero_of_card
#print axioms six_subset_count
#print axioms occupancy
#print axioms first_shortZero
#print axioms second_shortZero
#print axioms first_collision_count
#print axioms second_collision_count

end ArkLib.ProximityGap.Frontier.ProductionHalfSubsetRelations
