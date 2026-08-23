/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G101ExactSignedDepthWeld

/-!
# G114: full-depth population normal form

At maximal cancellation depth, the two endpoint value bags are disjoint.  Consequently the
unrestricted population fiber can be counted by first choosing the left endpoint and then choosing
every right coordinate outside its support.  This isolates the deterministic population term in
the G101 signed anomaly from the genuinely arithmetic equal-sum term.

Issue #466.  This is an exact combinatorial reduction, not a CORE closure claim.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G114DepthThreePopulationNormalForm

open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G96DepthMomentWeld

variable {α : Type*} [DecidableEq α]

/-- Full cancellation depth is exactly disjointness of the endpoint value bags. -/
theorem cancelDepth_eq_length_iff_disjoint {r : ℕ} (a b : Fin r → α) :
    cancelDepth (a, b) = r ↔ Disjoint (valueBag a) (valueBag b) := by
  have hreconstruct := congrArg Multiset.card (left_reconstruct (valueBag a) (valueBag b))
  have hbag : (valueBag a).card = r := by simp [valueBag]
  rw [Multiset.card_add, hbag] at hreconstruct
  change (leftCore (valueBag a) (valueBag b)).card = r ↔ _
  constructor
  · intro h
    have hzero : (commonPart (valueBag a) (valueBag b)).card = 0 := by omega
    rw [← Multiset.inter_eq_zero_iff_disjoint]
    apply Multiset.card_eq_zero.mp
    exact hzero
  · intro h
    rw [← Multiset.inter_eq_zero_iff_disjoint] at h
    have hzero : (commonPart (valueBag a) (valueBag b)).card = 0 := by
      simp [commonPart, h]
    omega

/-- Values available to a disjoint right endpoint after fixing the left endpoint. -/
def complementOfBag (G : Finset α) {r : ℕ} (a : Fin r → α) : Finset α :=
  G \ (valueBag a).toFinset

theorem mem_pi_complementOfBag_iff_disjoint
    (G : Finset α) {r : ℕ} (a b : Fin r → α) :
    b ∈ Fintype.piFinset (fun _ : Fin r => complementOfBag G a) ↔
      b ∈ Fintype.piFinset (fun _ : Fin r => G) ∧ Disjoint (valueBag a) (valueBag b) := by
  simp only [Fintype.mem_piFinset, complementOfBag, Finset.mem_sdiff,
    Multiset.mem_toFinset, valueBag]
  constructor
  · intro hb
    refine ⟨fun i => (hb i).1, ?_⟩
    rw [Multiset.disjoint_iff_ne]
    intro x hx y hy
    obtain ⟨i, hi⟩ : ∃ i, a i = x := by simpa [valueBag] using hx
    obtain ⟨j, hj⟩ : ∃ j, b j = y := by simpa [valueBag] using hy
    subst x
    subst y
    exact fun h => (hb j).2 (by simpa [valueBag] using ⟨i, h⟩)
  · rintro ⟨hbG, hd⟩ i
    refine ⟨hbG i, ?_⟩
    intro hi
    rw [Multiset.disjoint_iff_ne] at hd
    obtain ⟨j, hj⟩ : ∃ j, a j = b i := by simpa [valueBag] using hi
    exact hd (a j) (by simp) (b i) (by simp) hj

/-- Exact full-depth population count after conditioning on the left endpoint. -/
theorem allPairsDepthFiber_full_eq_sum_complements
    (G : Finset α) (r : ℕ) :
    allPairsDepthFiber G r r =
      ∑ a ∈ Fintype.piFinset (fun _ : Fin r => G), (complementOfBag G a).card ^ r := by
  classical
  let S := Fintype.piFinset (fun _ : Fin r => G)
  have hinner (a : Fin r → α) :
      (∑ b ∈ S, if Disjoint (valueBag a) (valueBag b) then (1 : ℕ) else 0) =
        (complementOfBag G a).card ^ r := by
    calc
      (∑ b ∈ S, if Disjoint (valueBag a) (valueBag b) then (1 : ℕ) else 0) =
          ∑ b ∈ (S.filter fun b => Disjoint (valueBag a) (valueBag b)), 1 := by
            rw [Finset.sum_filter]
      _ = (S.filter (fun b => Disjoint (valueBag a) (valueBag b))).card := by
            rw [Finset.card_eq_sum_ones]
      _ = (Fintype.piFinset (fun _ : Fin r => complementOfBag G a)).card := by
            congr 1
            ext b
            simp only [Finset.mem_filter]
            exact (mem_pi_complementOfBag_iff_disjoint G a b).symm
      _ = (complementOfBag G a).card ^ r := Fintype.card_piFinset_const _ _
  unfold allPairsDepthFiber
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  simp only [cancelDepth_eq_length_iff_disjoint]
  exact Finset.sum_congr rfl fun a _ => hinner a

/-- Right endpoints which are both support-disjoint from `a` and have the same additive sum. -/
def disjointEqualSumRightFiber [AddCommMonoid α]
    (G : Finset α) {r : ℕ} (a : Fin r → α) : Finset (Fin r → α) :=
  (Fintype.piFinset fun _ : Fin r => complementOfBag G a).filter fun b =>
    ∑ i, b i = ∑ i, a i

/-- Exact full-depth equal-sum count after conditioning on the left endpoint. -/
theorem depthFiber_full_eq_sum_disjointEqualSumRightFiber
    [AddCommMonoid α] (G : Finset α) (r : ℕ) :
    depthFiber G r r =
      ∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
        (disjointEqualSumRightFiber G a).card := by
  classical
  let S := Fintype.piFinset (fun _ : Fin r => G)
  have hcarrier :
      (energySet G r).filter (fun x => cancelDepth x = r) =
        (S ×ˢ S).filter fun x =>
          (∑ i, x.1 i = ∑ i, x.2 i) ∧ Disjoint (valueBag x.1) (valueBag x.2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_product, energySet, Fintype.mem_piFinset]
    have hc : cancelDepth x = r ↔ Disjoint (valueBag x.1) (valueBag x.2) :=
      cancelDepth_eq_length_iff_disjoint x.1 x.2
    rw [hc]
    simp only [S, Fintype.mem_piFinset]
    aesop
  have hinner (a : Fin r → α) :
      (S.filter fun b =>
          (∑ i, a i = ∑ i, b i) ∧ Disjoint (valueBag a) (valueBag b)).card =
        (disjointEqualSumRightFiber G a).card := by
    congr 1
    ext b
    simp only [Finset.mem_filter, disjointEqualSumRightFiber]
    constructor
    · rintro ⟨hbS, hsum, hd⟩
      exact ⟨(mem_pi_complementOfBag_iff_disjoint G a b).2 ⟨hbS, hd⟩, hsum.symm⟩
    · rintro ⟨hb, hsum⟩
      obtain ⟨hbS, hd⟩ := (mem_pi_complementOfBag_iff_disjoint G a b).1 hb
      exact ⟨hbS, hsum.symm, hd⟩
  rw [depthFiber, hcarrier, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]
  calc
    (∑ a ∈ S, ∑ b ∈ S,
        if (∑ i, a i = ∑ i, b i) ∧ Disjoint (valueBag a) (valueBag b)
        then 1 else 0) =
        ∑ a ∈ S, (S.filter fun b =>
          (∑ i, a i = ∑ i, b i) ∧ Disjoint (valueBag a) (valueBag b)).card := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ a ∈ S, (disjointEqualSumRightFiber G a).card := by
          exact Finset.sum_congr rfl fun a _ => hinner a

/-- The full-depth G101 anomaly is precisely a restricted equal-sum discrepancy. -/
theorem actualDepthAnomaly_full_eq_restricted_discrepancy
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ) :
    G101ExactSignedDepthWeld.actualDepthAnomaly G r r =
      (Fintype.card F : ℤ) *
          (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
            (disjointEqualSumRightFiber G a).card : ℕ) -
        (∑ a ∈ Fintype.piFinset (fun _ : Fin r => G),
          (complementOfBag G a).card ^ r : ℕ) := by
  rw [G101ExactSignedDepthWeld.actualDepthAnomaly,
    depthFiber_full_eq_sum_disjointEqualSumRightFiber,
    allPairsDepthFiber_full_eq_sum_complements]
  rfl

/-! ## The length-three population polynomial -/

/-- Length-three words with a one-point support. -/
def constantThreeWords (G : Finset α) : Finset (Fin 3 → α) :=
  (Fintype.piFinset fun _ : Fin 3 => G).filter fun a => a 0 = a 1 ∧ a 1 = a 2

/-- Length-three words with a three-point support. -/
def injectiveThreeWords (G : Finset α) : Finset (Fin 3 → α) :=
  (Fintype.piFinset fun _ : Fin 3 => G).filter Function.Injective

/-- Length-three words with a two-point support. -/
def twoSupportThreeWords (G : Finset α) : Finset (Fin 3 → α) :=
  (Fintype.piFinset fun _ : Fin 3 => G).filter fun a =>
    ¬(a 0 = a 1 ∧ a 1 = a 2) ∧ ¬Function.Injective a

theorem card_constantThreeWords (G : Finset α) :
    (constantThreeWords G).card = G.card := by
  classical
  refine Finset.card_nbij' (fun a => a 0) (fun x _ => x) ?_ ?_ ?_ ?_
  · intro a ha
    have ha' : a ∈ constantThreeWords G := ha
    rw [constantThreeWords, Finset.mem_filter] at ha'
    exact Fintype.mem_piFinset.mp ha'.1 0
  · intro x hx
    simp [constantThreeWords, Fintype.mem_piFinset]
    simpa using hx
  · intro a ha
    simp [constantThreeWords] at ha
    funext i
    fin_cases i
    · rfl
    · simpa using ha.2.1
    · simpa using ha.2.1.trans ha.2.2
  · intro x _
    rfl

theorem card_injectiveThreeWords (G : Finset α) :
    (injectiveThreeWords G).card = G.card.descFactorial 3 := by
  classical
  let T := {x : α // x ∈ G}
  let target : Finset (Fin 3 ↪ T) := Finset.univ
  have hcardTarget : target.card = G.card.descFactorial 3 := by
    simp [target, T, Fintype.card_embedding_eq]
  rw [← hcardTarget]
  refine Finset.card_bij
    (fun a ha =>
      { toFun := fun i => ⟨a i, (Fintype.mem_piFinset.mp (Finset.mem_filter.mp ha).1) i⟩
        inj' := fun i j hij =>
          (Finset.mem_filter.mp ha).2 (congrArg Subtype.val hij) }) ?_ ?_ ?_
  · intro a ha
    simp [target]
  · intro a ha b hb hab
    funext i
    exact congrArg Subtype.val (DFunLike.congr_fun hab i)
  · intro e _
    let a : Fin 3 → α := fun i => (e i).1
    have ha : a ∈ injectiveThreeWords G := by
      simp only [injectiveThreeWords, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => (e i).2, ?_⟩
      intro i j hij
      exact e.injective (Subtype.ext hij)
    refine ⟨a, ha, ?_⟩
    ext i
    rfl

theorem valueBag_toFinset_fin3 (a : Fin 3 → α) :
    (valueBag a).toFinset = {a 0, a 1, a 2} := by
  ext x
  simp [valueBag]

theorem card_support_one_of_constant {a : Fin 3 → α}
    (h : a 0 = a 1 ∧ a 1 = a 2) : (valueBag a).toFinset.card = 1 := by
  rw [valueBag_toFinset_fin3]
  simp [h.1, h.2]

theorem card_support_three_of_injective {a : Fin 3 → α}
    (h : Function.Injective a) : (valueBag a).toFinset.card = 3 := by
  have h01 : a 0 ≠ a 1 := fun h01 => by
    have : (0 : Fin 3) = 1 := h h01
    omega
  have h02 : a 0 ≠ a 2 := fun h02 => by
    have : (0 : Fin 3) = 2 := h h02
    omega
  have h12 : a 1 ≠ a 2 := fun h12 => by
    have : (1 : Fin 3) = 2 := h h12
    omega
  rw [valueBag_toFinset_fin3]
  simp [h01, h02, h12]

theorem card_support_two_of_neither {a : Fin 3 → α}
    (hc : ¬(a 0 = a 1 ∧ a 1 = a 2))
    (hi : ¬Function.Injective a) : (valueBag a).toFinset.card = 2 := by
  rw [valueBag_toFinset_fin3]
  by_cases h01 : a 0 = a 1
  · have h12 : a 1 ≠ a 2 := fun h => hc ⟨h01, h⟩
    simp [h01, h12]
  · by_cases h02 : a 0 = a 2
    · have h12 : a 1 ≠ a 2 := fun h => h01 (h02.trans h.symm)
      simp [h02, h12]
    · by_cases h12 : a 1 = a 2
      · simp [h02, h12]
      · exfalso
        apply hi
        intro i j hij
        fin_cases i <;> fin_cases j
        all_goals simp_all

omit [DecidableEq α] in
theorem injective_not_constant {a : Fin 3 → α} (hi : Function.Injective a) :
    ¬(a 0 = a 1 ∧ a 1 = a 2) := by
  rintro ⟨h01, _⟩
  have : (0 : Fin 3) = 1 := hi h01
  omega

theorem card_twoSupportThreeWords (G : Finset α) :
    (twoSupportThreeWords G).card =
      G.card ^ 3 - G.card - G.card.descFactorial 3 := by
  classical
  let S := Fintype.piFinset (fun _ : Fin 3 => G)
  let C : (Fin 3 → α) → Prop := fun a => a 0 = a 1 ∧ a 1 = a 2
  let I : (Fin 3 → α) → Prop := Function.Injective
  have htotal : S.card = G.card ^ 3 := Fintype.card_piFinset_const _ _
  have hC : (S.filter C).card = G.card := by
    simpa [S, C, constantThreeWords] using card_constantThreeWords G
  have hI : (S.filter I).card = G.card.descFactorial 3 := by
    simpa [S, I, injectiveThreeWords] using card_injectiveThreeWords G
  have hpartC := Finset.card_filter_add_card_filter_not (s := S) C
  have hpartI := Finset.card_filter_add_card_filter_not
    (s := S.filter fun a => ¬C a) I
  have hIfilter : (S.filter fun a => ¬C a).filter I = S.filter I := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨ha, hi⟩
      exact ⟨⟨ha, injective_not_constant hi⟩, hi⟩
  have hMfilter :
      (S.filter fun a => ¬C a).filter (fun a => ¬I a) = twoSupportThreeWords G := by
    ext a
    simp [S, C, I, twoSupportThreeWords, and_assoc]
  rw [hIfilter, hMfilter] at hpartI
  omega

private theorem support_subset_of_mem_pi {G : Finset α} {r : ℕ} {a : Fin r → α}
    (ha : a ∈ Fintype.piFinset fun _ : Fin r => G) : (valueBag a).toFinset ⊆ G := by
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, a i = x := by simpa [valueBag] using hx
  rw [← hi]
  exact Fintype.mem_piFinset.mp ha i

theorem card_complementOfBag_constantThree
    (G : Finset α) {a : Fin 3 → α}
    (ha : a ∈ Fintype.piFinset fun _ : Fin 3 => G)
    (hc : a 0 = a 1 ∧ a 1 = a 2) :
    (complementOfBag G a).card = G.card - 1 := by
  rw [complementOfBag, Finset.card_sdiff_of_subset (support_subset_of_mem_pi ha),
    card_support_one_of_constant hc]

theorem card_complementOfBag_injectiveThree
    (G : Finset α) {a : Fin 3 → α}
    (ha : a ∈ Fintype.piFinset fun _ : Fin 3 => G)
    (hi : Function.Injective a) :
    (complementOfBag G a).card = G.card - 3 := by
  rw [complementOfBag, Finset.card_sdiff_of_subset (support_subset_of_mem_pi ha),
    card_support_three_of_injective hi]

theorem card_complementOfBag_twoSupportThree
    (G : Finset α) {a : Fin 3 → α}
    (ha : a ∈ Fintype.piFinset fun _ : Fin 3 => G)
    (hc : ¬(a 0 = a 1 ∧ a 1 = a 2))
    (hi : ¬Function.Injective a) :
    (complementOfBag G a).card = G.card - 2 := by
  rw [complementOfBag, Finset.card_sdiff_of_subset (support_subset_of_mem_pi ha),
    card_support_two_of_neither hc hi]

/-- Exact cardinality-only formula for the unrestricted depth-three population. -/
theorem allPairsDepthFiber_three_polynomial (G : Finset α) :
    allPairsDepthFiber G 3 3 =
      G.card * (G.card - 1) ^ 3 +
      (G.card ^ 3 - G.card - G.card.descFactorial 3) * (G.card - 2) ^ 3 +
      G.card.descFactorial 3 * (G.card - 3) ^ 3 := by
  classical
  rw [allPairsDepthFiber_full_eq_sum_complements]
  let S := Fintype.piFinset (fun _ : Fin 3 => G)
  let C : (Fin 3 → α) → Prop := fun a => a 0 = a 1 ∧ a 1 = a 2
  let I : (Fin 3 → α) → Prop := Function.Injective
  have hpoint (a : Fin 3 → α) (ha : a ∈ S) :
      (complementOfBag G a).card ^ 3 =
        if C a then (G.card - 1) ^ 3
        else if I a then (G.card - 3) ^ 3 else (G.card - 2) ^ 3 := by
    by_cases hc : C a
    · simp only [hc, if_true]
      rw [card_complementOfBag_constantThree G (by simpa [S] using ha) hc]
    · simp only [hc, if_false]
      by_cases hi : I a
      · simp only [hi, if_true]
        rw [card_complementOfBag_injectiveThree G (by simpa [S] using ha) hi]
      · simp only [hi, if_false]
        rw [card_complementOfBag_twoSupportThree G (by simpa [S] using ha) hc hi]
  calc
    (∑ a ∈ Fintype.piFinset (fun _ : Fin 3 => G), (complementOfBag G a).card ^ 3) =
        ∑ a ∈ S, if C a then (G.card - 1) ^ 3
          else if I a then (G.card - 3) ^ 3 else (G.card - 2) ^ 3 := by
            exact Finset.sum_congr rfl hpoint
    _ = (constantThreeWords G).card * (G.card - 1) ^ 3 +
        (injectiveThreeWords G).card * (G.card - 3) ^ 3 +
        (twoSupportThreeWords G).card * (G.card - 2) ^ 3 := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const, Nat.nsmul_eq_mul]
      have hC : S.filter C = constantThreeWords G := by
        ext a
        simp [S, C, constantThreeWords]
      have hI : (S.filter fun a => ¬C a).filter I = injectiveThreeWords G := by
        rw [injectiveThreeWords]
        ext a
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨ha, _⟩, hi⟩
          exact ⟨ha, hi⟩
        · rintro ⟨ha, hi⟩
          exact ⟨⟨ha, injective_not_constant hi⟩, hi⟩
      have hM : (S.filter fun a => ¬C a).filter (fun a => ¬I a) =
          twoSupportThreeWords G := by
        ext a
        simp [S, C, I, twoSupportThreeWords, and_assoc]
      rw [Finset.sum_ite, hC, hI, hM]
      simp only [Finset.sum_const, Nat.nsmul_eq_mul]
      ac_rfl
    _ = _ := by
      rw [card_constantThreeWords, card_injectiveThreeWords, card_twoSupportThreeWords]
      ac_rfl

theorem three_word_two_support_count_simplify (n : ℕ) :
    n ^ 3 - n - n.descFactorial 3 = 3 * n * (n - 1) := by
  by_cases h : n < 3
  · interval_cases n <;> norm_num [Nat.descFactorial]
  · have hn : 3 ≤ n := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h1 : 3 + m - 1 = m + 2 := by omega
    have h2 : 3 + m - 2 = m + 1 := by omega
    have hid :
        (3 + m) ^ 3 = (3 + m) + (3 + m).descFactorial 3 +
          3 * (3 + m) * (3 + m - 1) := by
      simp [Nat.descFactorial, h1, h2]
      ring
    omega

theorem descFactorial_three (n : ℕ) :
    n.descFactorial 3 = n * (n - 1) * (n - 2) := by
  simp [Nat.descFactorial]
  ac_rfl

/-- Falling-factorial form of the exact unrestricted depth-three population. -/
theorem allPairsDepthFiber_three_fallingFactorial (G : Finset α) :
    allPairsDepthFiber G 3 3 =
      G.card * (G.card - 1) ^ 3 +
      3 * G.card * (G.card - 1) * (G.card - 2) ^ 3 +
      G.card * (G.card - 1) * (G.card - 2) * (G.card - 3) ^ 3 := by
  rw [allPairsDepthFiber_three_polynomial,
    three_word_two_support_count_simplify, descFactorial_three]

#print axioms cancelDepth_eq_length_iff_disjoint
#print axioms mem_pi_complementOfBag_iff_disjoint
#print axioms allPairsDepthFiber_full_eq_sum_complements
#print axioms depthFiber_full_eq_sum_disjointEqualSumRightFiber
#print axioms actualDepthAnomaly_full_eq_restricted_discrepancy
#print axioms card_constantThreeWords
#print axioms card_injectiveThreeWords
#print axioms card_twoSupportThreeWords
#print axioms allPairsDepthFiber_three_polynomial
#print axioms allPairsDepthFiber_three_fallingFactorial

end ArkLib.ProximityGap.Frontier.G114DepthThreePopulationNormalForm
