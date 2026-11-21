/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfListSplitDifferences
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-! # Disjoint families of completely split differences in a near-Johnson list

The integer pair-incidence bound applies to every subfamily. A lower threshold
than the actual list budget thus forces many mutually disjoint cliques within
one list around the same received word.
-/

set_option autoImplicit false
namespace ProximityGap.RobustSplitListCliques
open Finset Code Polynomial SimpleGraph SaturatedListCliques
open scoped ENNReal

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Integer incidence and Turán bounds force a clique even when its edges are
one or more agreements short of the maximum intersection. -/
theorem forced_clique_above {M t b c r a : ℕ} (S : Fin M → Finset I)
    (ht : ∀ i, t ≤ (S i).card) (hp : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ b + c)
    (hnum : M * ((M - 1) * b) + c * (2 * turanNumber M r) + a * (a + 1) * Fintype.card I <
      2 * a * (M * t)) : ¬ (fullGraph S (b + 1)).CliqueFree (r + 1) := by
  classical
  intro h
  have he : (fullGraph S (b + 1)).edgeFinset.card ≤ turanNumber M r := by
    simpa only [Fintype.card_fin] using h.card_edgeFinset_le
  have hn := forced_edges_above S ht hp a
  exact hnum.not_ge (hn.trans (by gcongr))

omit [Fintype I] in
private theorem subfamily_clique {M q t s b r : ℕ} (S : Fin M → Finset I)
    (ht : ∀ i, (S i).card = t) (hp : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ s)
    (force : ∀ R : Fin q → Finset I, (∀ i, t ≤ (R i).card) →
      (∀ i j, i ≠ j → (R i ∩ R j).card ≤ s) → ¬ (fullGraph R b).CliqueFree r)
    (A : Finset (Fin M)) (hq : q ≤ A.card) :
    ∃ K ⊆ A, (fullGraph S b).IsNClique r K := by
  classical
  obtain ⟨U, hUA, hU⟩ := exists_subset_card_eq hq
  let e : Fin q ≃ U := (Fintype.equivFinOfCardEq (by simpa using hU)).symm
  let f (i : Fin q) : Fin M := e i
  have hi : Function.Injective f := Subtype.val_injective.comp e.injective
  have hf := force (S ∘ f) (fun _ => (ht _).ge) (fun i j h => hp _ _ (hi.ne h))
  obtain ⟨K, hK⟩ := not_forall_not.mp hf
  refine ⟨K.image f, ?_, ?_⟩
  · rintro _ hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact hUA (e i).property
  · refine ⟨?_, (card_image_of_injective _ hi).trans hK.card_eq⟩
    rintro _ hx _ hy hne
    obtain ⟨i, hiK, rfl⟩ := mem_image.mp hx
    obtain ⟨j, hjK, rfl⟩ := mem_image.mp hy
    exact ⟨hne, (hK.isClique hiK hjK (fun h => hne (congrArg f h))).2⟩

/-- Greedy packing of cliques whose existence is guaranteed in every subfamily
of size at least `q`. -/
theorem pack {α : Type*} (G : SimpleGraph α) {r q : ℕ} (hr : 0 < r)
    (force : ∀ A : Finset α, q ≤ A.card → ∃ K ⊆ A, G.IsNClique r K)
    (p : ℕ) (A : Finset α) (ha : q + p * r ≤ A.card + r) (hq : q ≤ A.card ∨ p = 0) :
    ∃ C : Finset (Finset α), C.card = p ∧
      (∀ K ∈ C, K ⊆ A ∧ G.IsNClique r K) ∧ (C : Set (Finset α)).PairwiseDisjoint id := by
  classical
  induction p generalizing A with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ p ih =>
    obtain ⟨K, hKA, hK⟩ := force A (hq.resolve_right (by omega))
    have hcard : (A \ K).card = A.card - r := by rw [card_sdiff_of_subset hKA, hK.card_eq]
    have hKr : r ≤ A.card := hK.card_eq ▸ card_le_card hKA
    rw [Nat.succ_mul] at ha
    obtain ⟨C, hc, hh, hd⟩ := ih (A \ K) (by rw [hcard]; omega) (by
      rw [hcard]
      by_cases hp : p = 0
      · exact Or.inr hp
      · have : r ≤ p * r := by simpa using Nat.mul_le_mul_right r (show 1 ≤ p by omega)
        exact Or.inl (by omega))
    have dis (L) (hL : L ∈ C) : Disjoint K L :=
      disjoint_sdiff_self_right.mono_right (hh L hL).1
    have hnot : K ∉ C := by
      intro hm
      have := (disjoint_self.mp (dis K hm))
      simp_all
    refine ⟨insert K C, by rw [card_insert_of_notMem hnot, hc], ?_, ?_⟩
    · intro L hL
      rcases mem_insert.mp hL with rfl | hL
      · exact ⟨hKA, hK⟩
      · exact ⟨(hh L hL).1.trans sdiff_subset, (hh L hL).2⟩
    · rw [coe_insert, Set.pairwiseDisjoint_insert]
      exact ⟨hd, fun L hL _ => dis L hL⟩


variable {F : Type} [Field F]

/-- The same received word supports all the distinct messages in all the groups.
For each pair within a group the indicated number of chosen agreements are
common, and the polynomial difference splits over the ground field. -/
def SplitPacking (D : I ↪ F) (M k t b p r : ℕ) : Prop :=
  ∃ (y : I → F) (P : Fin M → F[X]) (S : Fin M → Finset I)
    (C : Finset (Finset (Fin M))), Function.Injective P ∧
    (∀ i, (P i).natDegree < k) ∧ (∀ i, (S i).card = t) ∧
    (∀ i x, x ∈ S i → (P i).eval (D x) = y x) ∧ C.card = p ∧
    (C : Set (Finset (Fin M))).PairwiseDisjoint id ∧
    ∀ K ∈ C, K.card = r ∧ ∀ i ∈ K, ∀ j ∈ K, i ≠ j →
      b ≤ (S i ∩ S j).card ∧ (P i - P j).Splits

/-- A hereditary numerical clique threshold below the list budget forces disjoint
sets of messages whose differences split over the ground field. -/
theorem packing_of_list (D : I ↪ F) {B k t q p r a b c : ℕ} (hk : 0 < k)
    (ht : t ≤ Fintype.card I) (hn : 0 < Fintype.card I) (hq : q ≤ B + 1)
    (hp : q + p * (r + 1) ≤ B + 1 + (r + 1)) (hbc : k - 1 ≤ b + c) (hs : k ≤ b + 3)
    (hnum : q * ((q - 1) * b) + c * (2 * turanNumber q r) + a * (a + 1) * Fintype.card I <
      2 * a * (q * t))
    (hlist : (B : ℕ∞) < Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I - t : ℕ) : ℝ) / Fintype.card I)) :
    SplitPacking D (B + 1) k t (b + 1) p (r + 1) := by
  classical
  obtain ⟨y, P, S, hinj, hdeg, hsize, hag, -⟩ :=
    from_list_at_overlap D (s := 0) (r := 0) hk ht hn (fun _ _ _ => not_cliqueFree_zero) hlist
  have hroot (i j : Fin (B + 1)) (x : I) (hx : x ∈ S i ∩ S j) :
      (P i - P j).eval (D x) = 0 := by
    obtain ⟨hi, hj⟩ := mem_inter.mp hx
    rw [eval_sub, hag i x hi, hag j x hj, sub_self]
  have hd (i j) : (P i - P j).natDegree ≤ k - 1 := by
    have hh := natDegree_sub_le (P i) (P j)
    have := hdeg i
    have := hdeg j
    omega
  have pair (i j) (hij : i ≠ j) : (S i ∩ S j).card ≤ k - 1 := by
    have hdiv := Polynomial.prod_X_sub_C_dvd (S i ∩ S j) D D.injective.injOn _ (hroot i j)
    have hle := natDegree_le_of_dvd hdiv (sub_ne_zero.mpr (hinj.ne hij))
    rw [show (∏ x ∈ S i ∩ S j, (X - Polynomial.C (D x))) = Lagrange.nodal (S i ∩ S j) D from rfl,
      Lagrange.natDegree_nodal] at hle
    exact hle.trans (hd i j)
  have forceR (R : Fin q → Finset I) (hw : ∀ i, t ≤ (R i).card)
      (hpair : ∀ i j, i ≠ j → (R i ∩ R j).card ≤ k - 1) :
      ¬ (fullGraph R (b + 1)).CliqueFree (r + 1) :=
    forced_clique_above R hw (fun i j he => (hpair i j he).trans hbc) hnum
  obtain ⟨C, hc, hh, hdis⟩ := pack (fullGraph S (b + 1)) (by omega : 0 < r + 1)
    (subfamily_clique S hsize pair forceR) p univ (by simpa using hp) (Or.inl (by simpa using hq))
  refine ⟨y, P, S, C, hinj, hdeg, hsize, hag, hc, hdis, ?_⟩
  intro K hK
  have hcl := (hh K hK).2
  refine ⟨hcl.card_eq, ?_⟩
  intro i hi j hj he
  have hb := (hcl.isClique hi hj he).2
  refine ⟨hb, HalfListSplitDifferences.splits_of_many_roots D _ (sub_ne_zero.mpr (hinj.ne he))
    (by have := hd i j; omega) (hroot i j)⟩

/-- At the first half-rate grid step outside strict Johnson, an oversized first-prime
budget gives at least 55,363,904 disjoint four-cliques of split differences. -/
theorem half (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hlist : (1073741824 : ℕ∞) < Lambda (ReedSolomon.code D 536870912 : Set (I → F))
      (314491700 / 1073741824)) :
    SplitPacking D 1073741825 536870912 759250124 536870910 55363904 4 := by
  apply packing_of_list D (q := 852286211) (a := 602657358) (c := 2)
    (by decide) (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)
  · rw [hn, turanNumber_eq, Nat.choose_two_right]
    decide
  · simpa only [hn, Nat.reduceSub, Nat.cast_ofNat] using hlist

/-- At the first rate-one-eighth grid step outside strict Johnson, an oversized
first-prime budget gives 25,809,976 disjoint seven-cliques of split differences. -/
theorem eighth (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hlist : (1073741824 : ℕ∞) < Lambda (ReedSolomon.code D 134217728 : Set (I → F))
      (694116763 / 1073741824)) :
    SplitPacking D 1073741825 134217728 379625061 134217726 25809976 7 := by
  apply packing_of_list D (q := 893071997) (a := 315748631) (c := 2)
    (by decide) (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)
  · rw [hn, turanNumber_eq, Nat.choose_two_right]
    decide
  · simpa only [hn, Nat.reduceSub, Nat.cast_ofNat] using hlist

/-- At the next open eighth-rate step for the second prime, overflow forces
366,766,857 disjoint triangles of split differences. -/
theorem second_eighth (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hlist : (2147483648 : ℕ∞) < Lambda (ReedSolomon.code D 134217728 : Set (I → F))
      (694116764 / 1073741824)) :
    SplitPacking D 2147483649 134217728 379625060 134217726 366766857 3 := by
  apply packing_of_list D (q := 1047183081) (a := 370235126) (c := 2)
    (by decide) (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)
  · rw [hn, turanNumber_eq, Nat.choose_two_right]
    decide
  · simpa only [hn, Nat.reduceSub, Nat.cast_ofNat] using hlist

omit [DecidableEq I] in
private theorem scalar_failure [Nonempty I] [Finite F] {κ : Type} [Finite κ] [Nonempty κ]
    (D : I ↪ F) (k B : ℕ) (δ : ℝ) (hB : B < Nat.card F) (hN : B * Fintype.card I ≤ Nat.card F)
    (h : (B : ℕ∞) < Lambda (interleavedCodeSet (κ := κ) (ReedSolomon.code D k : Set (I → F))) δ) :
    (B : ℕ∞) < Lambda (ReedSolomon.code D k : Set (I → F)) δ := by
  classical
  let := Fintype.ofFinite F
  let := Fintype.ofFinite κ
  exact lt_of_not_ge fun hs => h.not_ge
    ((InterleavedListProjection.support_list_budget_iff (ReedSolomon.code D k) δ B hB hN).mpr hs)

open ArkLib.ProximityGap

local instance : Fact (Nat.Prime PrizeShapePrimeP30.P) := ⟨PrizeShapePrimeP30.prime_P⟩
local instance : Fact (Nat.Prime PrizeShapePrimeP30Second.P) := ⟨PrizeShapePrimeP30Second.prime_P⟩

/-- At every positive interleaving width the first named prime's budget at eighth
rate forces the same 25,809,976 disjoint scalar seven-cliques. -/
theorem first_prime_eighth (D : Fin 1073741824 ↪ ZMod PrizeShapePrimeP30.P)
    (κ : Type) [Finite κ] [Nonempty κ] (hlist : ((PrizeShapePrimeP30.P / 2 ^ 128 : ℕ) : ℕ∞) <
      Lambda (interleavedCodeSet (κ := κ)
        (ReedSolomon.code D 134217728 : Set (Fin 1073741824 → ZMod PrizeShapePrimeP30.P)))
        (694116763 / 1073741824)) :
    SplitPacking D 1073741825 134217728 379625061 134217726 25809976 7 := by
  apply eighth D (by simp)
  apply scalar_failure (κ := κ) D
  · rw [Nat.card_eq_fintype_card, ZMod.card]
    decide
  · rw [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]
    decide
  · exact hlist

/-- At the first agreement count following the second prime's proved eighth-rate safety,
every over-budget interleaving forces the 366,766,857 scalar triangles. -/
theorem second_prime_eighth (D : Fin 1073741824 ↪ ZMod PrizeShapePrimeP30Second.P)
    (κ : Type) [Finite κ] [Nonempty κ] (hlist : ((PrizeShapePrimeP30Second.P / 2 ^ 128 : ℕ) : ℕ∞) <
      Lambda (interleavedCodeSet (κ := κ)
        (ReedSolomon.code D 134217728 : Set (Fin 1073741824 → ZMod PrizeShapePrimeP30Second.P)))
        (694116764 / 1073741824)) :
    SplitPacking D 2147483649 134217728 379625060 134217726 366766857 3 := by
  apply second_eighth D (by simp)
  apply scalar_failure (κ := κ) D
  · rw [Nat.card_eq_fintype_card, ZMod.card]
    decide
  · rw [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]
    decide
  · exact hlist

end ProximityGap.RobustSplitListCliques

#print axioms ProximityGap.RobustSplitListCliques.packing_of_list
#print axioms ProximityGap.RobustSplitListCliques.half
#print axioms ProximityGap.RobustSplitListCliques.eighth
#print axioms ProximityGap.RobustSplitListCliques.first_prime_eighth
#print axioms ProximityGap.RobustSplitListCliques.second_prime_eighth
