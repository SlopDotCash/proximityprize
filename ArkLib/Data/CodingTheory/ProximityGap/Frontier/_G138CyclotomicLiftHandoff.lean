/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G137MannPairingCensusConsumer
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal

/-!
# G138: one cyclotomic-lift accident hypothesis supplies both G137 Mann properties

G137 reduces the fully-disjoint production census to two Mann properties at length 110.  This file
turns them into one concrete arithmetic residual: every vanishing finite-field multiset of at most
220 subgroup elements must lift to a genuinely vanishing multiset of characteristic-zero
`2^k`-th roots.  The already-proved Lam--Leung multiset theorem then forces antipodal balance.

Thus the remaining certified-prime statement is literally the absence of reduction accidents of
weight at most 220.

Issue #466.  The accident exclusion itself remains a named arithmetic hypothesis.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G138CyclotomicLiftHandoff

open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G137MannPairingCensusConsumer
open LamLeungMultisetAntipodal

variable {F L : Type*} [Field F] [DecidableEq F]
  [Field L] [CharZero L] [DecidableEq L]

/-- Data identifying the finite subgroup values with characteristic-zero `2^k`-th roots. -/
structure CyclotomicLiftData (G : Finset F) (k : ℕ) where
  lift : F → L
  injective : Function.Injective lift
  map_neg : ∀ x, lift (-x) = -lift x
  root : ∀ x ∈ G, (lift x) ^ (2 ^ k) = 1

/-- No modular accident of weight at most `limit`: every finite-field vanishing multiset supported
on `G` remains vanishing after the cyclotomic lift. -/
def NoShortReductionAccidents
    (G : Finset F) {k : ℕ} (D : CyclotomicLiftData (L := L) G k) (limit : ℕ) : Prop :=
  ∀ M : Multiset F,
    M.card ≤ limit →
    (∀ x ∈ M, x ∈ G) →
    M.sum = 0 →
    (M.map D.lift).sum = 0

omit [CharZero L] in private theorem count_map_lift
    {G : Finset F} {k : ℕ} (D : CyclotomicLiftData (L := L) G k)
    (M : Multiset F) (x : F) :
    (M.map D.lift).count (D.lift x) = M.count x :=
  Multiset.count_map_eq_count' D.lift M D.injective x

private theorem count_map_neg (M : Multiset F) (x : F) :
    (M.map fun y => -y).count x = M.count (-x) := by
  simpa using
    (Multiset.count_map_eq_count' (fun y : F => -y) M neg_injective (-x))

/-- A genuinely vanishing cyclotomic lift reflects Lam--Leung antipodal balance back to the
finite-field multiset. -/
theorem negBalanced_of_cyclotomicLift_sum_zero
    {G : Finset F} {k : ℕ} (D : CyclotomicLiftData (L := L) G k)
    {M : Multiset F} (hM : ∀ x ∈ M, x ∈ G)
    (hlift : (M.map D.lift).sum = 0) : NegBalanced M := by
  have hroots : ∀ z ∈ M.map D.lift, z ^ (2 ^ k) = 1 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hz
    exact D.root x (hM x hx)
  have hbal := count_antipodal_of_sum_eq_zero hroots hlift
  ext x
  rw [count_map_neg]
  have hc := hbal (D.lift x)
  rw [← D.map_neg x] at hc
  rw [count_map_lift D M x, count_map_lift D M (-x)] at hc
  exact hc.symm

/-- One no-accident hypothesis implies the one-word Mann property at every shorter length. -/
theorem zeroSumMannProperty_of_noShortReductionAccidents
    (G : Finset F) {k limit m : ℕ}
    (D : CyclotomicLiftData (L := L) G k)
    (hacc : NoShortReductionAccidents G D limit) (hm : m ≤ limit) :
    ZeroSumMannProperty G m := by
  intro c hc hsum
  apply negBalanced_of_cyclotomicLift_sum_zero D
  · intro x hx
    obtain ⟨i, hi⟩ : ∃ i, c i = x := by simpa [valueBag] using hx
    rw [← hi]
    exact Fintype.mem_piFinset.mp hc i
  · apply hacc (valueBag c)
    · simpa [valueBag] using hm
    · intro x hx
      obtain ⟨i, hi⟩ : ∃ i, c i = x := by simpa [valueBag] using hx
      rw [← hi]
      exact Fintype.mem_piFinset.mp hc i
    · simpa [valueBag, List.sum_ofFn] using hsum

/-- The same no-accident hypothesis implies the signed two-endpoint Mann property. -/
theorem signedMannProperty_of_noShortReductionAccidents
    (G : Finset F) {k limit r : ℕ}
    (D : CyclotomicLiftData (L := L) G k)
    (hacc : NoShortReductionAccidents G D limit)
    (hneg : ∀ x ∈ G, -x ∈ G) (hr : 2 * r ≤ limit) :
    SignedMannProperty G r := by
  intro a b ha hb hsum
  let M := valueBag a + (valueBag b).map fun x => -x
  apply negBalanced_of_cyclotomicLift_sum_zero D
  · intro x hx
    simp only [Multiset.mem_add, Multiset.mem_map] at hx
    rcases hx with hxa | ⟨y, hy, rfl⟩
    · obtain ⟨i, hi⟩ : ∃ i, a i = x := by simpa [valueBag] using hxa
      rw [← hi]
      exact Fintype.mem_piFinset.mp ha i
    · obtain ⟨i, hi⟩ : ∃ i, b i = y := by simpa [valueBag] using hy
      exact hneg y (by rw [← hi]; exact Fintype.mem_piFinset.mp hb i)
  · apply hacc M
    · simp [M, valueBag]
      simpa [two_mul] using hr
    · intro x hx
      simp only [M, Multiset.mem_add, Multiset.mem_map] at hx
      rcases hx with hxa | ⟨y, hy, rfl⟩
      · obtain ⟨i, hi⟩ : ∃ i, a i = x := by simpa [valueBag] using hxa
        rw [← hi]
        exact Fintype.mem_piFinset.mp ha i
      · obtain ⟨i, hi⟩ : ∃ i, b i = y := by simpa [valueBag] using hy
        exact hneg y (by rw [← hi]; exact Fintype.mem_piFinset.mp hb i)
    · simp [M, valueBag, List.sum_ofFn, hsum]

/-- **G138 capstone.** One no-reduction-accident statement through weight 220 supplies both Mann
inputs to G137 and discharges the production fully-disjoint census. -/
theorem production_fullDepth_census_of_no_accidents_220
    [Fintype F] (G : Finset F)
    (D : CyclotomicLiftData (L := L) G 30)
    (hacc : NoShortReductionAccidents G D 220)
    (hneg : ∀ x ∈ G, -x ∈ G)
    (hself : ∀ x ∈ G, x ≠ -x)
    (hcard : G.card = 2 ^ 30)
    (hq : Fintype.card F ≤ 2 ^ 160)
    (h2 : (2 : F) ≠ 0) :
    Fintype.card F * depthFiber G 110 110 ≤ (2 ^ 30) ^ 220 := by
  apply production_fullDepth_census_le_dcMass G hcard hq h2
  · exact signedMannProperty_of_noShortReductionAccidents G D hacc hneg (by norm_num)
  · exact zeroSumMannProperty_of_noShortReductionAccidents G D hacc (by norm_num)
  · exact hself

#print axioms negBalanced_of_cyclotomicLift_sum_zero
#print axioms zeroSumMannProperty_of_noShortReductionAccidents
#print axioms signedMannProperty_of_noShortReductionAccidents
#print axioms production_fullDepth_census_of_no_accidents_220

end ArkLib.ProximityGap.Frontier.G138CyclotomicLiftHandoff
