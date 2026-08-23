/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G114DepthThreePopulationNormalForm
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingLifting

/-!
# G137: Mann-pairing consumer for the fully-disjoint census

For roots of unity of 2-power order, the characteristic-zero Mann/Lam--Leung classification says
that every short vanishing sum decomposes into opposite pairs.  Reduction modulo a certified prime
can fail only through a cyclotomic divisibility accident.  This file isolates the exact consumer
needed by the G132 census tower.

If the signed multiset formed from an equal-sum endpoint pair is negation-balanced, and the original
endpoint supports are disjoint, then no opposite pair can cross between endpoints: a crossing would
give the same original value on both sides.  Hence each endpoint is itself negation-balanced and,
away from characteristic two, has sum zero.

Issue #466.  The cyclotomic classification/accident exclusion remains an explicit hypothesis here.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G137MannPairingCensusConsumer

open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G114DepthThreePopulationNormalForm
open ArkLib.ProximityGap.NegationClosedWalk

variable {F : Type*} [Field F] [DecidableEq F]

/-- A multiset is a union of opposite pairs at the level of multiplicities. -/
def NegBalanced (M : Multiset F) : Prop :=
  M.map (fun x => -x) = M

private theorem count_map_neg (M : Multiset F) (x : F) :
    (M.map fun y => -y).count x = M.count (-x) := by
  simpa using
    (Multiset.count_map_eq_count' (fun y : F => -y) M neg_injective (-x))

omit [DecidableEq F] in private theorem sum_map_neg (M : Multiset F) :
    (M.map fun x => -x).sum = -M.sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih => simp [ih, add_comm]

-- Disjoint unsigned endpoints force a negation-balanced signed union to split into two
-- negation-balanced endpoints.
omit [DecidableEq F] in theorem negBalanced_endpoints_of_disjoint
    {A B : Multiset F} (hdis : Disjoint A B)
    (hbal : NegBalanced (A + B.map fun x => -x)) :
    NegBalanced A ∧ NegBalanced B := by
  classical
  have hinter : A ∩ B = 0 := Multiset.inter_eq_zero_iff_disjoint.mpr hdis
  have hleft : NegBalanced A := by
    ext x
    rw [count_map_neg]
    have hd0 := congrArg (Multiset.count x) hinter
    have hdn := congrArg (Multiset.count (-x)) hinter
    simp only [Multiset.count_inter, Multiset.count_zero] at hd0 hdn
    have hb := congrArg (Multiset.count x) hbal
    rw [count_map_neg, Multiset.count_add, Multiset.count_add] at hb
    rw [count_map_neg, count_map_neg] at hb
    simp only [neg_neg] at hb
    omega
  have hright : NegBalanced B := by
    ext x
    rw [count_map_neg]
    have hd0 := congrArg (Multiset.count x) hinter
    have hdn := congrArg (Multiset.count (-x)) hinter
    simp only [Multiset.count_inter, Multiset.count_zero] at hd0 hdn
    have hb := congrArg (Multiset.count x) hbal
    rw [count_map_neg, Multiset.count_add, Multiset.count_add] at hb
    rw [count_map_neg, count_map_neg] at hb
    simp only [neg_neg] at hb
    omega
  exact ⟨hleft, hright⟩

-- In odd characteristic, a negation-balanced multiset has sum zero.
omit [DecidableEq F] in theorem sum_eq_zero_of_negBalanced
    (h2 : (2 : F) ≠ 0) {A : Multiset F} (hbal : NegBalanced A) : A.sum = 0 := by
  have hsum := congrArg Multiset.sum hbal
  have hneg : -A.sum = A.sum := by
    rw [sum_map_neg] at hsum
    exact hsum
  have hadd : A.sum + A.sum = 0 := by
    calc
      A.sum + A.sum = A.sum + (-A.sum) := by rw [hneg]
      _ = 0 := add_neg_cancel _
  apply (mul_eq_zero.mp ?_).resolve_left h2
  calc
    (2 : F) * A.sum = A.sum + A.sum := two_mul A.sum
    _ = 0 := hadd

/-- The exact cyclotomic/Mann input: every signed equal-sum relation of length `2r` supported on
`G` is negation-balanced.  Failures after reduction modulo a prime are precisely the accidents
left to the arithmetic lane. -/
def SignedMannProperty (G : Finset F) (r : ℕ) : Prop :=
  ∀ a b : Fin r → F,
    a ∈ Fintype.piFinset (fun _ : Fin r => G) →
    b ∈ Fintype.piFinset (fun _ : Fin r => G) →
    (∑ i, a i) = ∑ i, b i →
    NegBalanced (valueBag a + (valueBag b).map fun x => -x)

-- Under the Mann property, support-disjoint equal-sum endpoints must each sum to zero.
omit [DecidableEq F] in theorem endpoint_sums_zero_of_signedMann
    (G : Finset F) {r : ℕ} (h2 : (2 : F) ≠ 0)
    (hMann : SignedMannProperty G r)
    {a b : Fin r → F}
    (ha : a ∈ Fintype.piFinset fun _ : Fin r => G)
    (hb : b ∈ Fintype.piFinset fun _ : Fin r => G)
    (hsum : (∑ i, a i) = ∑ i, b i)
    (hdis : Disjoint (valueBag a) (valueBag b)) :
    (∑ i, a i) = 0 ∧ (∑ i, b i) = 0 := by
  classical
  obtain ⟨hleft, hright⟩ :=
    negBalanced_endpoints_of_disjoint hdis (hMann a b ha hb hsum)
  have ha0 := sum_eq_zero_of_negBalanced h2 hleft
  have hb0 := sum_eq_zero_of_negBalanced h2 hright
  simpa [valueBag, List.sum_ofFn] using And.intro ha0 hb0

/-- The `r`-word zero-sum carrier inside `G`. -/
def zeroSumWords (G : Finset F) (r : ℕ) : Finset (Fin r → F) :=
  (Fintype.piFinset fun _ : Fin r => G).filter fun a => ∑ i, a i = 0

/-- **G137 census consumer.** The fully-disjoint equal-sum census injects into a pair of independent
zero-sum word carriers whenever the short signed Mann property holds. -/
theorem depthFiber_full_le_zeroSumWords_sq
    (G : Finset F) (r : ℕ) (h2 : (2 : F) ≠ 0)
    (hMann : SignedMannProperty G r) :
    depthFiber G r r ≤ (zeroSumWords G r).card ^ 2 := by
  classical
  unfold depthFiber
  calc
    ((energySet G r).filter fun x => cancelDepth x = r).card ≤
        (zeroSumWords G r ×ˢ zeroSumWords G r).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter] at hx
      have henergy := hx.1
      have hdepth := hx.2
      simp only [energySet, Finset.mem_filter, Finset.mem_product] at henergy
      have hdis := (cancelDepth_eq_length_iff_disjoint x.1 x.2).mp hdepth
      obtain ⟨hleft, hright⟩ := endpoint_sums_zero_of_signedMann G h2 hMann
        henergy.1.1 henergy.1.2 henergy.2 hdis
      simp [zeroSumWords, henergy.1, hleft, hright]
    _ = (zeroSumWords G r).card ^ 2 := by
      rw [Finset.card_product, pow_two]

/-- The one-word Mann property needed to turn zero-sum words into actual antipodal matchings. -/
def ZeroSumMannProperty (G : Finset F) (m : ℕ) : Prop :=
  ∀ c : Fin m → F,
    c ∈ Fintype.piFinset (fun _ : Fin m => G) →
    (∑ i, c i) = 0 → NegBalanced (valueBag c)

/-- A zero-sum Mann classification at even length gives the exact Wick pairing bound. -/
theorem zeroSumWords_card_le_doubleFactorial
    (G : Finset F) (k : ℕ)
    (hMann : ZeroSumMannProperty G (2 * k))
    (hself : ∀ x ∈ G, x ≠ -x) :
    (zeroSumWords G (2 * k)).card ≤
      Nat.doubleFactorial (2 * k - 1) * G.card ^ k := by
  have hpair :
      ∀ c ∈ Fintype.piFinset (fun _ : Fin (2 * k) => G),
        (∑ i, c i = 0) →
        ∃ σ : Equiv.Perm (Fin (2 * k)),
          IsPairing σ ∧ ∀ i, c (σ i) = -c i := by
    intro c hc hsum
    have hbalM := hMann c hc hsum
    have hcount : ∀ w : F,
        (Finset.univ.val.map c).count w = (Finset.univ.val.map c).count (-w) := by
      intro w
      have hb := congrArg (Multiset.count (-w)) hbalM
      rw [count_map_neg] at hb
      simpa [valueBag] using hb
    have hcself : ∀ i, c i ≠ -c i := fun i =>
      hself (c i) (Fintype.mem_piFinset.mp hc i)
    exact exists_isPairing_of_count_balanced c hcount hcself
  change zeroSumCount G (2 * k) ≤ _
  exact zeroSumCount_le_doubleFactorial G hpair

/-- **G137 capstone.** Once the characteristic-`p` accident exclusions supply the signed and
one-word Mann properties through length `4k`, the fully-disjoint census is at most the square of
the characteristic-zero Wick count. -/
theorem depthFiber_full_le_wick_sq_of_mann
    (G : Finset F) (k : ℕ) (h2 : (2 : F) ≠ 0)
    (hSigned : SignedMannProperty G (2 * k))
    (hZero : ZeroSumMannProperty G (2 * k))
    (hself : ∀ x ∈ G, x ≠ -x) :
    depthFiber G (2 * k) (2 * k) ≤
      (Nat.doubleFactorial (2 * k - 1) * G.card ^ k) ^ 2 := by
  calc
    depthFiber G (2 * k) (2 * k) ≤
        (zeroSumWords G (2 * k)).card ^ 2 :=
      depthFiber_full_le_zeroSumWords_sq G (2 * k) h2 hSigned
    _ ≤ (Nat.doubleFactorial (2 * k - 1) * G.card ^ k) ^ 2 := by
      exact Nat.pow_le_pow_left (zeroSumWords_card_le_doubleFactorial G k hZero hself) 2

/-- The production Wick-square census is tiny compared with the available DC mass. -/
theorem production_mann_wick_sq_fits_dcMass :
    2 ^ 160 *
        (Nat.doubleFactorial 109 * (2 ^ 30) ^ 55) ^ 2 ≤
      (2 ^ 30) ^ 220 := by
  norm_num [Nat.doubleFactorial]

/-- At the production parameters, the two Mann classifications immediately discharge the
fully-disjoint census share required by the tower. -/
theorem production_fullDepth_census_le_dcMass
    [Fintype F] (G : Finset F)
    (hcard : G.card = 2 ^ 30)
    (hq : Fintype.card F ≤ 2 ^ 160)
    (h2 : (2 : F) ≠ 0)
    (hSigned : SignedMannProperty G 110)
    (hZero : ZeroSumMannProperty G 110)
    (hself : ∀ x ∈ G, x ≠ -x) :
    Fintype.card F * depthFiber G 110 110 ≤ (2 ^ 30) ^ 220 := by
  have hdepth := depthFiber_full_le_wick_sq_of_mann G 55 h2 hSigned hZero hself
  norm_num at hdepth
  rw [hcard] at hdepth
  exact (Nat.mul_le_mul hq hdepth).trans production_mann_wick_sq_fits_dcMass

#print axioms negBalanced_endpoints_of_disjoint
#print axioms endpoint_sums_zero_of_signedMann
#print axioms depthFiber_full_le_zeroSumWords_sq
#print axioms zeroSumWords_card_le_doubleFactorial
#print axioms depthFiber_full_le_wick_sq_of_mann
#print axioms production_fullDepth_census_le_dcMass

end ArkLib.ProximityGap.Frontier.G137MannPairingCensusConsumer
