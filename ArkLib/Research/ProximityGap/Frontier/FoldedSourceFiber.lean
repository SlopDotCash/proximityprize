/-
Copyright (c) 2026 solidity-master. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: solidity-master
-/
import ArkLib.Research.ProximityGap.Frontier._BGKPrimitiveDepthSevenSparseCodeNoGo

/-!
# Exact source fibers of fourteen unit letters

A folded integer label with fourteen nonzero coefficients, all equal to `1` or `-1`, has
exactly `14!` ordered seven-tuple source pairs. Every such pair is injective on each side and
globally disjoint: fourteen occupied folded coordinates exhaust the fourteen source positions.
Thus this is the cardinality of the actual restricted source fiber, rather than the value of a
formal generating-function coefficient.

This fills the actual-cardinality gap recorded beside `allUnitFormalSourceFiberCoefficient_exact`
and `allUnitFormalOrderedFiberFactor_eq_factorial` in `_BGKPrimitiveFoldedAlphabet.lean`.
The proof uses the exact signed-profile enumeration from `_R322SignedWalkEndpointEnvelope.lean`
and pair-to-doubled-tuple bijection from `_R321ShadowAutocorrelationDoubling.lean`.
The new source-support argument shows that the primitive source restrictions impose no further
loss in this sector. At a field root satisfying
`g ^ m = -1`, the primitive collision fiber has `14!` members when the fixed label evaluates to
zero, and is empty otherwise. Summing these disjoint fibers gives the actual primitive tuple
census in this sector as `14!` times the number of vanishing fourteen-unit-letter labels.

These are ordered tuples. Applying the count to ordered pairs of unordered seven-subsets requires
dividing out `(7!)²`, giving `14! / (7!)² = 3432`; that quotient is a separate formalization step.
Transport to subsets of field elements additionally requires injectivity of the exponent
parametrization. No arithmetic bound on the number of labels evaluating to zero is supplied here;
the depth-seven cancellation target remains open.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.FoldedSourceFiber

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling
open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R379SparseOrbitSupportBound
open ArkLib.ProximityGap.Frontier.BGKPrimitiveDepthSevenSparseCodeNoGo

/-- Forget the sign of one signed exponent index. -/
def foldedIndex {m : ℕ} (x : Fin (2 * m)) : Fin m :=
  ((signedIndexEquiv m).symm x).1

/-- The folded coordinate at each of the fourteen source positions. -/
def pairFoldedIndex {m : ℕ} (a b : Fin 7 → Fin (2 * m)) : Fin 7 ⊕ Fin 7 → Fin m :=
  Sum.elim (fun i => foldedIndex (a i)) (fun i => foldedIndex (b i))

private theorem vecOf_eq_zero_of_foldedIndex_ne {m : ℕ}
    (x : Fin (2 * m)) (j : Fin m) (h : foldedIndex x ≠ j) :
    vecOf (2 * m) m x j = 0 := by
  obtain ⟨⟨k, e⟩, rfl⟩ := (signedIndexEquiv m).surjective x
  have hkj : k ≠ j := by simpa [foldedIndex] using h
  simp [vecOf_signedIndex, hkj]

/-- Every nonzero relation coordinate is occupied by at least one source position. -/
theorem vectorSupport_subset_pairFoldedIndex_image {m : ℕ}
    (a b : Fin 7 → Fin (2 * m)) :
    vectorSupport (depthSevenRelation m a b) ⊆ univ.image (pairFoldedIndex a b) := by
  intro j hj
  have hne : depthSevenRelation m a b j ≠ 0 := (mem_filter.mp hj).2
  by_contra hnot
  have ha : ∀ i, foldedIndex (a i) ≠ j := by
    intro i hi
    exact hnot (mem_image.mpr ⟨Sum.inl i, mem_univ _, hi⟩)
  have hb : ∀ i, foldedIndex (b i) ≠ j := by
    intro i hi
    exact hnot (mem_image.mpr ⟨Sum.inr i, mem_univ _, hi⟩)
  apply hne
  simp only [depthSevenRelation, tupleVec]
  have hA : ∑ i : Fin 7, vecOf (2 * m) m (a i) j = 0 :=
    sum_eq_zero fun i _ => vecOf_eq_zero_of_foldedIndex_ne (a i) j (ha i)
  have hB : ∑ i : Fin 7, vecOf (2 * m) m (b i) j = 0 :=
    sum_eq_zero fun i _ => vecOf_eq_zero_of_foldedIndex_ne (b i) j (hb i)
  rw [hA, hB, sub_self]

/-- Maximal folded support forces all fourteen source positions to use distinct coordinates. -/
theorem pairFoldedIndex_injective_of_support_card {m : ℕ}
    (a b : Fin 7 → Fin (2 * m))
    (hcard : (vectorSupport (depthSevenRelation m a b)).card = 14) :
    Function.Injective (pairFoldedIndex a b) := by
  have hlo := card_le_card (vectorSupport_subset_pairFoldedIndex_image a b)
  have hhi := card_image_le (s := (univ : Finset (Fin 7 ⊕ Fin 7)))
    (f := pairFoldedIndex a b)
  have heq : (univ.image (pairFoldedIndex a b)).card =
      (univ : Finset (Fin 7 ⊕ Fin 7)).card := by
    simp only [card_univ, Fintype.card_sum, Fintype.card_fin] at hhi ⊢
    omega
  have hinj := card_image_iff.mp heq
  intro i k hik
  exact hinj (mem_univ _) (mem_univ _) hik

/-- In the fourteen-coordinate sector, injectivity and disjointness are automatic. -/
theorem globallyDisjoint_of_support_card {m : ℕ} (a b : Fin 7 → Fin (2 * m))
    (hcard : (vectorSupport (depthSevenRelation m a b)).card = 14) :
    GloballyDisjointSevenPetals a b := by
  have hinj := pairFoldedIndex_injective_of_support_card a b hcard
  refine ⟨?_, ?_, ?_⟩
  · intro i k hik
    have h : (Sum.inl i : Fin 7 ⊕ Fin 7) = Sum.inl k := by
      apply hinj
      change foldedIndex (a i) = foldedIndex (a k)
      rw [hik]
    exact Sum.inl.inj h
  · intro i k hik
    have h : (Sum.inr i : Fin 7 ⊕ Fin 7) = Sum.inr k := by
      apply hinj
      change foldedIndex (b i) = foldedIndex (b k)
      rw [hik]
    exact Sum.inr.inj h
  · apply disjoint_left.mpr
    intro x hxa hxb
    obtain ⟨i, _, hi⟩ := mem_image.mp hxa
    obtain ⟨k, _, hk⟩ := mem_image.mp hxb
    have h : (Sum.inl i : Fin 7 ⊕ Fin 7) = Sum.inr k := by
      apply hinj
      change foldedIndex (a i) = foldedIndex (b k)
      rw [hi, hk]
    cases h

/-- Unit coefficients make the endpoint mass equal to its support cardinality. -/
theorem endpointL1_eq_support_card_of_unit_letters {m : ℕ} (d : Fin m → ℤ)
    (hunit : ∀ j, d j = -1 ∨ d j = 0 ∨ d j = 1) :
    endpointL1 d = (vectorSupport d).card := by
  have hterm : ∀ j, (d j).natAbs = if d j ≠ 0 then 1 else 0 := by
    intro j
    rcases hunit j with hj | hj | hj <;> simp [hj]
  unfold endpointL1 vectorSupport
  simp_rw [hterm]
  exact sum_boole (R := ℕ) (fun j : Fin m => d j ≠ 0) univ

private theorem cancellationProfile_eq_zero_of_length_eq_mass {m L : ℕ}
    (a b : Fin m → ℕ) (t : Fin L → Fin m × Fin 2)
    (hdisj : ∀ j, a j = 0 ∨ b j = 0)
    (hend : tupleVec (2 * m) m L (encodeSignedTuple t) =
      fun j => (a j : ℤ) - (b j : ℤ))
    (hmass : L = ∑ j : Fin m, (a j + b j)) :
    tupleCancellationProfile t = 0 := by
  have hprofile := tupleMultiset_eq_profile_of_endpoint a b t hdisj hend
  have hc := congrArg Multiset.card hprofile
  rw [card_tupleMultiset, card_multiplicityMultiset, sum_signedProfile,
    sum_two_mul_add_add] at hc
  have hsum : ∑ j : Fin m, tupleCancellationProfile t j = 0 := by omega
  funext j
  have hle := single_le_sum (s := (univ : Finset (Fin m)))
    (f := tupleCancellationProfile t) (fun _ _ => Nat.zero_le _) (mem_univ j)
  rw [hsum] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- With no cancellation and only unit letters, every endpoint fiber has `L!` tuples. -/
theorem NR_eq_factorial_of_unit_letters {m L : ℕ} (d : Fin m → ℤ)
    (hunit : ∀ j, d j = -1 ∨ d j = 0 ∨ d j = 1)
    (hcard : (vectorSupport d).card = L) :
    NR (2 * m) m L d = L.factorial := by
  classical
  let a : Fin m → ℕ := fun j => intPositivePart (d j)
  let b : Fin m → ℕ := fun j => intNegativePart (d j)
  have hdisj : ∀ j, a j = 0 ∨ b j = 0 := fun j =>
    intPositivePart_eq_zero_or_intNegativePart_eq_zero (d j)
  have hend : (fun j => (a j : ℤ) - (b j : ℤ)) = d := by
    funext j
    exact intPositivePart_cast_sub_intNegativePart_cast (d j)
  have hmass : L = ∑ j : Fin m, (a j + b j) := by
    calc
      L = (vectorSupport d).card := hcard.symm
      _ = endpointL1 d := (endpointL1_eq_support_card_of_unit_letters d hunit).symm
      _ = ∑ j : Fin m, (a j + b j) := by
        apply sum_congr rfl
        intro j _
        exact (intPositivePart_add_intNegativePart (d j)).symm
  have hset : canonicalEndpointTuples m L a b =
      (Fintype.piFinset (fun _ : Fin L => (univ : Finset (Fin m × Fin 2)))).filter
        (fun t => tupleMultiset t = multiplicityMultiset (signedProfile 0 a b)) := by
    ext t
    simp only [canonicalEndpointTuples, mem_filter]
    constructor
    · rintro ⟨ht, htend⟩
      refine ⟨ht, ?_⟩
      have hprof := tupleMultiset_eq_profile_of_endpoint a b t hdisj htend
      rw [cancellationProfile_eq_zero_of_length_eq_mass a b t hdisj htend hmass] at hprof
      exact hprof
    · rintro ⟨ht, hprof⟩
      exact ⟨ht, tupleVec_encodeSignedTuple_of_profile 0 a b t hprof⟩
  have hsum : ∑ x : Fin m × Fin 2, signedProfile 0 a b x = L := by
    rw [sum_signedProfile]
    simpa using hmass.symm
  have hprod : ∏ x : Fin m × Fin 2, (signedProfile 0 a b x).factorial = 1 := by
    rw [prod_factorial_signedProfile]
    apply prod_eq_one
    intro j _
    rcases hunit j with hj | hj | hj <;>
      simp [a, b, intPositivePart, intNegativePart, hj]
  have hmulti := Nat.multinomial_spec univ (signedProfile 0 a b)
  rw [hprod, one_mul, hsum] at hmulti
  rw [← hend, NR_eq_card_canonicalEndpointTuples, hset,
    tupleMultiset_fiber_card_eq_countPerms]
  · rw [countPerms_multiplicityMultiset]
    exact hmulti
  · rw [card_multiplicityMultiset]
    exact hsum

private instance {m : ℕ} (a b : Fin 7 → Fin (2 * m)) :
    Decidable (GloballyDisjointSevenPetals a b) := by
  unfold GloballyDisjointSevenPetals Function.Injective
  infer_instance

private instance {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m : ℕ) (a b : Fin 7 → Fin (2 * m)) :
    Decidable (PrimitiveDepthSevenCollision g m a b) := by
  unfold PrimitiveDepthSevenCollision NontrivialDepthSevenCollision
  infer_instance

/-- Actual globally disjoint ordered seven-tuple pairs with a prescribed folded relation. -/
def sourceFiber {m : ℕ} (d : Fin m → ℤ) :
    Finset ((Fin 7 → Fin (2 * m)) × (Fin 7 → Fin (2 * m))) :=
  univ.filter fun p => GloballyDisjointSevenPetals p.1 p.2 ∧
    depthSevenRelation m p.1 p.2 = d

/-- At maximal support the restricted source fiber equals the doubled signed-walk fiber. -/
theorem card_sourceFiber_eq_NR {m : ℕ} (d : Fin m → ℤ)
    (hcard : (vectorSupport d).card = 14) :
    (sourceFiber d).card = NR (2 * m) m 14 d := by
  classical
  rw [← tuplePairDifferenceCount_eq_NR m 7 d]
  unfold sourceFiber tuplePairDifferenceCount
  refine card_bij' (i := fun p _ => p.swap) (j := fun p _ => p.swap) ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_filter] at hp ⊢
    exact ⟨mem_univ _, hp.2.2⟩
  · intro p hp
    rw [mem_filter] at hp ⊢
    refine ⟨mem_univ _, ?_, hp.2⟩
    apply globallyDisjoint_of_support_card
    change (vectorSupport (fun j =>
      tupleVec (2 * m) m 7 p.2 j - tupleVec (2 * m) m 7 p.1 j)).card = 14
    rw [hp.2]
    exact hcard
  · intro p _
    exact Prod.swap_swap p
  · intro p _
    exact Prod.swap_swap p

/-- The actual source fiber over any fourteen-unit-letter label has exactly `14!` members. -/
theorem card_sourceFiber_of_fourteen_unit_letters {m : ℕ} (d : Fin m → ℤ)
    (hunit : ∀ j, d j = -1 ∨ d j = 0 ∨ d j = 1)
    (hcard : (vectorSupport d).card = 14) :
    (sourceFiber d).card = Nat.factorial 14 := by
  rw [card_sourceFiber_eq_NR d hcard]
  exact NR_eq_factorial_of_unit_letters d hunit hcard

/-- Members of an actual fixed-label source fiber that also collide in the field. -/
def primitiveSourceFiber {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m : ℕ} (g : F) (d : Fin m → ℤ) :
    Finset ((Fin 7 → Fin (2 * m)) × (Fin 7 → Fin (2 * m))) :=
  (sourceFiber d).filter fun p => PrimitiveDepthSevenCollision g m p.1 p.2

/-- The primitive collision fiber is exactly `14!` or zero according to the fixed label's
field evaluation. No assumption about production cancellation is used. -/
theorem card_primitiveSourceFiber_of_fourteen_unit_letters
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m : ℕ} (g : F) (hm : 0 < m) (hg : g ^ m = -1) (d : Fin m → ℤ)
    (hunit : ∀ j, d j = -1 ∨ d j = 0 ∨ d j = 1)
    (hcard : (vectorSupport d).card = 14) :
    (primitiveSourceFiber g d).card =
      if evalVec g m d = 0 then Nat.factorial 14 else 0 := by
  classical
  have hd : d ≠ 0 := by
    intro hzero
    simp [hzero, vectorSupport] at hcard
  by_cases heval : evalVec g m d = 0
  · have hset : primitiveSourceFiber g d = sourceFiber d := by
      ext p
      simp only [primitiveSourceFiber, mem_filter]
      constructor
      · exact And.left
      · intro hp
        refine ⟨hp, ?_⟩
        have hs := (mem_filter.mp hp).2
        rw [primitiveDepthSevenCollision_iff g m hm hg]
        exact ⟨hs.1, by rw [hs.2]; exact hd, by rw [hs.2]; exact heval⟩
    rw [hset, card_sourceFiber_of_fourteen_unit_letters d hunit hcard, ite_eq_left heval]
  · have hset : primitiveSourceFiber g d = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hs, hprim⟩ := mem_filter.mp hp
      have hlabel := (mem_filter.mp hs).2.2
      have hzero := ((primitiveDepthSevenCollision_iff g m hm hg p.1 p.2).mp hprim).2.2
      rw [hlabel] at hzero
      exact heval hzero
    rw [hset, card_empty, ite_eq_right heval]

/-- The finite label set for the fourteen-coordinate, unit-coefficient sector. -/
def unitLabels (m : ℕ) : Finset (Fin m → ℤ) :=
  (Fintype.piFinset (fun _ : Fin m => ({-1, 0, 1} : Finset ℤ))).filter
    fun d => (vectorSupport d).card = 14

theorem mem_unitLabels_iff {m : ℕ} (d : Fin m → ℤ) :
    d ∈ unitLabels m ↔
      (∀ j, d j = -1 ∨ d j = 0 ∨ d j = 1) ∧ (vectorSupport d).card = 14 := by
  simp [unitLabels, Fintype.mem_piFinset]

/-- Actual primitive ordered tuple collisions in the fourteen-unit-letter sector. -/
def primitiveUnitSourcePairs {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m : ℕ) :
    Finset ((Fin 7 → Fin (2 * m)) × (Fin 7 → Fin (2 * m))) :=
  univ.filter fun p => PrimitiveDepthSevenCollision g m p.1 p.2 ∧
    depthSevenRelation m p.1 p.2 ∈ unitLabels m

/-- The primitive tuple census in this sector is exactly the vanishing-label count times `14!`.
The remaining arithmetic task is to bound the number of vanishing labels. -/
theorem card_primitiveUnitSourcePairs
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m : ℕ) (hm : 0 < m) (hg : g ^ m = -1) :
    (primitiveUnitSourcePairs g m).card = Nat.factorial 14 *
      ((unitLabels m).filter fun d => evalVec g m d = 0).card := by
  classical
  have hmaps : (↑(primitiveUnitSourcePairs g m) :
      Set ((Fin 7 → Fin (2 * m)) × (Fin 7 → Fin (2 * m)))).MapsTo
      (fun p => depthSevenRelation m p.1 p.2) (↑(unitLabels m)) := by
    intro p hp
    exact (mem_filter.mp hp).2.2
  have hfiber (d : Fin m → ℤ) (hd : d ∈ unitLabels m) :
      (primitiveUnitSourcePairs g m).filter
        (fun p => depthSevenRelation m p.1 p.2 = d) = primitiveSourceFiber g d := by
    ext p
    simp only [primitiveUnitSourcePairs, primitiveSourceFiber, sourceFiber,
      mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hprim, _⟩, hlabel⟩
      exact ⟨⟨hprim.1, hlabel⟩, hprim⟩
    · rintro ⟨⟨_, hlabel⟩, hprim⟩
      refine ⟨⟨hprim, ?_⟩, hlabel⟩
      rw [hlabel]
      exact hd
  rw [card_eq_sum_card_fiberwise hmaps]
  calc
    ∑ d ∈ unitLabels m,
        ((primitiveUnitSourcePairs g m).filter
          (fun p => depthSevenRelation m p.1 p.2 = d)).card =
        ∑ d ∈ unitLabels m, if evalVec g m d = 0 then Nat.factorial 14 else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [hfiber d hd]
      obtain ⟨hunit, hcard⟩ := (mem_unitLabels_iff d).mp hd
      exact card_primitiveSourceFiber_of_fourteen_unit_letters g hm hg d hunit hcard
    _ = ∑ d ∈ (unitLabels m).filter (fun d => evalVec g m d = 0), Nat.factorial 14 := by
      rw [sum_filter]
    _ = Nat.factorial 14 * ((unitLabels m).filter fun d => evalVec g m d = 0).card := by
      simp [Nat.mul_comm]

end ArkLib.ProximityGap.Frontier.FoldedSourceFiber

#print axioms ArkLib.ProximityGap.Frontier.FoldedSourceFiber.globallyDisjoint_of_support_card
#print axioms ArkLib.ProximityGap.Frontier.FoldedSourceFiber.NR_eq_factorial_of_unit_letters
#print axioms
  ArkLib.ProximityGap.Frontier.FoldedSourceFiber.card_sourceFiber_of_fourteen_unit_letters
#print axioms
  ArkLib.ProximityGap.Frontier.FoldedSourceFiber.card_primitiveSourceFiber_of_fourteen_unit_letters
#print axioms ArkLib.ProximityGap.Frontier.FoldedSourceFiber.card_primitiveUnitSourcePairs
