/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R320KernelRelationL1Sparsity

/-!
# LANE B2 (#466 round 321): shadow autocorrelation is a doubled-depth histogram

A pair of depth-`r` signed-basis walks with difference `d` is equivalent to one
depth-`2r` walk ending at `d`: apply the antipodal permutation to the first walk and
concatenate it with the second.  This file constructs that equivalence and proves the exact
fiber-cardinality identity.

The next consumer identifies R314's `shadowRelationMass d` with this pair-difference count,
thereby replacing the per-relation autocorrelation unknown by the existing explicit histogram
`NR(2m,m,2r,d)`.

Issue #466, round 321, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition

/-- Antipodal index in the signed-basis model of the `2m` roots. -/
def antipodeIndex (m : ℕ) (a : Fin (2 * m)) : Fin (2 * m) :=
  if h : (a : ℕ) < m then
    ⟨(a : ℕ) + m, by omega⟩
  else
    ⟨(a : ℕ) - m, by omega⟩

/-- The antipodal index map is an involution. -/
theorem antipodeIndex_involutive (m : ℕ) : Function.Involutive (antipodeIndex m) := by
  intro a
  by_cases h : (a : ℕ) < m
  · have ha : antipodeIndex m a = ⟨(a : ℕ) + m, by omega⟩ := dif_pos h
    rw [ha]
    unfold antipodeIndex
    have hneg : ¬ ((⟨(a : ℕ) + m, by omega⟩ : Fin (2 * m)) : ℕ) < m := by
      simp
    rw [dif_neg hneg]
    ext
    simp
  · have ha : antipodeIndex m a = ⟨(a : ℕ) - m, by omega⟩ := dif_neg h
    rw [ha]
    unfold antipodeIndex
    have hpos : ((⟨(a : ℕ) - m, by omega⟩ : Fin (2 * m)) : ℕ) < m := by
      simp
      omega
    rw [dif_pos hpos]
    ext
    simp
    omega

/-- Antipodal indexing negates the signed basis vector. -/
theorem vecOf_antipodeIndex (m : ℕ) (a : Fin (2 * m)) :
    vecOf (2 * m) m (antipodeIndex m a) = -vecOf (2 * m) m a := by
  funext j
  unfold antipodeIndex vecOf
  split_ifs <;> simp_all <;> omega

/-- Antipodal index as a permutation. -/
def antipodeEquiv (m : ℕ) : Fin (2 * m) ≃ Fin (2 * m) :=
  { toFun := antipodeIndex m
    invFun := antipodeIndex m
    left_inv := antipodeIndex_involutive m
    right_inv := antipodeIndex_involutive m }

/-- Convert a pair `(t,u)` of depth-`r` tuples to the depth-`r+r` tuple consisting of
`u`, followed by the antipode of `t`. -/
def joinDifferenceTuple (m r : ℕ)
    (p : (Fin r → Fin (2 * m)) × (Fin r → Fin (2 * m))) :
    Fin (r + r) → Fin (2 * m) :=
  Fin.append p.2 (fun i => antipodeIndex m (p.1 i))

/-- `joinDifferenceTuple` is a genuine equivalence of the full tuple spaces. -/
def joinDifferenceEquiv (m r : ℕ) :
    ((Fin r → Fin (2 * m)) × (Fin r → Fin (2 * m))) ≃
      (Fin (r + r) → Fin (2 * m)) where
  toFun := joinDifferenceTuple m r
  invFun q :=
    (fun i => antipodeIndex m (q (Fin.natAdd r i)),
      fun i => q (Fin.castAdd r i))
  left_inv p := by
    apply Prod.ext
    · funext i
      simp only [joinDifferenceTuple, Fin.append_right]
      exact antipodeIndex_involutive m (p.1 i)
    · funext i
      simp [joinDifferenceTuple]
  right_inv q := by
    have hsecond :
        (fun i : Fin r => antipodeIndex m (antipodeIndex m (q (Fin.natAdd r i)))) =
          fun i : Fin r => q (Fin.natAdd r i) := by
      funext i
      exact antipodeIndex_involutive m _
    unfold joinDifferenceTuple
    rw [hsecond]
    exact Fin.append_castAdd_natAdd

/-- The joined tuple's shadow is exactly `shadow(u)-shadow(t)`. -/
theorem tupleVec_joinDifferenceTuple (m r : ℕ)
    (p : (Fin r → Fin (2 * m)) × (Fin r → Fin (2 * m))) :
    tupleVec (2 * m) m (r + r) (joinDifferenceTuple m r p) =
      fun j => tupleVec (2 * m) m r p.2 j - tupleVec (2 * m) m r p.1 j := by
  funext j
  unfold tupleVec joinDifferenceTuple
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, vecOf_antipodeIndex]
  simp only [Pi.neg_apply, Finset.sum_neg_distrib]
  omega

/-- Number of indexed tuple pairs whose signed-basis shadow difference is `d`. -/
def tuplePairDifferenceCount (m r : ℕ) (d : Fin m → ℤ) : ℕ :=
  ((Finset.univ : Finset
      ((Fin r → Fin (2 * m)) × (Fin r → Fin (2 * m)))).filter
    (fun p => (fun j => tupleVec (2 * m) m r p.2 j - tupleVec (2 * m) m r p.1 j) = d)).card

/-- **AUTOCORRELATION DOUBLING.**  The pair-difference fiber is exactly the depth-`2r`
shadow histogram at the same difference vector. -/
theorem tuplePairDifferenceCount_eq_NR (m r : ℕ) (d : Fin m → ℤ) :
    tuplePairDifferenceCount m r d = NR (2 * m) m (r + r) d := by
  classical
  unfold tuplePairDifferenceCount NR
  refine Finset.card_bij
    (i := fun p _ => joinDifferenceEquiv m r p) ?mem ?inj ?surj
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (tupleVec_joinDifferenceTuple m r p).trans hp.2
  · intro p hp q hq heq
    exact (joinDifferenceEquiv m r).injective heq
  · intro q hq
    rw [Finset.mem_filter] at hq
    let p := (joinDifferenceEquiv m r).symm q
    refine ⟨p, ?_, (joinDifferenceEquiv m r).apply_symm_apply q⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hjoin := tupleVec_joinDifferenceTuple m r p
    have hpq := (joinDifferenceEquiv m r).apply_symm_apply q
    change joinDifferenceTuple m r p = q at hpq
    rw [hpq] at hjoin
    exact hjoin.symm.trans hq.2

/-- Partitioning tuple pairs by their two shadow keys expresses a difference fiber as the
`NR(v)NR(w)`-weighted sum over key pairs with `w-v=d`. -/
theorem tuplePairDifferenceCount_eq_sum_keyPairs (m r : ℕ) (d : Fin m → ℤ) :
    tuplePairDifferenceCount m r d =
      ∑ p ∈ ((keysR (2 * m) m r) ×ˢ (keysR (2 * m) m r)).filter
          (fun p => shadowDifference p = d),
        NR (2 * m) m r p.1 * NR (2 * m) m r p.2 := by
  classical
  let U : Finset (Fin r → Fin (2 * m)) := Finset.univ
  let Q := (U ×ˢ U).filter (fun q =>
    shadowDifference (tupleVec (2 * m) m r q.1, tupleVec (2 * m) m r q.2) = d)
  let T := ((keysR (2 * m) m r) ×ˢ (keysR (2 * m) m r)).filter
    (fun p => shadowDifference p = d)
  let f := fun q : (Fin r → Fin (2 * m)) × (Fin r → Fin (2 * m)) =>
    (tupleVec (2 * m) m r q.1, tupleVec (2 * m) m r q.2)
  have hmaps : ∀ q ∈ Q, f q ∈ T := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
    refine ⟨⟨?_, ?_⟩, hq.2⟩
    · exact Finset.mem_image_of_mem _ (Finset.mem_univ q.1)
    · exact Finset.mem_image_of_mem _ (Finset.mem_univ q.2)
  have hfiber : ∀ p ∈ T,
      (Q.filter (fun q => f q = p)).card =
        NR (2 * m) m r p.1 * NR (2 * m) m r p.2 := by
    intro p hp
    let A := U.filter (fun t => tupleVec (2 * m) m r t = p.1)
    let B := U.filter (fun t => tupleVec (2 * m) m r t = p.2)
    have hset : Q.filter (fun q => f q = p) = A ×ˢ B := by
      ext q
      simp only [Q, T, f, A, B, Finset.mem_filter, Finset.mem_product]
      rw [Finset.mem_filter] at hp
      constructor
      · rintro ⟨⟨hqU, _hqd⟩, hqf⟩
        exact ⟨⟨hqU.1, congrArg Prod.fst hqf⟩,
          ⟨hqU.2, congrArg Prod.snd hqf⟩⟩
      · rintro ⟨⟨hq1, hqf1⟩, ⟨hq2, hqf2⟩⟩
        have hqf : f q = p := Prod.ext hqf1 hqf2
        have hqd :
            shadowDifference
              (tupleVec (2 * m) m r q.1, tupleVec (2 * m) m r q.2) = d := by
          change shadowDifference (f q) = d
          rw [hqf]
          exact hp.2
        exact ⟨⟨⟨hq1, hq2⟩, hqd⟩, hqf⟩
    rw [hset, Finset.card_product]
    unfold NR
    rfl
  unfold tuplePairDifferenceCount
  change Q.card = ∑ p ∈ T, NR (2 * m) m r p.1 * NR (2 * m) m r p.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  exact Finset.sum_congr rfl hfiber

/-- **RELATION MASS DOUBLING.**  For every realized finite-field kernel relation, its R314
histogram autocorrelation mass is exactly the characteristic-zero depth-`2r` histogram at
that relation. -/
theorem shadowRelationMass_eq_NR_double
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g (2 * m) m r) :
    shadowRelationMass g (2 * m) m r d = NR (2 * m) m (r + r) d := by
  classical
  have hdstruct := shadowKernelRelation_ne_zero_and_evalVec_eq_zero
    g (2 * m) m r hd
  rw [← tuplePairDifferenceCount_eq_NR]
  rw [tuplePairDifferenceCount_eq_sum_keyPairs]
  unfold shadowRelationMass shadowCollisionPairs
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨hp1, hp2, hne⟩, heval⟩, hdiff⟩
    exact ⟨⟨hp1, hp2⟩, hdiff⟩
  · rintro ⟨⟨hp1, hp2⟩, hdiff⟩
    have hne : p.1 ≠ p.2 := by
      intro heq
      apply hdstruct.1
      rw [← hdiff]
      funext j
      change p.2 j - p.1 j = 0
      rw [heq]
      simp
    have heval : evalVec g m p.1 = evalVec g m p.2 := by
      have hzero : evalVec g m (shadowDifference p) = 0 := by
        rw [hdiff, hdstruct.2]
      rw [evalVec_shadowDifference] at hzero
      exact sub_eq_zero.mp hzero |>.symm
    exact ⟨⟨⟨hp1, hp2, hne⟩, heval⟩, hdiff⟩

/-- The full finite-field collision surplus is exactly the doubled-depth integer histogram
summed over the realized nonzero kernel relations. -/
theorem shadowCollisionMass_eq_sum_NR_double
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) :
    shadowCollisionMass g (2 * m) m r =
      ∑ d ∈ shadowKernelRelations g (2 * m) m r, NR (2 * m) m (r + r) d := by
  rw [shadowCollisionMass_eq_sum_relationMass]
  exact Finset.sum_congr rfl fun d hd => shadowRelationMass_eq_NR_double g m r hd

end ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling

/-! ## Axiom audit (must contain no `sorryAx`) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling.vecOf_antipodeIndex
#print axioms
  ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling.tupleVec_joinDifferenceTuple
#print axioms
  ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling.tuplePairDifferenceCount_eq_NR
#print axioms
  ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling.shadowRelationMass_eq_NR_double
#print axioms
  ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling.shadowCollisionMass_eq_sum_NR_double
