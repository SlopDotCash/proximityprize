/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AgreementSlicePacking
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Limits of bounds based on agreement-set intersections

An auxiliary finite field labels the coordinates. Coloring each locator by its
highest nonleading coefficients produces large constant-weight block families
with the same pairwise intersection cap as a Reed–Solomon list.
-/

namespace ProximityGap.AgreementSupportBarrier

open Finset Polynomial

/-- A color records the coefficients in degrees `k,...,t-1`. If two locators
have the same color their difference has degree below `k`, so the corresponding
blocks meet in fewer than `k` points. -/
theorem exists_family {I F : Type*} [Fintype I] [DecidableEq I] [Fintype F] [Field F]
    (D : I ↪ F) (k t B : ℕ) (hk : 0 < k) (hkt : k ≤ t)
    (hB : (Fintype.card F)^(t-k)*B < (Fintype.card I).choose t) :
    ∃ A : Finset (Finset I), B < A.card ∧ (∀ S ∈ A, S.card=t) ∧
      ∀ S ∈ A, ∀ T ∈ A, S ≠ T → (S ∩ T).card < k := by
  classical
  let loc (S : Finset I) : F[X] := ∏ i ∈ S, (X - C (D i))
  let key (S : Finset I) (j : Fin (t-k)) := (loc S).coeff (k+j.val)
  let blocks := (univ : Finset I).powersetCard t
  obtain ⟨y, _, hmany⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := blocks) (t := univ) (f := key) (fun _ _ => mem_univ _)
    (show univ.card * B < blocks.card by simpa [blocks,Fintype.card_fun] using hB)
  let A := blocks.filter fun S => key S = y
  have size {S} (h : S ∈ A) : S.card = t := (mem_powersetCard.mp (mem_filter.mp h).1).2
  refine ⟨A,hmany,fun _ h => size h,?_⟩
  intro S hS T hT hne
  have dS : (loc S).natDegree=t := by simp [loc,size hS]
  have dT : (loc T).natDegree=t := by simp [loc,size hT]
  have mS : (loc S).Monic := monic_prod_X_sub_C _ _
  have mT : (loc T).Monic := monic_prod_X_sub_C _ _
  have kd : (loc S - loc T).natDegree < k := by
    suffices (loc S - loc T).natDegree ≤ k-1 by omega
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_sub,sub_eq_zero]
    rcases lt_trichotomy j t with h | rfl | h
    · have hh := congrFun ((mem_filter.mp hS).2.trans (mem_filter.mp hT).2.symm)
        (⟨j-k,by omega⟩ : Fin (t-k))
      simpa [key,show k+(j-k)=j by omega] using hh
    · exact (dS ▸ mS.coeff_natDegree).trans (dT ▸ mT.coeff_natDegree).symm
    · rw [coeff_eq_zero_of_natDegree_lt (dS ▸ h), coeff_eq_zero_of_natDegree_lt (dT ▸ h)]
  have roots (U : Finset I) (i : I) : (loc U).eval (D i) = 0 ↔ i ∈ U := by
    simp [loc,eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero,D.injective.eq_iff]
  by_contra! hover
  have heq := eq_zero_of_natDegree_lt_card_of_eval_eq_zero (loc S-loc T)
    (f := fun i : ↥(S ∩ T) => D i.val) (D.injective.comp Subtype.val_injective)
    (fun i => by rw [eval_sub,(roots S i).mpr (mem_inter.mp i.property).1,
      (roots T i).mpr (mem_inter.mp i.property).2,sub_self])
    (by simpa only [Fintype.card_coe] using kd.trans_le hover)
  have hl := sub_eq_zero.mp heq
  exact hne (Finset.ext fun i => (roots S i).symm.trans (hl ▸ roots T i))

open ArkLib.ProximityGap.Frontier.DyadicLogWitness237 (P)

set_option maxRecDepth 10000

private noncomputable def labels (n p : ℕ) [NeZero p] (h : n ≤ p) : Fin n ↪ ZMod p :=
  (Fin.castLEEmb h).trans ((Fintype.equivFinOfCardEq (ZMod.card p)).symm.toEmbedding)

/-- At 66 agreements in 128 sites and dimension 64 the abstract support bound
exceeds the 237-bit field's budget. -/
theorem length128 : ∃ A : Finset (Finset (Fin 128)), P/2^128 < A.card ∧
    (∀ S ∈ A, S.card=66) ∧ ∀ S ∈ A, ∀ T ∈ A, S ≠ T → (S ∩ T).card < 64 := by
  let : Fact (Nat.Prime 131) := ⟨by decide⟩
  apply exists_family (labels 128 131 (by decide)) 64 66 _ (by decide) (by decide)
  rw [ZMod.card,Fintype.card_fin,Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The four length-1024 support families at the largest agreement counts
certified by the 1031-element auxiliary alphabet. -/
theorem length1024 (k t : ℕ) (h : (k=512 ∧ t=600) ∨ (k=256 ∧ t=338) ∨
    (k=128 ∧ t=186) ∨ (k=64 ∧ t=99)) :
    ∃ A : Finset (Finset (Fin 1024)), P/2^128 < A.card ∧ (∀ S ∈ A, S.card=t) ∧
      ∀ S ∈ A, ∀ T ∈ A, S ≠ T → (S ∩ T).card < k := by
  let : Fact (Nat.Prime 1031) := ⟨by decide⟩
  apply exists_family (labels 1024 1031 (by decide)) k t
  all_goals rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals first | (rw [ZMod.card,Fintype.card_fin,Nat.choose_eq_descFactorial_div_factorial]; decide) | decide

end ProximityGap.AgreementSupportBarrier

#print axioms ProximityGap.AgreementSupportBarrier.length128
#print axioms ProximityGap.AgreementSupportBarrier.length1024
