/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SaturatedListCliques
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Lagrange

/-! # Four completely split message differences at the rate-half Johnson successor

An oversized list at 314491700 errors contains four messages with six pairwise
differences split over the ground field. Each of the six differences has at least
536870910 distinct roots on the selected center agreements.
-/

namespace ProximityGap.HalfListSplitDifferences

open Code Polynomial Finset SaturatedListCliques

variable {I F : Type} [Fintype I] [DecidableEq I] [Field F]

/-- The integer multiplicities force more near-maximal intersections than any
four-clique-free graph on one block length plus one vertices can have. -/
theorem four_agreement_sets (S : Fin 1073741825 → Finset I)
    (hn : Fintype.card I = 1073741824) (ht : ∀ i, 759250124 ≤ (S i).card)
    (hp : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 536870911) :
    ¬ (fullGraph S 536870910).CliqueFree 4 := by
  classical
  intro hfree
  have hsum := forced_edges_above (b := 536870909) (c := 2) S ht hp 759250124
  rw [hn] at hsum
  have hedges : (fullGraph S 536870910).edgeFinset.card ≤
      SimpleGraph.turanNumber 1073741825 3 := by
    simpa only [Fintype.card_fin] using hfree.card_edgeFinset_le
  rw [SimpleGraph.turanNumber_eq, Nat.choose_two_right] at hedges
  norm_num at hedges hsum
  omega

/-- A polynomial with all but at most one of its degrees accounted for by
distinct evaluation roots splits over the ground field. -/
theorem splits_of_many_roots (D : I ↪ F) (A : Finset I) {f : F[X]}
    (hn : f ≠ 0) (hd : f.natDegree ≤ A.card+1) (hf : ∀ i ∈ A, f.eval (D i) = 0) :
    f.Splits := by
  classical
  obtain ⟨Q,hQ⟩ := Polynomial.prod_X_sub_C_dvd A D D.injective.injOn f hf
  change f = Lagrange.nodal A D * Q at hQ
  have hnQ : Q ≠ 0 := fun he => hn (by simpa [he] using hQ)
  rw [hQ,natDegree_mul Lagrange.nodal_ne_zero hnQ,Lagrange.natDegree_nodal] at hd
  rw [hQ]
  exact (Splits.prod (fun i _ => Splits.X_sub_C (D i))).mul
    (Splits.of_natDegree_le_one (by omega))

/-- In any oversized scalar list at the first half-rate Hamming step below
strict Johnson, a four-clique has all six polynomial differences split. -/
theorem from_list (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hlist : (1073741824 : ℕ∞) < Lambda (ReedSolomon.code D 536870912 : Set (I → F))
      ((314491700 : ℝ)/1073741824)) :
    ∃ (y : I → F) (P : Fin 1073741825 → F[X]) (S : Fin 1073741825 → Finset I),
      Function.Injective P ∧ (∀ i, (P i).natDegree < 536870912) ∧
      (∀ i, (S i).card = 759250124) ∧ (∀ i x, x ∈ S i → (P i).eval (D x) = y x) ∧
      ¬ (fullGraph S 536870910).CliqueFree 4 ∧
      ∀ i j, (fullGraph S 536870910).Adj i j → (P i - P j).Splits := by
  classical
  have h : ((1073741824 : ℕ) : ℕ∞) < Lambda (ReedSolomon.code D 536870912 : Set (I → F))
      (((Fintype.card I-759250124 : ℕ) : ℝ)/Fintype.card I) := by
    simpa only [hn, Nat.reduceSub, Nat.cast_ofNat] using hlist
  obtain ⟨y,P,S,hi,hdeg,hsize,hag,hfour⟩ :=
    from_list_at_overlap D (by decide : 0 < 536870912) (by omega : 759250124 ≤ Fintype.card I)
      (by omega) (fun S ht hp => four_agreement_sets S hn (fun i => (ht i).ge) hp) h
  refine ⟨y,P,S,hi,hdeg,hsize,hag,hfour,?_⟩
  intro i j hij
  apply splits_of_many_roots D (S i ∩ S j) (sub_ne_zero.mpr (hi.ne hij.1))
  · have hd := natDegree_sub_le (P i) (P j)
    have ha := hdeg i
    have hb := hdeg j
    have hc := hij.2
    omega
  · intro x hx
    obtain ⟨hx₁,hx₂⟩ := mem_inter.mp hx
    rw [eval_sub,hag i x hx₁,hag j x hx₂,sub_self]

#print axioms four_agreement_sets
#print axioms from_list

end ProximityGap.HalfListSplitDifferences
