/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFourPairPrime
import ArkLib.Research.ProximityGap.Frontier.DyadicMeanPairTransfer

/-! # Counting surviving complex minors of a non-dihedral modular involution -/

namespace ProximityGap.JointPairCounting
open Finset DyadicPairMinorTransfer

private def triples (I : Type*) : (I × I × I) ≃ (Fin 3 → I) where
  toFun t := ![t.1,t.2.1,t.2.2]
  invFun f := (f 0,f 1,f 2)
  left_inv _ := rfl
  right_inv f := by funext i;fin_cases i <;> rfl

/-- Count ordered nonzero triples by extending each ordered pair of distinct
indices. The loss of three includes the two repeated rows. -/
theorem count {L : ℕ} (P : (Fin 3 → Fin L) → Prop) [DecidablePred P]
    (localBound : ∀ u v : Fin L, u≠v →
      (univ.filter (fun k : Fin L => ¬P ![u,v,k])).card≤3) :
    L*(L-1)*(L-3)≤(univ.filter P).card := by
  classical
  let N (u v : Fin L) := (univ.filter (fun k : Fin L => P ![u,v,k])).card
  have extCount (u v : Fin L) (uv : u≠v) : L-3≤N u v := by
    have partition := card_filter_add_card_filter_not (s:=univ) (fun k : Fin L => P ![u,v,k])
    have bound := localBound u v uv
    simp only [card_univ,Fintype.card_fin] at partition
    dsimp [N];omega
  have row (u : Fin L) : (L-1)*(L-3) ≤ ∑ v,N u v := calc
    (L-1)*(L-3) = ∑ _v∈univ.erase u,(L-3) := by simp
    _ ≤ ∑ v∈univ.erase u,N u v := sum_le_sum (fun v hv => extCount u v (ne_of_mem_erase hv).symm)
    _ ≤ ∑ v,N u v := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have eq : (univ.filter P).card=∑ u,∑ v,N u v := by
    rw [card_filter]
    rw [←(triples (Fin L)).sum_comp]
    simp only [Fintype.sum_prod_type,N,card_filter]
    rfl
  have bound := sum_le_sum (s:=univ) (fun u _ => row u)
  simpa [eq,Nat.mul_assoc] using bound

/-- A fixed pair of distinct rows has at most three zero extensions at a
complex primitive root if the prime-field involution is non-dihedral. -/
theorem zero_extensions {m p L : ℕ} [Fact p.Prime] {z : ZMod p} {w : ℂ}
    (hz : IsPrimitiveRoot z (2^m)) (hw : IsPrimitiveRoot w (2^m))
    (q : Fin L × Fin 2 ↪ Fin (2^m)) (a b c : ZMod p)
    (law : ∀ i, c*z^(q (i,0)).val*z^(q (i,1)).val-a*(z^(q (i,0)).val+z^(q (i,1)).val)=b)
    (nonDihedral : ¬(a=0 ∨ c=0 ∧ b=0)) (u v : Fin L) (uv : u≠v) :
    (univ.filter (fun k : Fin L => minor (w^(q (u,0)).val) (w^(q (u,1)).val)
      (w^(q (v,0)).val) (w^(q (v,1)).val) (w^(q (k,0)).val) (w^(q (k,1)).val)=0)).card≤3 := by
  classical
  let W (i : Fin L) (j : Fin 2) := w^(q (i,j)).val
  let P (k : Fin L) := minor (W u 0) (W u 1) (W v 0) (W v 1) (W k 0) (W k 1)=0
  let S := univ.filter P
  change S.card≤3
  by_contra! tooMany
  have remove (s : Finset (Fin L)) (x : Fin L) : s.card≤(s.erase x).card+1 := by
    by_cases h : x∈s
    · exact (card_erase_add_one h).symm.le
    · simp [erase_eq_of_notMem h]
  obtain ⟨r,hr⟩ := DyadicSevenCombinatorics.select ((S.erase u).erase v) 2
    (by have := remove S u;have := remove (S.erase u) v;omega)
  have clean (i : Fin 2) : r i≠v ∧ r i≠u ∧ P (r i) := by
    have h := hr i
    simpa only [S,mem_erase,mem_filter,mem_univ,true_and] using h
  let g : Fin 4 → Fin L := ![u,v,r 0,r 1]
  have inj : Function.Injective g := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp_all [g, (clean 0).1,(clean 0).2.1,(clean 1).1,
      (clean 1).2.1,Ne.symm, (r.injective.ne (by decide : (0:Fin 2)≠1))]
  let e : Fin 4 × Fin 2 ↪ Fin (2^m) := (Function.Embedding.prodMap ⟨g,inj⟩ (Function.Embedding.refl _)).trans q
  apply nonDihedral (DyadicFourPairPrime.of_minors hz hw e a b c (fun i => law (g i)) ?_)
  intro i
  change P (g i)
  fin_cases i
  · simp [P,g,minor]
  · simp [P,g,minor]
  · exact (clean 0).2.2
  · exact (clean 1).2.2

end ProximityGap.JointPairCounting
#print axioms ProximityGap.JointPairCounting.zero_extensions
