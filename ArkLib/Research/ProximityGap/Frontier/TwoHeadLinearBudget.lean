/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CriticalLinearBudget
import Mathlib.LinearAlgebra.Lagrange

/-! # Two affine heads at the half-distance transition on any domain

Choose two disjoint private site sets of e+1 points each. A locator H vanishes
on their common complement. Use the zero head on one private set and (XH,H)
on the other. Every private coordinate i gives its distinct bad challenge
−xᵢ on the opposing core together with i.
-/

set_option autoImplicit false
namespace ProximityGap.TwoHeadLinearBudget
open Finset Polynomial Lagrange MCAThresholdLedger
open scoped NNReal ENNReal
variable {I F : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
private theorem bad_extension (x : I ↪ F) {k e : ℕ} (T : Finset I) (hs : T.card=e+1)
    (hk : k≤Tᶜ.card) (u v c d : I → F) (hc : c ∈ ReedSolomon.code x k)
    (hd : d ∈ ReedSolomon.code x k) (agree : ∀ j ∉ T, c j = u j ∧ d j = v j)
    {i : I} (hi : i ∈ T) (z : F) (acc : c i+z*d i=u i+z*v i) (miss : d i≠v i) :
    mcaEvent (F:=F) (ReedSolomon.code x k : Set (I → F)) ((e:ℝ≥0)/(Fintype.card I)) u v z := by
  classical
  have size := T.card_le_univ
  have ni : (Fintype.card I:ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : e ≤ Fintype.card I := by omega
  refine ⟨insert i Tᶜ,?_,⟨c+z • d,(ReedSolomon.code x k).add_mem hc ((ReedSolomon.code x k).smul_mem z hd),?_⟩,?_⟩
  · rw [card_insert_of_notMem (fun h => (mem_compl.mp h) hi),card_compl,hs,
      tsub_mul,one_mul,div_mul_cancel₀ _ ni,← Nat.cast_tsub]
    exact_mod_cast (show Fintype.card I-e ≤ Fintype.card I-(e+1)+1 by omega)
  · intro j hj
    rcases mem_insert.mp hj with eq|hj
    · exact eq ▸ acc
    · obtain ⟨h₁,h₂⟩ := agree j (mem_compl.mp hj)
      change c j+z*d j = u j+z*v j
      rw [h₁,h₂]
  · rintro ⟨_,_,w,hw,h⟩
    have eq : w=d := ReedSolomon.eq_of_agree_of_card_le hw hd hk fun j hj =>
      ((h j (mem_insert_of_mem hj)).2).trans (agree j (mem_compl.mp hj)).2.symm
    exact miss (eq ▸ (h i (mem_insert_self i _)).2)

set_option maxHeartbeats 1200000 in
/-- Over every finite field, on every domain satisfying the three integer
inequalities, one received pair has at least 2(e+1) distinct bad challenges. -/
theorem errors (x : I ↪ F) {k e : ℕ} (private_room : 2*(e+1)≤Fintype.card I)
    (degree_room : Fintype.card I≤k+2*e) (core_room : k+e+1≤Fintype.card I) :
    ((2*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F) ≤
      epsMCA (F:=F) (ReedSolomon.code x k : Set (I → F)) ((e:ℝ≥0)/(Fintype.card I)) := by
  classical
  obtain ⟨S,_,hs⟩ := exists_subset_card_eq (s:=(univ : Finset I))
    (show e+1≤univ.card by rw [card_univ];omega)
  obtain ⟨T,hT,ht⟩ := exists_subset_card_eq (s:=Sᶜ) (show e+1≤Sᶜ.card by rw [card_compl,hs];omega)
  have dis : Disjoint S T := disjoint_left.mpr fun i hi hti => (mem_compl.mp (hT hti)) hi
  have size : (S ∪ T).card = 2*(e+1) := by rw [card_union_of_disjoint dis,hs,ht];omega
  let C := (S ∪ T)ᶜ
  let H := nodal C x
  let d (i : I) := H.eval (x i)
  let c (i : I) := (x i)*d i
  have deg : H.natDegree+1<k := by rw [natDegree_nodal];dsimp only [C];rw [card_compl,size];omega
  have : NeZero k := ⟨by omega⟩
  have hd : d ∈ ReedSolomon.code x k := ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr
    ⟨H,by omega,fun _ => rfl⟩
  have hc : c ∈ ReedSolomon.code x k := ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr
    ⟨(Polynomial.X : F[X])*H,by
      apply natDegree_mul_le.trans_lt
      simpa only [natDegree_X,Nat.add_comm 1] using deg,fun i => by simp [c,d]⟩
  have nz {i : I} (hi : i ∈ S ∪ T) : d i ≠ 0 := eval_nodal_not_at_node fun j hj eq =>
    (mem_compl.mp hj) (x.injective eq ▸ hi)
  let v (i : I) := if i∈T then d i else 0
  let u (i : I) := x i*v i
  let labels := (S ∪ T).image fun i => -(x i)
  have bound := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code x k : Set (I → F)) ((e:ℝ≥0)/Fintype.card I) ![u,v] labels (by
      intro z hz
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
      rcases mem_union.mp hi with hS|hTi
      · have notT := disjoint_left.mp dis hS
        apply bad_extension x S hs (by rw [card_compl,hs];omega) u v c d hc hd _ hS
        · simp [c,u,v,notT]
        · simpa [v,notT] using nz (mem_union_left T hS)
        · intro j jS
          by_cases jT : j∈T
          · simp [c,u,v,jT]
          · have zH : d j=0 := eval_nodal_at_node (mem_compl.mpr (fun h => (mem_union.mp h).elim jS jT))
            simp [c,u,v,jT,zH]
      · apply bad_extension x T ht (by rw [card_compl,ht];omega) u v 0 0
          (ReedSolomon.code x k).zero_mem (ReedSolomon.code x k).zero_mem _ hTi
        · simp [u,v,hTi]
        · simpa [v,hTi,ne_comm] using nz (mem_union_right S hTi)
        · intro j jT
          simp [u,v,jT])
  have count : labels.card = 2*(e+1) := (card_image_of_injective _ (neg_injective.comp x.injective)).trans size
  simpa only [count] using bound

end ProximityGap.TwoHeadLinearBudget
#print axioms ProximityGap.TwoHeadLinearBudget.errors
