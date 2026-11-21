/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarDividedPolynomial

/-! # The first Vandermonde defect beyond the apolar covering range -/

open Polynomial Finset
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarDividedPolynomial

namespace ProximityGap.ApolarSuccessorDefect

variable {K : Type*} [Field K] [DecidableEq K]

/-- For one site more than the Vandermonde covering range, every weighted
locator value times its nodal derivative equals the same next moment. -/
theorem site_defect (E : Finset K) (w : K → K) (f : K[X]) {s : ℕ} (hE : E.card=s+2)
    (ha : ApolarThrough (weighted E (RingHom.id K) w) f s) (y : K) (hy : y ∈ E) :
    w y*f.eval y*(Lagrange.nodal (E.erase y) id).eval y =
      weighted E (RingHom.id K) w (f*X^(s+1)) := by
  classical
  let G := Lagrange.nodal (E.erase y) id
  let L := weighted E (RingHom.id K) w
  have hd : G.natDegree=s+1 := by simp [G,hE,card_erase_of_mem hy]
  have hm : G.Monic := Lagrange.nodal_monic
  have hsplit : G.eraseLead+X^(s+1)=G := by
    simpa only [hd,hm.leadingCoeff,map_one,one_mul] using G.eraseLead_add_C_mul_X_pow
  have hh := ha G.eraseLead (G.eraseLead_natDegree_le.trans (by omega))
  have he (z : K) (hz : z ∈ E) (hne : z ≠ y) : G.eval z=0 :=
    Lagrange.eval_nodal_at_node (v:=id) (mem_erase.mpr ⟨hne,hz⟩)
  have hcol : L (f*G)=w y*f.eval y*G.eval y := by
    rw [show L=weighted E (RingHom.id K) w from rfl,weighted_apply,sum_eq_single_of_mem y hy]
    · simp [mul_assoc]
    · intro z hz h
      simp [he z hz h]
  rw [←hcol,←hsplit,mul_add,map_add,show L (f*G.eraseLead)=0 from hh,zero_add]

/-- Every error is covered or every error is missed when the support has
exactly s+2 nonzero weights. -/
theorem all_or_none (E : Finset K) (w : K → K) (f : K[X]) {s : ℕ} (hE : E.card=s+2)
    (ha : ApolarThrough (weighted E (RingHom.id K) w) f s) (hw : ∀ y ∈ E, w y ≠ 0) :
    (∀ y ∈ E, f.eval y=0) ∨ (∀ y ∈ E, f.eval y≠0) := by
  classical
  by_cases hc : weighted E (RingHom.id K) w (f*X^(s+1))=0
  · left
    intro y hy
    have hh := site_defect E w f hE ha y hy
    rw [hc] at hh
    have hn : (Lagrange.nodal (E.erase y) id).eval y ≠ 0 :=
      Lagrange.eval_nodal_not_at_node (fun z hz => (mem_erase.mp hz).1.symm)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hn)).resolve_left (hw y hy)
  · right
    intro y hy h
    apply hc
    rw [←site_defect E w f hE ha y hy,h,mul_zero,zero_mul]

/-- The error vanisher times the actual divided representative equals minus
the first non-annihilated moment modulo the locator, including multiplicities. -/
theorem residue_identity (E : Finset K) (w : K → K) (f : K[X]) {s : ℕ} (hE : E.card=s+2)
    (ha : ApolarThrough (weighted E (RingHom.id K) w) f s) :
    Lagrange.nodal E id * representative E id w f +
      C (weighted E (RingHom.id K) w (f*X^(s+1))) =
      f * ∑ y ∈ E,C (w y)*Lagrange.nodal (E.erase y) id := by
  classical
  let G (y : K) := Lagrange.nodal (E.erase y) id
  let c := weighted E (RingHom.id K) w (f*X^(s+1))
  let R := ∑ y ∈ E, C (w y*f.eval y)*G y
  have hR (z : K) (hz : z ∈ E) : R.eval z=c := by
    rw [show R=∑ y ∈ E,C (w y*f.eval y)*G y from rfl,eval_finsetSum,sum_eq_single_of_mem z hz]
    · simpa only [eval_mul,eval_C] using site_defect E w f hE ha z hz
    · intro y hy hne
      have hw : (G y).eval z=0 := Lagrange.eval_nodal_at_node (v:=id) (mem_erase.mpr ⟨hne.symm,hz⟩)
      rw [eval_mul,hw,mul_zero]
  have hRd : R.natDegree ≤ s+1 := by
    apply natDegree_sum_le_of_forall_le
    intro y hy
    exact (natDegree_C_mul_le _ _).trans (by simp [G,card_erase_of_mem hy,hE])
  have hRc : R=C c := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' R (C c) E
    · intro x hx
      simpa only [eval_C] using hR x hx
    · simp only [hE,natDegree_C]; omega
  rw [show C (weighted E (RingHom.id K) w (f*X^(s+1)))=R from hRc.symm]
  rw [representative,Finset.mul_sum,show R=∑ y ∈ E,C (w y*f.eval y)*G y from rfl,
    ← Finset.sum_add_distrib,Finset.mul_sum]
  apply sum_congr rfl
  intro y hy
  have hh := f.modByMonic_add_div (X-C y)
  rw [modByMonic_X_sub_C_eq_C_eval] at hh
  change C (f.eval y)+(X-C y)*divided f y=f at hh
  rw [Lagrange.nodal_eq_mul_nodal_erase hy,map_mul]
  conv_rhs => rw [←hh]
  change (X-C y)*G y*(C (w y)*divided f y) +
    C (w y)*C (f.eval y)*G y =
    (C (f.eval y)+(X-C y)*divided f y)*(C (w y)*G y)
  ring

#print axioms site_defect
#print axioms all_or_none
#print axioms residue_identity

end ProximityGap.ApolarSuccessorDefect
