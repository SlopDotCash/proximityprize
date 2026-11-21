/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.LinearAlgebra.Lagrange

/-! # Lifting affine-line MCA along a polynomial with full evaluation fibers

When a degree-m polynomial identifies the upstairs evaluation points in fibers
of size m, each base witness lifts with the same agreement fraction and the RS
dimension scales exactly by m. Polynomial interpolation on the base witness
recovers a low-degree explanation from any putative joint explanation upstairs.
-/
set_option autoImplicit false
namespace ProximityGap.FullFiberMcaLift
open Finset Polynomial
open scoped NNReal ENNReal
variable {I J F : Type} [Fintype I] [Fintype J] [Field F] [DecidableEq F]
variable [DecidableEq J]

private def preimage (π : I → J) (S : Finset J) : Finset I := univ.filter (fun i => π i ∈ S)

omit [Fintype J] in
private theorem card_preimage (π : I → J) {m : ℕ}
    (hfib : ∀ j, (univ.filter fun i => π i = j).card = m) (S : Finset J) :
    (preimage π S).card = S.card * m := by
  classical
  have h := card_eq_sum_card_fiberwise (s := preimage π S) (t := S) (f := π)
    (fun i hi => (mem_filter.mp hi).2)
  rw [h]
  have he (j : J) (hj : j ∈ S) : (preimage π S).filter (fun i => π i = j) =
      univ.filter (fun i => π i = j) := by
    ext i
    simp only [preimage, mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl
    exact hj
  calc ∑ j ∈ S, ((preimage π S).filter fun i => π i = j).card = ∑ _j ∈ S, m :=
         sum_congr rfl fun j hj => (congrArg Finset.card (he _ hj)).trans (hfib j)
    _ = _ := by simp

omit [Fintype J] in
private theorem descends (D : I ↪ F) (E : J ↪ F) (π : I → J) (P : F[X]) {k m : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hP : P.natDegree = m) (hdom : ∀ i, P.eval (D i) = E (π i))
    (hfib : ∀ j, (univ.filter fun i => π i = j).card = m)
    (S : Finset J) (u : J → F) (Q : F[X]) (hQ : Q.natDegree < k*m)
    (hfit : ∀ i ∈ preimage π S, Q.eval (D i) = u (π i)) :
    ∃ v ∈ ReedSolomon.code E k, ∀ j ∈ S, v j = u j := by
  classical
  let q := Lagrange.interpolate S E u
  have hqdeg : q.degree < S.card := Lagrange.degree_interpolate_lt u E.injective.injOn
  have hqval (j : J) (hj : j ∈ S) : q.eval (E j) = u j :=
    Lagrange.eval_interpolate_at_node _ E.injective.injOn hj
  refine ⟨fun j => q.eval (E j), ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval q ?_
    (fun _ => rfl), hqval⟩
  rcases le_or_gt S.card k with hs | hs
  · exact hqdeg.trans_le (by exact_mod_cast hs)
  · have hpos : 0 < S.card := hk.trans hs
    have hqc : q.natDegree < S.card := by
      by_cases hq : q = 0
      · simpa [hq] using hpos
      · exact (natDegree_lt_iff_degree_lt hq).mpr hqdeg
    have heq : Q = q.comp P := by
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (preimage π S) D.injective.injOn
      · rw [card_preimage π hfib]
        exact (degree_le_natDegree.trans_lt (by exact_mod_cast hQ.trans (Nat.mul_lt_mul_of_pos_right hs hm)))
      · rw [card_preimage π hfib]
        apply degree_le_natDegree.trans_lt
        exact_mod_cast (show (q.comp P).natDegree < S.card*m by
          rw [natDegree_comp, hP]
          exact Nat.mul_lt_mul_of_pos_right hqc hm)
      · intro i hi
        rw [eval_comp, hdom, hqval (π i) (mem_filter.mp hi).2, hfit i hi]
    rw [heq, natDegree_comp, hP] at hQ
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (Nat.lt_of_mul_lt_mul_right hQ))

/-- Each bad scalar on the base stays bad after pulling both rows back through the
projection. The upstairs RS dimension is exactly the base dimension times the degree. -/
theorem mcaEvent_lift (D : I ↪ F) (E : J ↪ F) (π : I → J) (P : F[X]) {k m : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hP : P.natDegree = m) (hdom : ∀ i, P.eval (D i) = E (π i))
    (hfib : ∀ j, (univ.filter fun i => π i = j).card = m) (δ : ℝ≥0) (u₀ u₁ : J → F) (γ : F)
    (hbad : mcaEvent (F := F) (ReedSolomon.code E k : Set (J → F)) δ u₀ u₁ γ) :
    mcaEvent (F := F) (ReedSolomon.code D (k*m) : Set (I → F)) δ (u₀ ∘ π) (u₁ ∘ π) γ := by
  classical
  let : NeZero k := ⟨hk.ne'⟩
  let : NeZero (k*m) := ⟨(Nat.mul_pos hk hm).ne'⟩
  obtain ⟨S,hsize,⟨w,hw,hagr⟩,hpair⟩ := hbad
  have hn : Fintype.card I = Fintype.card J * m := by simpa [preimage] using card_preimage π hfib univ
  refine ⟨preimage π S, ?_, ?_, ?_⟩
  · rw [card_preimage π hfib, hn, Nat.cast_mul, Nat.cast_mul, ← mul_assoc]
    gcongr
  · obtain ⟨q,hq,he⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
    refine ⟨fun i => (q.comp P).eval (D i), ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
      (q.comp P) (by rw [natDegree_comp,hP]; exact Nat.mul_lt_mul_of_pos_right hq hm)
      (fun _ => rfl), ?_⟩
    intro i hi
    change (q.comp P).eval (D i) = u₀ (π i) + γ • u₁ (π i)
    rw [eval_comp, hdom, he, hagr (π i) (mem_filter.mp hi).2]
  · rintro ⟨v₀,hv₀,v₁,hv₁,hboth⟩
    obtain ⟨Q₀,hQ₀,he₀⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv₀
    obtain ⟨Q₁,hQ₁,he₁⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv₁
    obtain ⟨b₀,hb₀,hf₀⟩ := descends D E π P hm hk hP hdom hfib S u₀ Q₀ hQ₀
      (fun i hi => (he₀ i).trans (hboth i hi).1)
    obtain ⟨b₁,hb₁,hf₁⟩ := descends D E π P hm hk hP hdom hfib S u₁ Q₁ hQ₁
      (fun i hi => (he₁ i).trans (hboth i hi).2)
    exact hpair ⟨b₀,hb₀,b₁,hb₁,fun j hj => ⟨hf₀ j hj,hf₁ j hj⟩⟩

/-- Polynomial fiber lifts preserve the rate and can only increase worst-case MCA error. -/
theorem epsMCA_le [Fintype F] [Nonempty I] [Nonempty J] [DecidableEq I]
    (D : I ↪ F) (E : J ↪ F) (π : I → J) (P : F[X]) {k m : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hP : P.natDegree = m) (hdom : ∀ i, P.eval (D i) = E (π i))
    (hfib : ∀ j, (univ.filter fun i => π i = j).card = m) (δ : ℝ≥0) :
    epsMCA (F := F) (ReedSolomon.code E k : Set (J → F)) δ ≤
      epsMCA (F := F) (ReedSolomon.code D (k*m) : Set (I → F)) δ := by
  classical
  rw [epsMCA_eq_iSup_badCount_div,epsMCA_eq_iSup_badCount_div]
  apply ENNReal.div_le_div_right _ _
  apply iSup_le
  intro u
  let v : Code.WordStack F (Fin 2) I := fun j => u j ∘ π
  apply le_iSup_of_le v
  apply Nat.cast_le.mpr
  apply card_le_card
  intro γ hγ
  exact mem_filter.mpr ⟨mem_univ _, mcaEvent_lift D E π P hm hk hP hdom hfib δ (u 0) (u 1) γ
    (mem_filter.mp hγ).2⟩

#print axioms epsMCA_le
end ProximityGap.FullFiberMcaLift
