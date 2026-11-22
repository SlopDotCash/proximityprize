/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.LocatorShortening
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor

/-! # MCA invariance under translated inversion of evaluation sites -/

namespace ProximityGap.ProjectiveDomainMass
open Polynomial Finset Code
open scoped NNReal ENNReal
variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F]

/-- Diagonal equivalence of two field codes transports every bad scalar. -/
theorem diagonal_le (C C' : Set (I → F)) (m : I → F) (hm : ∀ i, m i≠0)
    (forward : ∀ w∈C, (fun i => m i*w i)∈C')
    (back : ∀ w∈C', (fun i => (m i)⁻¹*w i)∈C) (δ : ℝ≥0) :
    epsMCA (F:=F) C δ ≤ epsMCA (F:=F) C' δ := by
  classical
  rw [epsMCA_eq_iSup_badCount_div,epsMCA_eq_iSup_badCount_div]
  apply ENNReal.div_le_div_right
  apply iSup_le
  intro u
  let v : WordStack F (Fin 2) I := fun b i => m i*u b i
  apply le_iSup_of_le v
  apply Nat.cast_le.mpr
  apply card_le_card
  intro γ hγ
  obtain ⟨S,hS,⟨w,hw,hagree⟩,hno⟩ := (mem_filter.mp hγ).2
  apply mem_filter.mpr
  refine ⟨mem_univ _,S,hS,⟨_,forward w hw,?_⟩,?_⟩
  · intro i hi
    change m i*w i=m i*u 0 i+γ*(m i*u 1 i)
    rw [hagree i hi,smul_eq_mul]; ring
  · rintro ⟨a,ha,b,hb,hab⟩
    apply hno
    refine ⟨_,back a ha,_,back b hb,?_⟩
    intro i hi
    obtain ⟨h₀,h₁⟩ := hab i hi
    change a i=m i*u 0 i at h₀
    change b i=m i*u 1 i at h₁
    simp [h₀,h₁,hm i]

omit [Fintype F] [Nonempty I] [DecidableEq I] in
private theorem reciprocal_word (D E : I ↪ F) (nonzero : ∀ i, D i≠0)
    (sites : ∀ i, E i=(D i)⁻¹) (k : ℕ) [NeZero k] {w : I → F} (hw : w∈ReedSolomon.code E k) :
    (fun i => D i^(k-1)*w i)∈ReedSolomon.code D k := by
  obtain ⟨P,hP,ev⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
  have hd : P.natDegree≤k-1 := by omega
  let R := reflect (k-1) P
  have hR : R.natDegree≤k-1 := natDegree_reflect_le.trans (max_le le_rfl hd)
  refine ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨R,by omega,?_⟩
  intro i
  let _ := invertibleOfNonzero (inv_ne_zero (nonzero i))
  have h := eval₂_reflect_mul_pow (RingHom.id F) (D i)⁻¹ (k-1) P hd
  rw [invOf_eq_inv,inv_inv,eval₂_id,eval₂_id,←sites,ev,sites,inv_pow] at h
  change (reflect (k-1) P).eval (D i)=D i^(k-1)*w i
  rw [← h]
  field_simp [nonzero i]

/-- Coordinate inversion preserves the worst MCA probability when every site
is nonzero, at every positive dimension and every real radius. -/
theorem inversion (D E : I ↪ F) (nonzero : ∀ i, D i≠0) (sites : ∀ i, E i=(D i)⁻¹)
    (k : ℕ) [NeZero k] (δ : ℝ≥0) :
    epsMCA (F:=F) (ReedSolomon.code E k : Set (I → F)) δ =
      epsMCA (F:=F) (ReedSolomon.code D k : Set (I → F)) δ := by
  have nz' (i : I) : E i≠0 := sites i ▸ inv_ne_zero (nonzero i)
  have back (i : I) : D i=(E i)⁻¹ := by rw [sites,inv_inv]
  have le (D E : I ↪ F) (hd : ∀ i, D i≠0) (he : ∀ i, E i≠0)
      (s : ∀ i, E i=(D i)⁻¹) (t : ∀ i, D i=(E i)⁻¹) :
      epsMCA (F:=F) (ReedSolomon.code E k : Set (I → F)) δ ≤
        epsMCA (F:=F) (ReedSolomon.code D k : Set (I → F)) δ := by
    apply diagonal_le _ _ (fun i => D i^(k-1)) (fun i => pow_ne_zero _ (hd i))
    · exact fun _ hw => reciprocal_word D E hd s k hw
    · intro w hw
      change (fun i => (D i^(k-1))⁻¹*w i)∈ReedSolomon.code E k
      simpa only [s,inv_pow] using reciprocal_word E D he t k hw
  exact le_antisymm (le D E nonzero nz' sites back) (le E D nz' nonzero back sites)

omit [Fintype I] [Fintype F] [Nonempty I] [DecidableEq I] in
/-- Translating all sites preserves the Reed–Solomon code as a set of words. -/
theorem translated_code (D E : I ↪ F) (a : F) (sites : ∀ i, E i = D i+a)
    (k : ℕ) [NeZero k] : ReedSolomon.code E k = ReedSolomon.code D k := by
  have subset (D E : I ↪ F) (a : F) (s : ∀ i, E i=D i+a) : ReedSolomon.code E k ≤ ReedSolomon.code D k := by
    intro w hw
    obtain ⟨P,hP,ev⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
    exact ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨taylor a P,by simpa using hP,fun i => by
      rw [taylor_eval,←s,ev]⟩
  exact le_antisymm (subset D E a sites) (subset E D (-a) (fun i => by simp [sites]))

end ProximityGap.ProjectiveDomainMass
#print axioms ProximityGap.ProjectiveDomainMass.inversion
