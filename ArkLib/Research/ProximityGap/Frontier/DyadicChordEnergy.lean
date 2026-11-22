/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFrobeniusNorm
import Mathlib.Analysis.MeanInequalities

/-! # Mean square of a pair sum over primitive dyadic conjugates -/

namespace ProximityGap.DyadicChordEnergy
open Finset Polynomial
open scoped ComplexConjugate BigOperators

private noncomputable def oddEquiv {m : ℕ} {z : ℂ} (root : IsPrimitiveRoot z (2^(m+1))) :
    Fin (2^m) ≃ primitiveRoots (2^(m+1)) ℂ := by
  let f (i : Fin (2^m)) : primitiveRoots (2^(m+1)) ℂ := ⟨z^(2*i.val+1),by
    apply (mem_primitiveRoots (by positivity)).mpr
    apply root.pow_of_coprime
    apply Nat.Coprime.pow_right
    exact Nat.coprime_two_right.mpr ⟨i.val,by omega⟩⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  constructor
  · intro i j eq
    have ij := root.pow_inj (i:=2*i.val+1) (j:=2*j.val+1) (by rw [pow_succ];omega)
      (by rw [pow_succ];omega) (congrArg Subtype.val eq)
    exact Fin.ext (by omega)
  · simp only [Fintype.card_fin,Fintype.card_coe,root.card_primitiveRoots,Nat.totient_prime_pow_succ Nat.prime_two]
    omega

private theorem odd_pow_sum {h : ℕ} {R : ℂ} (rt : (R^2)^h=1) (different : R≠1) :
    (∑ i : Fin h,(R^(2*i.val+1)).re) ≤ 0 := by
  by_cases e : R^2=1
  · have neg := (sq_eq_one_iff.mp e).resolve_left different
    simp only [neg,show ∀ i : Fin h, (-1:ℂ)^(2*i.val+1)= -1 from fun i =>
      (show Odd (2*i.val+1) from ⟨i.val,rfl⟩).neg_one_pow,Complex.neg_re,Complex.one_re]
    simp
  · have g : ∑ i ∈ range h,(R^2)^i=0 :=
      (mul_eq_zero.mp ((geom_sum_mul (R^2) h).trans (sub_eq_zero.mpr rt))).resolve_right (sub_ne_zero.mpr e)
    have s : ∑ i : Fin h,R^(2*i.val+1)=0 := by
      simp only [show ∀ j : ℕ, R^(2*j+1)=(R^2)^j*R from fun j => by rw [pow_succ,pow_mul],
        ←sum_mul,Fin.sum_univ_eq_sum_range,g,zero_mul]
    exact le_of_eq (by simpa only [map_sum,Complex.reCLM_apply,Complex.zero_re]
      using (congrArg Complex.reCLM s))

/-- Distinct sites have conjugate-average squared pair-sum norm at most two.
The antipodal case has mean zero. Every other difference cancels exactly. -/
theorem pair_sum {m : ℕ} (a b : Fin (2^(m+1))) (distinct : a≠b) :
    (∑ w : primitiveRoots (2^(m+1)) ℂ, ‖(w:ℂ)^a.val+(w:ℂ)^b.val‖^2) ≤ 2*(2^m:ℕ) := by
  obtain ⟨z,root⟩ : ∃ z : ℂ, IsPrimitiveRoot z (2^(m+1)) :=
    ⟨_,Complex.isPrimitiveRoot_exp (2^(m+1)) (by positivity)⟩
  let H := 2^m
  let X := z^a.val
  let Y := z^b.val
  let R := X/Y
  have zn := root.norm'_eq_one (by positivity)
  have np : z≠0 := root.ne_zero (by positivity)
  have yn : Y≠0 := pow_ne_zero _ np
  have neq : R≠1 := fun eq => distinct (Fin.ext (root.pow_inj a.isLt b.isLt ((div_eq_one_iff_eq yn).mp eq)))
  have full (i : ℕ) : (z^i)^(2^(m+1))=1 := by
    rw [←pow_mul,Nat.mul_comm,pow_mul,root.pow_eq_one,one_pow]
  have rt : (R^2)^H=1 := by
    rw [←pow_mul,show 2*H=2^(m+1) by dsimp [H];rw [pow_succ];omega,div_pow,full,full,div_one]
  have cross := odd_pow_sum rt neq
  have eqi (i : Fin H) : ‖(z^(2*i.val+1))^a.val+(z^(2*i.val+1))^b.val‖^2 =
      2+2*(R^(2*i.val+1)).re := by
    have mor (j l : ℕ) : (z^j)^l=(z^l)^j := by rw [←pow_mul,Nat.mul_comm,pow_mul]
    rw [mor _ a.val,mor _ b.val,Complex.sq_norm,Complex.normSq_add,←Complex.sq_norm,←Complex.sq_norm]
    simp only [norm_pow,zn,one_pow]
    have unitY : ‖Y^(2*i.val+1)‖=1 := by simp [Y,norm_pow,zn]
    rw [show (z^b.val)^(2*i.val+1)=Y^(2*i.val+1) from rfl,←Complex.inv_eq_conj unitY]
    rw [show R^(2*i.val+1)=X^(2*i.val+1)/Y^(2*i.val+1) from div_pow ..]
    simp only [X,div_eq_mul_inv]
    ring
  rw [← (oddEquiv root).sum_comp]
  change (∑ i : Fin H, ‖(z^(2*i.val+1))^a.val+(z^(2*i.val+1))^b.val‖^2) ≤ _
  simp_rw [eqi]
  rw [sum_add_distrib,←mul_sum]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  change (H:ℝ)*2+2* _≤2*(H:ℝ)
  linarith

/-- Product form of AM–GM convenient for an integral resultant. -/
theorem prod_le_of_sum {J : Type*} [Fintype J] [Nonempty J] (f : J → ℝ) (hf : ∀ i,0≤f i)
    {C : ℝ} (bound : ∑ i,f i ≤ Fintype.card J*C) : ∏ i,f i ≤ C^Fintype.card J := by
  have pos : 0<(Fintype.card J:ℝ) := by exact_mod_cast Fintype.card_pos
  have g := Real.geom_mean_le_arith_mean (univ : Finset J) (fun _ => 1) f (fun _ _ => zero_le_one)
    (by simpa using pos) (fun i _ => hf i)
  simp only [Real.rpow_one,sum_const,card_univ,nsmul_eq_mul,mul_one,one_mul] at g
  have ac : (∏ i,f i)^((Fintype.card J:ℝ)⁻¹)≤C := g.trans ((div_le_iff₀ pos).mpr (by simpa [mul_comm] using bound))
  have out := Real.rpow_le_rpow (Real.rpow_nonneg (prod_nonneg (fun i _ => hf i)) _) ac pos.le
  simpa [←Real.rpow_mul (prod_nonneg (fun i _ => hf i)),pos.ne',Real.rpow_natCast] using out

end ProximityGap.DyadicChordEnergy
#print axioms ProximityGap.DyadicChordEnergy.pair_sum
