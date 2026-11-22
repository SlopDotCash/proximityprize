/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.JointMinorGram
import ArkLib.Research.ProximityGap.Frontier.DyadicMeanPairTransfer

/-! # Joint mean-square bound for three-row transposition minors -/

namespace ProximityGap.JointPairEnergy
open Finset DyadicMeanPairTransfer DyadicPairMinorTransfer
open ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm

private theorem pointwise {L : ℕ} (x y : Fin L → ℂ) (hx : ∀ i,‖x i‖=1) (hy : ∀ i,‖y i‖=1) :
    (∑ f : Fin 3 → Fin L, ‖form (x ∘ f) (y ∘ f)‖^2) ≤ 6*(L:ℝ)^2*∑ i,‖x i+y i‖^2 := by
  let M : Matrix (Fin L) (Fin 3) ℂ := fun i => ![1,x i+y i,x i*y i]
  have entry (f : Fin 3 → Fin L) : JointMinorGram.minor M f=form (x ∘ f) (y ∘ f) := by
    rw [JointMinorGram.minor,Matrix.det_fin_three];simp [Matrix.submatrix,M,form,minor];ring
  have h := JointMinorGram.total M
  simp_rw [entry] at h
  rw [Fin.prod_univ_three] at h
  have c₀ : (∑ j,‖M j 0‖^2)=(L:ℝ) := by
    change (∑ _j : Fin L,‖(1:ℂ)‖^2)=(L:ℝ)
    simp
  have c₂ : (∑ j,‖M j 2‖^2)=(L:ℝ) := by
    change (∑ j : Fin L,‖x j*y j‖^2)=(L:ℝ)
    simp [hx,hy]
  rw [c₀,c₂,show Fintype.card (Equiv.Perm (Fin 3))=6 by decide] at h
  change _ ≤ (6:ℕ)*(↑L*(∑ j,‖x j+y j‖^2)*↑L) at h
  exact h.trans_eq (by push_cast;ring)

/-- The joint energy of all ordered transposition minors is at most
12 L³ per primitive embedding on average. -/
theorem total {m L : ℕ} (q : Fin L × Fin 2 ↪ Fin (2^(m+1))) :
    (∑ w : primitiveRoots (2^(m+1)) ℂ, ∑ f : Fin 3 → Fin L,
      ‖valAt (cert (fun i => q (f i,0)) (fun i => q (f i,1))) w‖^2) ≤
      ((2^(m+1)).totient:ℝ)*(12*(L:ℝ)^3) := by
  let J := ↥(primitiveRoots (2^(m+1)) ℂ)
  let W (w : J) (i : Fin L) (j : Fin 2) := (w:ℂ)^(q (i,j)).val
  have pw (w : J) : (∑ f : Fin 3 → Fin L,‖valAt (cert (fun i => q (f i,0)) (fun i => q (f i,1))) w‖^2)
      ≤ 6*(L:ℝ)^2*∑ i,‖W w i 0+W w i 1‖^2 := by
    have unit := (isPrimitiveRoot_of_mem_primitiveRoots w.property).norm'_eq_one (by positivity)
    simpa only [valAt,eval_cert,Function.comp_def,W] using pointwise
      (fun i => W w i 0) (fun i => W w i 1) (fun i => by simp [W,norm_pow,unit])
      (fun i => by simp [W,norm_pow,unit])
  refine (sum_le_sum (fun w _ => pw w)).trans ?_
  rw [←mul_sum,sum_comm]
  have row (i : Fin L) : ∑ w : J,‖W w i 0+W w i 1‖^2≤2*(2^m:ℕ) :=
    DyadicChordEnergy.pair_sum _ _ (q.injective.ne (fun e => (by decide : (0:Fin 2)≠1) (congrArg Prod.snd e)))
  have bound := sum_le_sum (s:=univ) (fun i _ => row i)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at bound
  apply (mul_le_mul_of_nonneg_left bound (by positivity : 0≤6*(L:ℝ)^2)).trans
  rw [Nat.totient_prime_pow_succ Nat.prime_two]
  push_cast
  nlinarith

end ProximityGap.JointPairEnergy
#print axioms ProximityGap.JointPairEnergy.total
