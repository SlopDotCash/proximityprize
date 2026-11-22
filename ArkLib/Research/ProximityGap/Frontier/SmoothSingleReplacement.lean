/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ProjectivePairPadding
import ArkLib.Research.ProximityGap.Frontier.DenseMobiusRigidity

/-! # One replacement changes the dimension-three smooth threshold -/

namespace ProximityGap.SmoothSingleReplacement
open Finset Polynomial ProjectivePairCompletions DimensionThreeInvolution MCAThresholdLedger
open scoped NNReal ENNReal
variable {F : Type} [Field F] [DecidableEq F]

/-- An n-point multiplicative coset, n≥9, ceases to be projectively paired
after any single replacement, in characteristic zero or greater than n+2. -/
theorem loses_symmetry {n : ℕ} (large : 9≤n)
    (units : ∀ i : ℕ, 0 < i → i ≤ n+2 → (i:F)≠0)
    {α : F} (nz : α≠0) (H : Finset F) (size : H.card=n) (roots : ∀ z∈H, z^n=α)
    (o y : F) (outside : y∉H) : ¬PairedSet (insert y (H.erase o)) := by
  classical
  rintro ⟨a,b,c,valid,given⟩
  let S := insert y (H.erase o)
  let f := fun z : F => -(b*z+c)/(a*z+b)
  have pair {i j : F} (eq : a*i*j+b*(i+j)+c=0) : f i=j := by
    have den : a*i+b≠0 := by intro zero;exact valid (by linear_combination a*eq-(a*j+b)*zero)
    exact (div_eq_iff den).mpr (by linear_combination -eq)
  have orbit {i : F} (hi : i∈S) : f i∈S ∧ f i≠i ∧ f (f i)=i ∧ a*i*(f i)+b*(i+f i)+c=0 := by
    obtain ⟨j,hj,ij,rel⟩ := given i hi
    rw [pair rel]
    exact ⟨hj,ij.symm,pair (by linear_combination rel),rel⟩
  have hy : y∈S := mem_insert_self ..
  have fy := orbit hy
  have fyH := (mem_erase.mp ((mem_insert.mp fy.1).resolve_left fy.2.1)).2
  let T : Finset F := {o,f y}
  have hT : T.card≤2 := (card_insert_le ..).trans (by simp)
  have good {z : F} (hz : z∈H) (keep : z∉T) : f z∈H ∧ a*z*(f z)+b*(z+f z)+c=0 := by
    have diff : z≠o ∧ z≠f y := by simpa [T] using keep
    have hS : z∈S := mem_insert_of_mem (mem_erase.mpr ⟨diff.1,hz⟩)
    have zorb := orbit hS
    have nY : f z≠y := fun eq => diff.2 (zorb.2.2.1.symm.trans (congrArg f eq))
    exact ⟨(mem_erase.mp ((mem_insert.mp zorb.1).resolve_left nY)).2,zorb.2.2.2⟩
  have dihedral := DenseMobiusRigidity.rigid (r:=2) (by omega : 3*2+2<n) units nz
    (a:=-b) (b:=-c) (c:=a) (d:=b) (by intro eq;exact valid (by linear_combination eq)) H T
    size hT roots (by
      intro z hz keep
      obtain ⟨fz,rel⟩ := good hz keep
      rw [show -b*z+ -c=f z*(a*z+b) by linear_combination -rel,mul_pow,roots _ fz])
  obtain ⟨u,hu,ok⟩ := exists_mem_notMem_of_card_lt_card (s:=T) (t:=H) (by omega)
  obtain ⟨hu',ur⟩ := good hu ok
  have yr := fy.2.2.2
  have ypow : y^n=α := by
    rcases dihedral with ⟨c0,a0⟩|⟨b0,_⟩
    · have cZ := neg_eq_zero.mp c0
      rw [a0,cZ] at ur yr valid
      have nb : b≠0 := by intro z;simp [z] at valid
      have eu : u+f u=0 := (mul_eq_zero.mp (by simpa using ur : b*(u+f u)=0)).resolve_left nb
      have ey : y+f y=0 := (mul_eq_zero.mp (by simpa using yr : b*(y+f y)=0)).resolve_left nb
      have cross : y*f u=f y*u := by linear_combination f u*ey-f y*eu
      have e := congrArg (·^n) cross
      simpa [mul_pow,roots u hu,roots _ hu',roots _ fyH,nz] using e
    · have bZ := neg_eq_zero.mp b0
      rw [bZ] at ur yr valid
      have na : a≠0 := by intro z;simp [z] at valid
      have cross : y*f y=u*f u := by
        apply mul_left_cancel₀ na
        linear_combination yr-ur
      have e := congrArg (·^n) cross
      simpa [mul_pow,roots u hu,roots _ hu',roots _ fyH,nz] using e
  have cap := Polynomial.card_eval_zero_le_natDegree (insert y H) id Function.injective_id.injOn
    ((Polynomial.X:F[X])^n-Polynomial.C α) (Polynomial.X_pow_sub_C_ne_zero (by omega : 0<n) α)
  rw [filter_eq_self.mpr (by
    intro z hz
    rcases mem_insert.mp hz with rfl|present
    · simp [ypow]
    · simp [roots _ present]),card_insert_of_notMem outside,size,natDegree_X_pow_sub_C] at cap
  omega

private theorem smooth_fiber [Fintype F] {n : ℕ} [NeZero n] (D : Fin n ↪ F)
    [ReedSolomon.Smooth D] (large : 2≤n) : ∃ α : F, α≠0 ∧ ∀ z∈univ.image D, z^n=α := by
  classical
  obtain ⟨V,size,on,_,_⟩ := CodingTheory.AdditiveSetListDecoding.Smooth.exists_pow_projection_structure
    D (by simp : Fintype.card (Fin n)=n*1)
  obtain ⟨α,eq⟩ := card_eq_one.mp size
  have power (z : F) (hz : z∈univ.image D) : z^n=α := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp hz
    simpa [eq] using on i
  refine ⟨α,?_,power⟩
  intro zero
  have all : univ.image D⊆{0} := by
    intro z hz
    have e := power z hz
    rw [zero] at e
    simpa using (eq_zero_of_pow_eq_zero e)
  have cap := card_le_card all
  rw [card_image_of_injective _ D.injective,card_univ,Fintype.card_fin,card_singleton] at cap
  omega

/-- Every one-site replacement in an even smooth domain changes the first
failing count from h−1 to h at budget h, for all interleaving widths. -/
theorem thresholds [Fintype F] {n h Q : ℕ} [NeZero n] (D E : Fin n ↪ F) [ReedSolomon.Smooth E]
    (length : n=2*h+2) (large : 4≤h) (odd : h%2=1)
    (units : ∀ i : ℕ, 0 < i → i ≤ n+2 → (i:F)≠0) (o y : F) (outside : y∉univ.image E)
    (edit : univ.image D=insert y ((univ.image E).erase o))
    (positive : 0<Q) (budget : Fintype.card F/Q=h) (width : ℕ) [NeZero width] :
    ∀ δ : ℝ≥0,
      (epsMCA (F:=F) ((ReedSolomon.code E 3 : Set (Fin n → F)) ^⋈ (Fin width)) δ≤1/(Q:ℝ≥0∞) ↔
        δ<((h-1:ℕ):ℝ≥0)/n) ∧
      (epsMCA (F:=F) ((ReedSolomon.code D 3 : Set (Fin n → F)) ^⋈ (Fin width)) δ≤1/(Q:ℝ≥0∞) ↔
        δ<(h:ℝ≥0)/n) := by
  classical
  have base := (reflects_iff E).2 (ProjectivePairPadding.smooth_paired E (by omega))
  obtain ⟨α,nz,root⟩ := smooth_fiber E (by omega)
  have wrong : ¬ Reflects D := by
    intro yes
    exact loses_symmetry (by omega : 9≤n) units nz (univ.image E) (by rw [card_image_of_injective _ E.injective,card_univ,Fintype.card_fin]) root o y outside
      (edit ▸ (reflects_iff D).1 yes)
  intro δ
  have a := (classification E length large odd positive budget width).2 δ
  have b := (classification D length large odd positive budget width).2 δ
  simpa only [ite_eq_left base,ite_eq_right wrong] using And.intro a b

end ProximityGap.SmoothSingleReplacement
#print axioms ProximityGap.SmoothSingleReplacement.loses_symmetry
#print axioms ProximityGap.SmoothSingleReplacement.thresholds
