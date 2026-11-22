/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicPairMinorTransfer
import ArkLib.Research.ProximityGap.Frontier.DyadicSevenProjectivities

/-! # Recovering a trace-zero projectivity from disjoint transpositions -/

namespace ProximityGap.DyadicFourPairGeometry
open DyadicParityGalois DyadicPairMinorTransfer DyadicSevenDescent
variable {K : Type*} [Field K]

/-- The determinant of the canonical involution through two pairs is exactly
the product of their four cross-pair differences. -/
theorem det_pairs (u v x y : K) :
    (x*y-u*v)^2+((x+y-u-v)*u*v-(x*y-u*v)*(u+v))*(x+y-u-v)=
    (u-x)*(u-y)*(v-x)*(v-y) := by ring

/-- A trace-zero relation on three pairs forces their three-row minor to vanish. -/
theorem incident {a b c u v x y s t : K} (det : a^2+b*c≠0)
    (h₀ : c*u*v-a*(u+v)=b) (h₁ : c*x*y-a*(x+y)=b) (h₂ : c*s*t-a*(s+t)=b) :
    minor u v x y s t=0 := by
  by_cases nc : c=0
  · have na : a≠0 := by intro h;apply det;simp [nc,h]
    have s₁ : x+y-u-v=0 := by apply mul_left_cancel₀ na;rw [nc] at h₀ h₁;linear_combination h₀-h₁
    have s₂ : s+t-u-v=0 := by apply mul_left_cancel₀ na;rw [nc] at h₀ h₂;linear_combination h₀-h₂
    simp [minor,s₁,s₂]
  · apply mul_left_cancel₀ nc
    dsimp only [minor]
    linear_combination (x+y-u-v)*h₂-(s+t-u-v)*h₁+(s+t-x-y)*h₀

/-- If four disjoint pairs have vanishing three-row minors on a rigid grid,
the first two pairs have equal products or both are antipodal. -/
theorem pattern {n : ℕ} {w : K} (hw : IsPrimitiveRoot w n) (rigid : Rigid w)
    (q : Fin 4 × Fin 2 ↪ Fin n)
    (minors : ∀ i, minor (w^(q (0,0)).val) (w^(q (0,1)).val) (w^(q (1,0)).val)
      (w^(q (1,1)).val) (w^(q (i,0)).val) (w^(q (i,1)).val)=0) :
    w^(q (0,0)).val*w^(q (0,1)).val=w^(q (1,0)).val*w^(q (1,1)).val ∨
    (w^(q (0,0)).val+w^(q (0,1)).val=0 ∧ w^(q (1,0)).val+w^(q (1,1)).val=0) := by
  let X (i : Fin 4 × Fin 2) := w^(q i).val
  let u := X (0,0)
  let v := X (0,1)
  let x := X (1,0)
  let y := X (1,1)
  let a := x*y-u*v
  let c := x+y-u-v
  let b := c*u*v-a*(u+v)
  have ix : Function.Injective X := fun i j eq =>
    q.injective (Fin.ext (hw.pow_inj (q i).isLt (q j).isLt eq))
  have n (i j : Fin 4 × Fin 2) (ij : i≠j) := sub_ne_zero.mpr (ix.ne ij)
  have det : a^2+b*c≠0 := by
    dsimp only [a,b,c];rw [det_pairs]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (n _ _ (by decide)) (n _ _ (by decide)))
      (n _ _ (by decide))) (n _ _ (by decide))
  have mdet : a*(-a)≠b*c := fun eq => det (by linear_combination -eq)
  have law (i : Fin 4) : c*X (i,0)*X (i,1)-a*(X (i,0)+X (i,1))=b := by
    have h : minor u v x y (X (i,0)) (X (i,1))=0 := minors i
    dsimp only [minor] at h
    dsimp only [a,b,c]
    linear_combination h
  let f : Fin 7 ↪ Fin 4 × Fin 2 := ⟨![(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0)],by decide⟩
  let sw := Equiv.prodCongr (Equiv.refl (Fin 4)) (Equiv.swap (0:Fin 2) 1)
  have edges (i : Fin 4 × Fin 2) : Graph a b c (-a) (X i) (X (sw i)) := by
    rcases i with ⟨i,j⟩
    fin_cases j <;> simp [sw,Graph] <;> linear_combination -(law i)
  rcases rigid (fun i => (q (f i)).val) (fun i => (q (sw (f i))).val)
    (ix.comp f.injective) (ix.comp (sw.injective.comp f.injective)) a b c (-a) mdet
    (fun i => edges (f i)) with ⟨hb,hc⟩|⟨ha,_⟩
  · right
    have na : a≠0 := by intro ha;apply det;simp [ha,hc]
    have zero (i : Fin 4) : X (i,0)+X (i,1)=0 := by
      have eq := law i
      rw [hc,hb] at eq
      apply mul_left_cancel₀ na
      linear_combination -eq
    exact ⟨zero 0,zero 1⟩
  · exact .inl (sub_eq_zero.mp ha).symm

end ProximityGap.DyadicFourPairGeometry
#print axioms ProximityGap.DyadicFourPairGeometry.pattern
