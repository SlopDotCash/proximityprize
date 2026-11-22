/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicParityGalois

/-! # Field of definition from three marked points and antipodal normalization -/

namespace ProximityGap.DyadicProjectiveDescent
open DyadicParityGalois
variable {K L : Type*} [Field K] [Field L]

/-- Any projectivity matching three points of the ground field to three
points of that field has a ground-field matrix for its entire graph in any
extension. This also handles projectivities given with transcendental complex
coefficients before normalizing them on three cyclotomic matches. -/
theorem field_of_three (φ : K →+* L) (x y : Fin 3 ↪ K) {a b c d : L}
    (det : a*d≠b*c) (pins : ∀ i, Graph a b c d (φ (x i)) (φ (y i))) :
    ∃ A B C D : K, A*D≠B*C ∧ ∀ s t : L,
      Graph a b c d s t ↔ Graph (φ A) (φ B) (φ C) (φ D) s t := by
  let U := (x 1-x 2)*(y 1-y 0)
  let V := (x 1-x 0)*(y 1-y 2)
  let A := U*y 2-V*y 0
  let B := -x 0*U*y 2+x 2*V*y 0
  let C := U-V
  let D := -x 0*U+x 2*V
  have xu (i j : Fin 3) (ij : i≠j) := sub_ne_zero.mpr (x.injective.ne ij)
  have yu (i j : Fin 3) (ij : i≠j) := sub_ne_zero.mpr (y.injective.ne ij)
  have nU : U≠0 := mul_ne_zero (xu 1 2 (by decide)) (yu 1 0 (by decide))
  have nV : V≠0 := mul_ne_zero (xu 1 0 (by decide)) (yu 1 2 (by decide))
  have good : A*D≠B*C := by
    rw [←sub_ne_zero,show A*D-B*C=U*V*(x 2-x 0)*(y 2-y 0) by dsimp [A,B,C,D];ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero nU nV) (xu 2 0 (by decide))) (yu 2 0 (by decide))
  have given (i : Fin 3) : Graph A B C D (x i) (y i) := by
    fin_cases i <;> dsimp [Graph,A,B,C,D,U,V] <;> ring
  let X : Fin 3 ↪ L := ⟨φ ∘ x,φ.injective.comp x.injective⟩
  refine ⟨A,B,C,D,good,?_⟩
  have imageDet : φ A*φ D≠φ B*φ C := fun e => good (φ.injective (by simpa only [map_mul] using e))
  apply three det imageDet X (φ ∘ y) pins
  intro i
  simpa only [X,Function.comp_apply,Function.Embedding.coeFn_mk,map_mul,map_add,Graph]
    using congrArg φ (given i)

/-- Two opposite matches give the coefficient identities controlling the
unique target dilation which interchanges those two input sites. -/
theorem antipodal_equations [CharZero K] {a b c d u v : K}
    (first : Graph a b c d u v) (second : Graph a b c d (-u) (-v)) :
    a*u=v*d ∧ b=c*u*v := by
  dsimp only [Graph] at first second
  constructor
  · apply mul_left_cancel₀ (by norm_num : (2:K)≠0)
    linear_combination first-second
  · apply mul_left_cancel₀ (by norm_num : (2:K)≠0)
    linear_combination first+second

/-- Rescaling the target by −u/v turns an antipodal match u↦v, −u↦−v
into the specific conic Bxy+x+y+B u²=0. Its two normalized coefficients
satisfy B≠0 and B²u²≠1 for every non-dihedral nonsingular map. -/
theorem normalize_antipodal [CharZero K] {a b c d u v : K} (det : a*d≠b*c)
    (other : ¬((b=0 ∧ c=0) ∨ (a=0 ∧ d=0))) (nu : u≠0) (nv : v≠0)
    (first : Graph a b c d u v) (second : Graph a b c d (-u) (-v)) :
    ∃ B : K, B≠0 ∧ B^2*u^2≠1 ∧ ∀ x y, Graph a b c d x y →
      B*x*((-u/v)*y)+x+(-u/v)*y+B*u^2=0 := by
  obtain ⟨au,bc⟩ := antipodal_equations first second
  have nc : c≠0 := fun hc => other (Or.inl ⟨by simp [hc] at bc;exact bc,hc⟩)
  have nd : d≠0 := by
    intro hd
    have zero : a*u=0 := by simpa [hd] using au
    exact other (Or.inr ⟨(mul_eq_zero.mp zero).resolve_right nu,hd⟩)
  refine ⟨c/d,div_ne_zero nc nd,?_,?_⟩
  · intro singular
    field_simp [nd] at singular
    apply det
    apply mul_left_cancel₀ nu
    linear_combination d*au - (c*u)*bc - v*singular
  · intro x y e
    dsimp only [Graph] at e
    field_simp [nd,nv]
    linear_combination u*e - x*au - u*bc

/-- If both opposite sites are anti-invariant, the target rotation and the
squared source site in the normalized conic are invariant. -/
theorem fixed_normalization (σ : K ≃+* K) {u v : K} (hu : σ u= -u) (hv : σ v= -v) :
    σ (-u/v)= -u/v ∧ σ (u^2)=u^2 := by simp [hu,hv,div_neg,neg_div]

end ProximityGap.DyadicProjectiveDescent
#print axioms ProximityGap.DyadicProjectiveDescent.field_of_three
#print axioms ProximityGap.DyadicProjectiveDescent.normalize_antipodal
