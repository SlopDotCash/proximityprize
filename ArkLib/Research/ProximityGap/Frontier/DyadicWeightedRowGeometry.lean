/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicQuadraticRows
import ArkLib.Research.ProximityGap.Frontier.DyadicSevenProjectivities

/-! # The reflected and quadratic terms in the dyadic two-error penalty -/
namespace ProximityGap.DyadicWeightedRowGeometry
open DyadicParityGalois DyadicSevenDescent
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

/-- On a nonantipodal anchor row, at most six distinct tested sites can have a
positive-weight record produced by an antipodal transposition. -/
theorem reflected {m n : ℕ} {z : K} (hz : IsPrimitiveRoot z (2^m)) {s μ : K}
    (sn : s^2≠1) (s3 : s^3≠1) (mn : μ≠0)
    (A B : Fin n → ℕ) (ix : Function.Injective (fun i => z^(A i)))
    (iy : Function.Injective (fun i => z^(B i)))
    (record : ∀ i, (z^(A i)-1)*(z^(B i)-1)=μ*(z^(A i)-s^2)*(z^(B i)-s)) : n≤6 := by
  by_contra! large
  let f := Fin.castLEEmb (by omega : 7≤n)
  let a := s*μ-1
  let b := 1-s^3*μ
  let c := μ-1
  let d := 1-μ*s^2
  have sm : s-1≠0 := fun eq => sn (by rw [sub_eq_zero.mp eq];ring)
  have sp : s+1≠0 := fun eq => sn (by rw [eq_neg_of_add_eq_zero_left eq];ring)
  have det : a*d≠b*c := by
    rw [←sub_ne_zero,show a*d-b*c= -μ*(s-1)^2*(s+1) by dsimp [a,b,c,d];ring]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr mn) (pow_ne_zero _ sm)) sp
  have edges (i : Fin 7) : Graph a b c d (z^(A (f i))) (z^(B (f i))) := by
    dsimp only [Graph,a,b,c,d]
    linear_combination record (f i)
  rcases DyadicSevenProjectivities.all_orders hz (A ∘ f) (B ∘ f) (ix.comp f.injective)
    (iy.comp f.injective) a b c d det edges with ⟨b0,c0⟩|⟨a0,d0⟩
  · have mu : μ=1 := sub_eq_zero.mp c0
    apply s3
    dsimp only [b] at b0
    rw [mu,mul_one] at b0
    exact (sub_eq_zero.mp b0).symm
  · apply sm
    dsimp only [a] at a0
    dsimp only [d] at d0
    linear_combination -d0-s*a0

/-- The quadratic family of transpositions contributes at most ten tested
sites in one orientation of the anchor. The two indices at each tested site
are the other two distinct heads of the symmetric family. -/
theorem quadratic [Normal ℚ K] {m n : ℕ} {z : K} (hz : IsPrimitiveRoot z (2^m)) {s μ : K}
    (sn : s≠0) (ss : s≠1) (mn : μ≠0) (A : Fin n × Fin 2 → ℕ) (B : Fin n → ℕ)
    (ix : Function.Injective (fun i => z^(A i))) (iy : Function.Injective (fun i => z^(B i)))
    (sq : ∀ i, (z^(A i))^2≠s)
    (record : ∀ i, ((z^(A i))^2-s)*(z^(B i.1)-1)=
      s*μ*(z^(A i)-s)*(z^(A i)+1)*(z^(B i.1)-s)) : n≤10 := by
  let a := s^2*μ-1
  let b := s^2*μ*(1-s)
  let c := s*μ-1
  let d := s*μ*(1-s)
  have sm : 1-s≠0 := sub_ne_zero.mpr ss.symm
  have det : a*d≠b*c := by
    rw [←sub_ne_zero,show a*d-b*c= -(s*μ)*(1-s)^2 by dsimp [a,b,c,d];ring]
    exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero sn mn)) (pow_ne_zero _ sm)
  apply DyadicQuadraticRows.ten (a:=a) (b:=b) (c:=c) (d:=d) hz det
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ sn) mn) sm)
    (mul_ne_zero (mul_ne_zero sn mn) sm) A B ix iy sq
  intro i
  dsimp only [a,b,c,d]
  linear_combination record i

end ProximityGap.DyadicWeightedRowGeometry
#print axioms ProximityGap.DyadicWeightedRowGeometry.reflected
#print axioms ProximityGap.DyadicWeightedRowGeometry.quadratic
