/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicRationalSites

/-! # A quadratic rational row with two preimages per tested value

The numerator and denominator are linear combinations of X²−s and X.
Removing at most two exceptional outputs leaves a nonexceptional match at
each of the two input sites for every remaining output.
-/
namespace ProximityGap.DyadicQuadraticRows
open Polynomial Finset DyadicRationalParity
variable {K : Type*} [Field K] [CharZero K]

private noncomputable def row (s a b : K) : K[X] := C a * (X^2-C s)+C b*X

private theorem degree (s a b : K) : (row s a b).natDegree≤2 := by
  unfold row
  compute_degree!

@[simp] private theorem at_site (s a b t : K) : (row s a b).eval t=a*(t^2-s)+b*t := by
  simp [row]

private theorem clean {s a b c d t y : K} (det : a*d≠b*c) (nz : t≠0) (sq : t^2≠s)
    (law : a*(t^2-s)+b*t=y*(c*(t^2-s)+d*t)) (good : c*d*y^2≠a*b) :
    Clean (row s a b) (row s c d) t y := by
  simp only [Clean,at_site,neg_sq]
  refine ⟨?_,law,?_,?_⟩
  · intro h
    apply det
    apply mul_right_cancel₀ nz
    linear_combination (a-c*y)*h-c*law
  · intro h
    have hard : (a-y*c)*(t^2-s)=0 := by linear_combination (law+h)/2
    have aa := sub_eq_zero.mp ((mul_eq_zero.mp hard).resolve_right (sub_ne_zero.mpr sq))
    have bb : b=y*d := by apply mul_right_cancel₀ nz; linear_combination (law-h)/2
    exact det (by rw [aa,bb]; ring)
  · intro h
    apply good
    apply mul_right_cancel₀ nz
    linear_combination -(y*c)*(law+h)/2-a*(law-h)/2

/-- On any dyadic grid, at most ten distinct nonzero outputs can each have
two distinct admitted input sites for the displayed quadratic row. -/
theorem ten [Algebra ℚ K] [Normal ℚ K] {m n : ℕ} {z : K} (hz : IsPrimitiveRoot z (2^m))
    {s a b c d : K} (det : a*d≠b*c) (bn : b≠0) (dn : d≠0)
    (A : Fin n × Fin 2 → ℕ) (B : Fin n → ℕ) (ix : Function.Injective (fun i => z^(A i)))
    (iy : Function.Injective (fun i => z^(B i)))
    (sq : ∀ i, (z^(A i))^2≠s)
    (law : ∀ i, a*((z^(A i))^2-s)+b*z^(A i)=z^(B i.1)*(c*((z^(A i))^2-s)+d*z^(A i))) :
    n≤10 := by
  classical
  let y (i : Fin n) := z^(B i)
  let bad := univ.filter fun i => c*d*(y i)^2=a*b
  let H : K[X] := C (c*d)*X^2-C (a*b)
  have nh : H≠0 := by
    intro eq
    have ab : a*b=0 := by simpa [H] using congrArg (eval 0) eq
    have cd : c*d=0 := by simpa [H,ab] using congrArg (eval 1) eq
    have cz := (mul_eq_zero.mp cd).resolve_right dn
    have az := (mul_eq_zero.mp ab).resolve_right bn
    exact det (by simp [az,cz])
  have bad_size : bad.card≤2 := by
    apply le_trans _ (show H.natDegree≤2 by dsimp [H];compute_degree!)
    apply DyadicRationalSites.zeros nh y iy
    intro i hi
    simpa [H,sub_eq_zero] using (show c*d*(y i)^2=a*b from (mem_filter.mp hi).2)
  let good := univ \ bad
  have rest := card_sdiff_add_card_eq_card (t:=univ) (s:=bad) (subset_univ _)
  change good.card+bad.card=_ at rest
  simp only [card_univ,Fintype.card_fin] at rest
  by_contra! too_many
  obtain ⟨f,mem⟩ := DyadicSevenCombinatorics.select good 9 (by omega)
  let pair : Fin 18 ≃ Fin 9 × Fin 2 := (finProdFinEquiv (m:=9) (n:=2)).symm
  let sel : Fin 18 ↪ Fin n × Fin 2 := ⟨fun i => (f (pair i).1,(pair i).2),by
    intro i j eq
    apply pair.injective
    exact Prod.ext (f.injective (congrArg Prod.fst eq)) (congrArg (fun t : Fin n × Fin 2 => t.2) eq)⟩
  have no (i : Fin 18) : c*d*(y (sel i).1)^2≠a*b := by
    change c*d*(y (f (pair i).1))^2≠a*b
    have ok : f (pair i).1∉bad := (mem_sdiff.mp (mem (pair i).1)).2
    simpa only [bad,mem_filter,mem_univ,true_and] using ok
  have h := DyadicRationalParity.bound (by decide : 0<2) hz (row s a b) (row s c d)
    (degree ..) (degree ..) (A ∘ sel) (fun i => B (sel i).1) (ix.comp sel.injective)
    (fun i => clean det (pow_ne_zero _ (hz.ne_zero (by positivity))) (sq _) (law _) (no i))
  omega

end ProximityGap.DyadicQuadraticRows
#print axioms ProximityGap.DyadicQuadraticRows.ten
