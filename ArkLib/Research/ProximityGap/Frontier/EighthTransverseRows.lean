/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.EighthTransverseMobius
import Mathlib.LinearAlgebra.Lagrange

/-! # The four polynomial pairs for the second-prime transverse Möbius witness -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
namespace ArkLib.ProximityGap.Frontier.EighthTransverseRows
open Polynomial SecondPrimeSmoothSeed EighthTransverseMobius PrizeShapePrimeP30Second

local instance : Fact P.Prime := ⟨prime_P⟩

abbrev s : ℕ := 33554432
abbrev k : ℕ := 134217728

/-- The two nonzero quotient polynomials at a residue fiber. -/
def pv (j : Fin 32) : F := values (z ^ j.val) 1
def qv (j : Fin 32) : F := values (z ^ j.val) 2

local notation "d₁" => EighthTransverseMobius.slope

section
variable {K : Type*} [Field K]

private def lin (a b : K) : K[X] := C a * Polynomial.X + C b

private def polysA (L Q : K[X]) (a b : K) : Fin 4 → K[X] :=
  ![0, Polynomial.X * L, Polynomial.X * Q, L * lin a (-b)]

private def polysB (L Q : K[X]) (c d : K) : Fin 4 → K[X] := ![0, L, Q, L * lin d c]

@[simp] private def valsA (y p q a b : K) : Fin 4 → K := ![0, y*p, y*q, p*(a*y-b)]
@[simp] private def valsB (y p q c d : K) : Fin 4 → K := ![0, p, q, p*(c+d*y)]

private theorem lin_degree (a b : K) : (lin a b).natDegree ≤ 1 := by
  unfold lin
  exact natDegree_add_le_of_degree_le
    ((natDegree_C_mul_le a (Polynomial.X : K[X])).trans natDegree_X.le)
    ((natDegree_C b).le.trans (by decide))

private theorem degree_vector (L Q : K[X]) (a b c d : K) (i : Fin 4)
    (hL : L.natDegree ≤ 134217726) (hQ : Q.natDegree ≤ 134217726) :
    (polysA L Q a b i).degree < (k : WithBot ℕ) ∧
    (polysB L Q c d i).degree < (k : WithBot ℕ) := by
  have linear (R : K[X]) (h : R.natDegree ≤ 134217726) :
      ((Polynomial.X : K[X]) * R).natDegree ≤ 134217727 :=
    natDegree_mul_le.trans (add_le_add (natDegree_X (R := K)).le h)
  have pair (a b : K) : (L * lin a b).natDegree ≤ 134217727 :=
    natDegree_mul_le.trans (add_le_add hL (lin_degree a b))
  have small (f : K[X]) (h : f.natDegree ≤ 134217727) : f.degree < (k : WithBot ℕ) :=
    degree_le_natDegree.trans_lt (by exact_mod_cast (h.trans_lt (by decide : 134217727 < k)))
  fin_cases i
  · exact ⟨small 0 (by simp), small 0 (by simp)⟩
  · exact ⟨small _ (linear L hL), small _ (hL.trans (by decide))⟩
  · exact ⟨small _ (linear Q hQ), small _ (hQ.trans (by decide))⟩
  · exact ⟨small _ (pair a (-b)), small _ (pair d c)⟩

private theorem evaluated (L Q : K[X]) (y w p q a b c d : K) (i : Fin 4)
    (hL : L.eval y = w*p) (hQ : Q.eval y = w*q) :
    (polysA L Q a b i).eval y = w * valsA y p q a b i ∧
    (polysB L Q c d i).eval y = w * valsB y p q c d i := by
  fin_cases i <;> constructor <;> simp [polysA, polysB, valsA, valsB, lin, hL, hQ] <;> ring

end

private def head (J : F[X]) (i : Fin 3) := J * seed s i

/-- First row polynomials, with the leading terms in the fourth row canceled. -/
def rowA (J : F[X]) : Fin 4 → F[X] :=
  polysA (head J 1) (head J 2) (intercept + d₁ * (u+v)) (d₁*u*v)

/-- The second coordinate for each of the four polynomial pairs. -/
def rowB (J : F[X]) : Fin 4 → F[X] := polysB (head J 1) (head J 2) intercept d₁

/-- First-coordinate values after removing the common locator. -/
def aVal (x p q : F) : Fin 4 → F := valsA x p q (intercept+d₁*(u+v)) (d₁*u*v)

/-- Second-coordinate values after removing the common locator. -/
def bVal (x p q : F) : Fin 4 → F := valsB x p q intercept d₁

/-- All eight polynomials lie in the permitted degree range at rate one eighth. -/
theorem degrees (J : F[X]) (hj : J.natDegree = s-2) (i : Fin 4) :
    (rowA J i).degree < (k : WithBot ℕ) ∧ (rowB J i).degree < (k : WithBot ℕ) := by
  have hd (j : Fin 3) : (head J j).natDegree ≤ 134217726 :=
    natDegree_mul_le.trans ((add_le_add hj.le (SecondPrimeSmoothSeed.degree s j)).trans (by decide))
  exact degree_vector (head J 1) (head J 2) _ _ _ _ i (hd 1) (hd 2)

/-- Evaluate both rows at a physical site by indexing the 32 quotient values. -/
theorem evals (J : F[X]) (i : Fin 4) (x : Fin N) (j : Fin 32) (hj : j.val = x.val % 32) :
    (rowA J i).eval (dom x) = J.eval (dom x) * aVal (dom x) (pv j) (qv j) i ∧
    (rowB J i).eval (dom x) = J.eval (dom x) * bVal (dom x) (pv j) (qv j) i := by
  have ev (h : Fin 3) : (head J h).eval (dom x) = J.eval (dom x) * values (z ^ j.val) h := by
    rw [head, eval_mul, hj, eval_eighth_seed]
  exact evaluated (head J 1) (head J 2) (dom x) (J.eval (dom x)) (pv j) (qv j)
    _ _ _ _ i (ev 1) (ev 2)

/-- At a marked extra intersection the fourth row meets the third whenever
its prescribed quotient value is reached. -/
theorem marked_agreement {x p q : F} (hx : x = u ∨ x = v) (hq : (intercept+d₁*x)*p=q) :
    aVal x p q 3 = aVal x p q 2 ∧ bVal x p q 3 = bVal x p q 2 := by
  rcases hx with rfl | rfl <;> subst q <;> constructor <;> simp [aVal, bVal, valsA, valsB] <;> ring

/-- The three polynomial heads lie on the line of slope x, giving the folded label -x. -/
theorem line (x p q : F) (i : Fin 4) (hi : i.val < 3) :
    aVal x p q i + (-x) * bVal x p q i = 0 := by
  fin_cases i <;> simp_all [aVal, bVal, valsA, valsB]

/-- The fourth head and a triple head with normalized coefficient determined by its pole
have different second rows and coincide after folding at the stated Möbius label. -/
theorem cross {x p h : F} (hp : p ≠ 0) (hx : x ≠ h) :
    let a := aVal x p 0 3
    let b := bVal x p 0 3
    let f := p * (intercept+d₁*h)
    let scalar := ((h-u-v)*x+u*v)/(x-h)
    b ≠ f ∧ a + scalar*b = x*f + scalar*f := by
  dsimp [aVal, bVal, valsA, valsB]
  constructor
  · intro eq
    apply hx
    exact mul_left_cancel₀ marked.2.2.1 (add_left_cancel (mul_left_cancel₀ hp eq))
  · field_simp [sub_ne_zero.mpr hx]
    ring

#print axioms degrees
#print axioms evals
#print axioms cross
end ArkLib.ProximityGap.Frontier.EighthTransverseRows
