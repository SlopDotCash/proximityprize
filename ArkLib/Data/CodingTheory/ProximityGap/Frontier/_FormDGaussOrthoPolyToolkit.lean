/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Scratch: char-0 Hermite recurrence `b_k² = n·k` from the Wick moments (#444, form D)
-/

set_option autoImplicit false


namespace ProximityGap.Frontier.HermiteRecurrence

open Polynomial

noncomputable section

variable (n : ℝ)

/-- The **Wick / Gaussian moment sequence** for `N(0,n)`:
`m(2k) = (2k-1)‼ · n^k`, `m(2k+1) = 0`.  The proven char-0 period moments. -/
def wickMoment : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | (r + 2) => n * (r + 1) * wickMoment r

/-- The **Wick recursion** `m(r+2) = n·(r+1)·m(r)` (definitional). -/
theorem wickMoment_succ_succ (r : ℕ) :
    wickMoment n (r + 2) = n * (r + 1) * wickMoment n r := rfl

/-- The **Wick / Gaussian moment linear functional** `L : ℝ[X] →ₗ[ℝ] ℝ`,
`L(∑ c_r X^r) = ∑ c_r · m(r)`.  This is the (deterministic) expectation against `N(0,n)`. -/
def momentFunctional : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := p.sum (fun r c => c * wickMoment n r)
  map_add' p q := by
    classical
    rw [Polynomial.sum_add_index]
    · intro i; simp
    · intro i a b; ring
  map_smul' a p := by
    classical
    show (a • p).sum (fun r c => c * wickMoment n r)
        = a * p.sum (fun r c => c * wickMoment n r)
    rw [Polynomial.sum_smul_index' p a (fun r c => c * wickMoment n r) (by intro i; simp)]
    simp only [smul_eq_mul, Polynomial.sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring

@[simp] theorem momentFunctional_monomial (r : ℕ) (c : ℝ) :
    momentFunctional n (Polynomial.monomial r c) = c * wickMoment n r := by
  simp only [momentFunctional, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Polynomial.sum_monomial_index]
  simp

@[simp] theorem momentFunctional_X_pow (r : ℕ) :
    momentFunctional n (X ^ r) = wickMoment n r := by
  have : (X ^ r : ℝ[X]) = Polynomial.monomial r 1 := by
    rw [Polynomial.X_pow_eq_monomial]
  rw [this, momentFunctional_monomial]; ring

@[simp] theorem momentFunctional_C (c : ℝ) :
    momentFunctional n (C c) = c := by
  have : (C c : ℝ[X]) = Polynomial.monomial 0 c := (Polynomial.monomial_zero_left c).symm
  rw [this, momentFunctional_monomial]; simp [wickMoment]

/-- The **moment shift** `m(r+1) = n·r·m(r-1)`: the half-step Wick recursion that powers
Gaussian integration by parts. (For `r = 0` both sides are `0`.) -/
theorem wickMoment_shift (r : ℕ) :
    wickMoment n (r + 1) = n * r * wickMoment n (r - 1) := by
  cases r with
  | zero => simp [wickMoment]
  | succ s =>
      have : s + 1 + 1 = s + 2 := by ring
      rw [this, wickMoment_succ_succ]
      push_cast
      ring_nf

/-- `L(C c · q) = c · L(q)` (the functional is `C`-linear). -/
theorem momentFunctional_C_mul (c : ℝ) (q : ℝ[X]) :
    momentFunctional n (C c * q) = c * momentFunctional n q := by
  rw [← Polynomial.smul_eq_C_mul, map_smul]; rfl

/-- `L(C c · X^s) = c · m(s)`. -/
@[simp] theorem momentFunctional_C_mul_X_pow (c : ℝ) (s : ℕ) :
    momentFunctional n (C c * X ^ s) = c * wickMoment n s := by
  rw [momentFunctional_C_mul, momentFunctional_X_pow]

/-- **The Gaussian / Stein integration-by-parts identity on monomials:**
`L(X · X^r) = n · L((X^r)')`.  This is `E[X·f(X)] = n·E[f'(X)]` for `X ~ N(0,n)`, the
single identity that drives the whole orthogonal-polynomial theory. -/
theorem momentFunctional_stein_pow (r : ℕ) :
    momentFunctional n (X * X ^ r) = n * momentFunctional n (derivative (X ^ r)) := by
  rw [Polynomial.derivative_X_pow, momentFunctional_C_mul_X_pow,
      show X * X ^ r = (X : ℝ[X]) ^ (r + 1) by ring, momentFunctional_X_pow,
      wickMoment_shift]
  ring

/-- **The general Gaussian / Stein integration-by-parts identity:** for every polynomial `p`,
`L(X · p) = n · L(p')`.  (`E[X·p(X)] = n·E[p'(X)]` for `X ~ N(0,n)`.)  Proven by linearity
from the monomial case. -/
theorem momentFunctional_stein (p : ℝ[X]) :
    momentFunctional n (X * p) = n * momentFunctional n (derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [mul_add, map_add, hp, hq, derivative_add, map_add]; ring
  | monomial s c =>
      have hmono : (Polynomial.monomial s c : ℝ[X]) = C c * X ^ s := by
        rw [← Polynomial.smul_eq_C_mul, Polynomial.smul_X_eq_monomial]
      rw [hmono]
      rw [show (X : ℝ[X]) * (C c * X ^ s) = C c * (X * X ^ s) by ring,
          momentFunctional_C_mul, momentFunctional_stein_pow,
          derivative_C_mul, momentFunctional_C_mul]
      ring

/-! ## The monic Gaussian orthogonal polynomials and their recurrence -/

/-- The **monic Gaussian (scaled-Hermite) orthogonal polynomials** for `N(0,n)`, defined by the
three-term recurrence
`π₀ = 1`, `π₁ = X`, `π_{k+2} = X·π_{k+1} − n·(k+1)·π_k`.
These are `n^{k/2}·He_k(x/√n)` — the monic OPs for the Wick moment functional `L`. -/
def gaussOP : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | (k + 2) => X * gaussOP (k + 1) - C (n * (k + 1)) * gaussOP k

@[simp] theorem gaussOP_zero : gaussOP n 0 = 1 := rfl
@[simp] theorem gaussOP_one : gaussOP n 1 = X := rfl
theorem gaussOP_succ_succ (k : ℕ) :
    gaussOP n (k + 2) = X * gaussOP n (k + 1) - C (n * (k + 1)) * gaussOP n k := rfl

/-- The off-diagonal recurrence coefficient `b_{k+1}² := n·(k+1)` read off the recurrence
`π_{k+2} = X·π_{k+1} − b_{k+1}²·π_k`. This is the Jacobi matrix's squared off-diagonal. -/
def recCoeffSq (k : ℕ) : ℝ := n * (k + 1)

/-- **The Hermite derivative ladder** `π_{k+1}' = (k+1)·π_k`.  (`He_k' = k·He_{k-1}` scaled.)
The structural identity that, with Stein, drives orthogonality. -/
theorem derivative_gaussOP (k : ℕ) :
    derivative (gaussOP n (k + 1)) = (k + 1 : ℝ) • gaussOP n k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [gaussOP]
  | one =>
      -- π₂' = 2·π₁ :  (X² − C n)' = 2X
      rw [show (1 : ℕ) + 1 = 2 from rfl, gaussOP_succ_succ]
      simp only [gaussOP_one, gaussOP_zero, Nat.cast_zero, zero_add, mul_one]
      rw [derivative_sub, derivative_mul, Polynomial.derivative_X, one_mul, mul_one,
          Polynomial.derivative_C, sub_zero]
      push_cast; module
  | more j ih1 ih2 =>
      -- P j : π_{j+1}' = (j+1)π_j;  P (j+1) : π_{j+2}' = (j+2)π_{j+1};  prove P (j+2).
      rw [show j + 2 + 1 = (j + 1) + 2 from rfl, gaussOP_succ_succ,
          derivative_sub, derivative_mul, Polynomial.derivative_X, one_mul,
          ih2, derivative_C_mul, ih1]
      -- now use the recurrence X·π_{j+1} = π_{j+2} + C(n(j+1))·π_j
      have hrec : (X : ℝ[X]) * gaussOP n (j + 1)
          = gaussOP n (j + 2) + C (n * ((j:ℝ) + 1)) * gaussOP n j := by
        rw [gaussOP_succ_succ]; ring
      have hidx : j + 1 + 1 = j + 2 := rfl
      rw [hidx] at *
      simp only [smul_eq_C_mul]
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, map_mul, map_add, map_one,
        map_ofNat] at hrec ⊢
      -- Use hrec to eliminate X * gaussOP n (j+1)
      linear_combination (C ((j:ℝ)) + 2) * hrec

/-- `π_k` is **monic of degree `k`** (so it is genuinely the `k`-th monic OP, and `b_k` is
genuinely the off-diagonal of the associated Jacobi matrix). -/
theorem gaussOP_monic (k : ℕ) : (gaussOP n k).Monic ∧ (gaussOP n k).natDegree = k := by
  induction k using Nat.twoStepInduction with
  | zero => exact ⟨monic_one, by simp [gaussOP]⟩
  | one => exact ⟨monic_X, by simp [gaussOP]⟩
  | more j ih1 ih2 =>
      obtain ⟨hm1, hd1⟩ := ih1
      obtain ⟨hm2, hd2⟩ := ih2
      rw [show j + 2 = (j + 1) + 1 from rfl, gaussOP_succ_succ]
      -- `X·π_{j+1}` is monic of degree `j+2`; the subtracted term has natDegree ≤ j.
      have hXmonic : (X * gaussOP n (j + 1)).Monic := monic_X.mul hm2
      have hXdeg : (X * gaussOP n (j + 1)).natDegree = j + 1 + 1 := by
        rw [Polynomial.natDegree_mul (Polynomial.X_ne_zero) hm2.ne_zero,
            Polynomial.natDegree_X, hd2]; omega
      have hsubdeg : (C (n * ((j : ℝ) + 1)) * gaussOP n j).natDegree ≤ j :=
        (Polynomial.natDegree_C_mul_le _ _).trans (le_of_eq hd1)
      have hdeglt : (C (n * ((j : ℝ) + 1)) * gaussOP n j).degree
          < (X * gaussOP n (j + 1)).degree := by
        rw [Polynomial.degree_eq_natDegree hXmonic.ne_zero, hXdeg]
        calc (C (n * ((j : ℝ) + 1)) * gaussOP n j).degree
            ≤ (j : WithBot ℕ) := Polynomial.degree_le_of_natDegree_le hsubdeg
          _ < ((j + 1 + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : j < j + 1 + 1)
      refine ⟨hXmonic.sub_of_left hdeglt, ?_⟩
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rw [hXdeg]; omega), hXdeg]

/-! ## The master lowering identity and orthogonality -/

/-- **The master lowering identity** `L(π_{k+1}·q) = n·L(π_k·q')`, valid for every `k` and every
polynomial `q`.  Proof: Stein on `X·π_k·q` plus the derivative ladder `π_k' = k·π_{k-1}` exactly
cancels the recurrence's `−n·k·π_{k-1}` term.  This single identity lowers degree against the
weight, and gives orthogonality and the diagonal norms in one stroke. -/
theorem momentFunctional_lower (k : ℕ) (q : ℝ[X]) :
    momentFunctional n (gaussOP n (k + 1) * q)
      = n * momentFunctional n (gaussOP n k * derivative q) := by
  cases k with
  | zero =>
      -- π₁ = X, π₀ = 1:  L(X·q) = n·L(q') = n·L(1·q')
      simp only [gaussOP_zero, one_mul, Nat.zero_add]
      rw [show gaussOP n (0 + 1) = X from rfl]
      exact momentFunctional_stein n q
  | succ j =>
      -- L(π_{j+2}·q): expand recurrence, Stein on X·π_{j+1}·q, ladder π_{j+1}'=(j+1)π_j.
      rw [gaussOP_succ_succ, sub_mul, map_sub, mul_assoc (X : ℝ[X])]
      -- Stein:  L(X·(π_{j+1}·q)) = n·L((π_{j+1}·q)')
      have hstein : momentFunctional n (X * (gaussOP n (j + 1) * q))
          = n * momentFunctional n (derivative (gaussOP n (j + 1) * q)) :=
        momentFunctional_stein n (gaussOP n (j + 1) * q)
      rw [hstein, derivative_mul, derivative_gaussOP, map_add]
      -- first inner term:  L(((j+1)•π_j)·q) = (j+1)·L(π_j·q)
      rw [show ((j : ℝ) + 1) • gaussOP n j * q = C ((j : ℝ) + 1) * (gaussOP n j * q) by
            rw [smul_eq_C_mul]; ring,
          momentFunctional_C_mul]
      -- second (recurrence) term:  L(C(n(j+1))·π_j·q) = n(j+1)·L(π_j·q)
      rw [show C (n * ((j : ℝ) + 1)) * gaussOP n j * q
            = C (n * ((j : ℝ) + 1)) * (gaussOP n j * q) by ring,
          momentFunctional_C_mul]
      -- now everything is in terms of L(π_j·q) and L(π_{j+1}·q'); ring closes
      ring

/-- **Iterated lowering** `L(π_k · q) = n^k · L(q^{(k)})` for every `k` and `q`.  The whole
weight is converted into `k` derivatives on the test polynomial. -/
theorem momentFunctional_iterate_lower (k : ℕ) (q : ℝ[X]) :
    momentFunctional n (gaussOP n k * q) = n ^ k * momentFunctional n (derivative^[k] q) := by
  induction k generalizing q with
  | zero => simp
  | succ j ih =>
      rw [momentFunctional_lower, ih (derivative q),
          ← Function.iterate_succ_apply derivative j q, pow_succ]
      ring

/-- **The Hermite derivative count** `π_k^{(k)} = k!` (the `k`-th derivative of the monic
degree-`k` Gaussian OP is the constant `k!`).  Follows from iterating the ladder
`π_k' = k·π_{k-1}`. -/
theorem iterate_derivative_gaussOP_self (k : ℕ) :
    derivative^[k] (gaussOP n k) = C (k.factorial : ℝ) := by
  induction k with
  | zero => simp [gaussOP]
  | succ j ih =>
      rw [Function.iterate_succ_apply, derivative_gaussOP]
      rw [show derivative^[j] ((j + 1 : ℝ) • gaussOP n j)
            = (j + 1 : ℝ) • derivative^[j] (gaussOP n j) from
            Polynomial.iterate_derivative_smul _ _ _]
      rw [ih, Nat.factorial_succ, smul_eq_C_mul, ← map_mul]
      push_cast
      ring_nf

/-! ## Orthogonality, the diagonal Hankel norm, and the recurrence coefficient `b_k² = n·k` -/

/-- **The diagonal Hankel norm** `h_k := L(π_k²) = n^k · k!`.
This is the squared `L²(N(0,n))`-norm of the monic Gaussian OP `π_k`, and it is the
quantity whose successive ratios are the squared recurrence coefficients. -/
theorem momentFunctional_gaussOP_sq (k : ℕ) :
    momentFunctional n (gaussOP n k * gaussOP n k) = n ^ k * (k.factorial : ℝ) := by
  rw [momentFunctional_iterate_lower, iterate_derivative_gaussOP_self, momentFunctional_C]

/-- **Orthogonality (degree form):** if `deg q < k`, then `L(π_k · q) = 0`.
The Gaussian OPs are orthogonal to every lower-degree polynomial w.r.t. the Wick functional. -/
theorem momentFunctional_gaussOP_orthogonal {k : ℕ} {q : ℝ[X]} (hq : q.natDegree < k) :
    momentFunctional n (gaussOP n k * q) = 0 := by
  rw [momentFunctional_iterate_lower, Polynomial.iterate_derivative_eq_zero hq, map_zero,
      mul_zero]

/-- **The diagonal norm is positive** for `n > 0` (so the ratio defining `b_k²` is well posed). -/
theorem momentFunctional_gaussOP_sq_pos (hn : 0 < n) (k : ℕ) :
    0 < momentFunctional n (gaussOP n k * gaussOP n k) := by
  rw [momentFunctional_gaussOP_sq]
  positivity

/-- **★ THE CHAR-0 HERMITE RECURRENCE `b_k² = n·k` (derived, not assumed). ★**
The squared off-diagonal Jacobi coefficient of the empirical Gaussian period measure is the
ratio of successive diagonal Hankel norms:
`b_{k}² = h_k / h_{k-1} = (n^{k+1}·(k+1)!) / (n^k·k!) = n·(k+1)`.
Stated as: `h_{k+1} = n·(k+1) · h_k`, i.e. `b_{k+1}² = n·(k+1)` — the Hermite law `b_k²=n·k`,
*proven from the Wick moments* via the Hankel/recurrence map, not put in by hand.  This closes the
char-0 half of Form (D). -/
theorem hermite_recurrence_bSq (k : ℕ) :
    momentFunctional n (gaussOP n (k + 1) * gaussOP n (k + 1))
      = (n * (k + 1)) * momentFunctional n (gaussOP n k * gaussOP n k) := by
  rw [momentFunctional_gaussOP_sq, momentFunctional_gaussOP_sq, Nat.factorial_succ]
  push_cast
  ring

/-- **The recurrence coefficient read off as the norm ratio equals `recCoeffSq k = n·(k+1)`.**
For `n > 0`, dividing the diagonal-norm identity gives `h_{k+1}/h_k = n·(k+1) = recCoeffSq n k`,
i.e. the off-diagonal of the Jacobi matrix squared is exactly `n·(k+1)` (Hermite `b_k²=n·k`). -/
theorem hermite_recCoeffSq_eq (hn : 0 < n) (k : ℕ) :
    momentFunctional n (gaussOP n (k + 1) * gaussOP n (k + 1))
      / momentFunctional n (gaussOP n k * gaussOP n k) = recCoeffSq n k := by
  rw [hermite_recurrence_bSq, mul_div_assoc,
      div_self (ne_of_gt (momentFunctional_gaussOP_sq_pos n hn k)), mul_one, recCoeffSq]

/-- **Concrete check `b₁² = n`** (the first off-diagonal: `h₁/h₀ = n·1·0!⁻¹·... = n`). -/
theorem hermite_bSq_one (hn : 0 < n) :
    momentFunctional n (gaussOP n 1 * gaussOP n 1)
      / momentFunctional n (gaussOP n 0 * gaussOP n 0) = n := by
  rw [hermite_recCoeffSq_eq n hn 0]; simp [recCoeffSq]

/-- **Concrete check `b₂² = 2n`.** -/
theorem hermite_bSq_two (hn : 0 < n) :
    momentFunctional n (gaussOP n 2 * gaussOP n 2)
      / momentFunctional n (gaussOP n 1 * gaussOP n 1) = 2 * n := by
  rw [hermite_recCoeffSq_eq n hn 1]; rw [recCoeffSq]; push_cast; ring

end

end ProximityGap.Frontier.HermiteRecurrence

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ProximityGap.Frontier.HermiteRecurrence

#print axioms momentFunctional_stein
#print axioms gaussOP_monic
#print axioms derivative_gaussOP
#print axioms momentFunctional_lower
#print axioms momentFunctional_iterate_lower
#print axioms iterate_derivative_gaussOP_self
#print axioms momentFunctional_gaussOP_sq
#print axioms momentFunctional_gaussOP_orthogonal
#print axioms hermite_recurrence_bSq
#print axioms hermite_recCoeffSq_eq
#print axioms hermite_bSq_one
#print axioms hermite_bSq_two
