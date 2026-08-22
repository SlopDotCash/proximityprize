/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovNonVanishing

/-!
# LANE S1 (#466 round 21): Stepanov linear independence for the squarefree cubic

Step S1 of `CubicStepanovUpper` (`_R20StepanovScaffold.lean`): the auxiliary polynomial
`P = A₀(X, X^q) + f^((q−1)/2) · A₁(X, X^q)` built from a NONZERO low-degree coefficient
vector is a NONZERO polynomial, for `f = X(X−u)(X−v)` squarefree (`0, u, v` distinct).

## Discovery of this lane (honest provenance)

The hard core of S1 is NOT new: `StepanovNonVanishing.obstruction_forces_trivial` (in-tree,
axiom-clean, #232-era) already proves the general hyperelliptic non-vanishing by the
square-first + base-`q` faithfulness + integrally-closed argument, for ANY squarefree `g`
of positive degree — under a block-degree hypothesis `hblk` stated on the COMBINED squared
blocks `C g·A₀² − ĝ·A₁²`.  What was missing (and is proven here) is the cubic
specialization with hypotheses S2 can actually CHECK:

1. `cubic_squarefree` / `cubic_natDegree` — `f = X(X−u)(X−v)` is squarefree of degree 3
   exactly when `0, u, v` are distinct (the scaffold's standing hypothesis).  This is WHY
   Stepanov needs `u ≠ 0 ≠ v`, `u ≠ v`: squarefreeness is the entire independence input.
2. `blocks_mul_le` + the derivation `hblk` FROM per-block bounds: if every `X`-block of
   `A₀, A₁` has degree `≤ D` and `2D + 3 < q`, the combined squared blocks have degree
   `< q`.  This pins the classical Stepanov coefficient budget `D ≤ (q−4)/2` — the budget
   S2's dimension count must respect.
3. `cubic_stepanov_independence` — THE S1 STATEMENT: `A₀(X,X^q) + f^((q−1)/2)·A₁(X,X^q) = 0`
   with blocks `≤ D`, `2D + 3 < q`, `q` odd forces `A₀ = A₁ = 0`.
4. `cubic_aux_ne_zero` — the contrapositive packaging S2 consumes directly as the `hP ≠ 0`
   input of `hasseDeriv_stepanov_degree_count` / `stepanov_absurd`.
5. `natDegree_subq_le_blocks` + `cubic_aux_natDegree_le` — the degree budget
   `deg P ≤ q·J + 3(q−1)/2 + D` (`J` = Y-degree bound), the other half of the
   `m·N⁺ ≤ deg P` contradiction.
6. `one_and_cubic_pow_independent` — the `J = 0` textbook corollary: `1` and `f^((q−1)/2)`
   are linearly independent over polynomials of degree `≤ D` (`2D + 3 < q`).
7. `cubic_eval` — the evaluation bridge to the scaffold's char-sum shape
   `s(s−u)(s−v)`.

## What S1 does NOT do (honest scope)

No claim about `CubicStepanovUpper` itself: S2 (dimension-count existence of the coefficient
vector + Hasse-derivative Leibniz vanishing bookkeeping on the `N⁺` set) and S3 (assembling
the contradiction, small-`q` cases) remain open.  S1 is exactly the `P ≠ 0` + degree-budget
interface those steps consume.

Probe: `q = 13, 17` sympy check of non-vanishing at the budget boundary and the overflow
counterexample at `D ≥ 3(q−1)/2` (scratchpad `probe_r21_s1_independence.py`).

No closure claimed.
-/

namespace ArkLib.ProximityGap.Frontier.R21StepanovS1

open Polynomial ArkLib.ProximityGap.StepanovNonVanishing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The cubic and its squarefreeness (the independence input) -/

/-- The Stepanov cubic `f = X(X−u)(X−v)`, matching the scaffold family. -/
noncomputable def cubic (u v : F) : F[X] := X * ((X - C u) * (X - C v))

theorem cubic_def (u v : F) : cubic u v = X * ((X - C u) * (X - C v)) := rfl

/-- Evaluation bridge to the `_R20StepanovScaffold` char-sum shape. -/
theorem cubic_eval (u v s : F) : (cubic u v).eval s = s * ((s - u) * (s - v)) := by
  simp [cubic_def]

/-- `0, u, v` distinct ⟹ the cubic is squarefree (three distinct roots).  This is the
entire algebraic content behind Stepanov independence. -/
theorem cubic_squarefree {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Squarefree (cubic u v) := by
  have h0 : (0 : F) ∉ ({u, v} : Finset F) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hu h.symm
    · exact hv h.symm
  have h1 : u ∉ ({v} : Finset F) := by
    simp only [Finset.mem_singleton]; exact huv
  have hprod : (∏ a ∈ ({0, u, v} : Finset F), (X - C a)) = cubic u v := by
    rw [Finset.prod_insert h0, Finset.prod_insert h1, Finset.prod_singleton,
      C_0, sub_zero, cubic_def]
  rw [← hprod]
  exact (separable_prod_X_sub_C_iff'.mpr fun a _ b _ h => h).squarefree

theorem cubic_natDegree (u v : F) : (cubic u v).natDegree = 3 := by
  have h2 : ((X - C u) * (X - C v)).natDegree = 2 := by
    rw [natDegree_mul (X_sub_C_ne_zero u) (X_sub_C_ne_zero v),
      natDegree_X_sub_C, natDegree_X_sub_C]
  rw [cubic_def, natDegree_mul X_ne_zero
    (mul_ne_zero (X_sub_C_ne_zero u) (X_sub_C_ne_zero v)), natDegree_X, h2]

theorem cubic_ne_zero (u v : F) : cubic u v ≠ 0 := fun h => by
  have := cubic_natDegree u v; rw [h, natDegree_zero] at this; omega

/-! ## 2. Block-degree bookkeeping in `F[X][Y]` -/

/-- Blocks of a product are bounded by the sum of block bounds (Cauchy convolution). -/
theorem blocks_mul_le {A B : Polynomial (Polynomial F)} {DA DB : ℕ}
    (hA : ∀ j, (A.coeff j).natDegree ≤ DA) (hB : ∀ j, (B.coeff j).natDegree ≤ DB) :
    ∀ j, ((A * B).coeff j).natDegree ≤ DA + DB := by
  intro j
  rw [coeff_mul]
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact natDegree_mul_le.trans (add_le_add (hA _) (hB _))

/-- The combined squared-block degree hypothesis of `obstruction_forces_trivial`, derived
from per-block bounds: blocks `≤ D` and `2D + 3 < q` give combined blocks `< q`.  This is
the classical Stepanov coefficient budget `D ≤ (q−4)/2`. -/
theorem combined_blocks_lt {u v : F} {D q : ℕ} (hD : 2 * D + 3 < q)
    (A0 A1 : Polynomial (Polynomial F))
    (h0 : ∀ j, (A0.coeff j).natDegree ≤ D) (h1 : ∀ j, (A1.coeff j).natDegree ≤ D) :
    ∀ j, ((C (cubic u v) * A0 ^ 2 - ((cubic u v).map C) * A1 ^ 2).coeff j).natDegree < q := by
  intro j
  have hA0sq : ∀ j, ((A0 ^ 2).coeff j).natDegree ≤ D + D := by
    rw [sq]; exact blocks_mul_le h0 h0
  have hA1sq : ∀ j, ((A1 ^ 2).coeff j).natDegree ≤ D + D := by
    rw [sq]; exact blocks_mul_le h1 h1
  have hterm1 : ((C (cubic u v) * A0 ^ 2).coeff j).natDegree ≤ 3 + (D + D) := by
    rw [coeff_C_mul]
    exact natDegree_mul_le.trans
      (add_le_add (le_of_eq (cubic_natDegree u v)) (hA0sq j))
  have hmapblk : ∀ j, (((cubic u v).map (C : F →+* F[X])).coeff j).natDegree ≤ 0 := by
    intro j; rw [coeff_map]; exact le_of_eq (natDegree_C _)
  have hterm2 : ((((cubic u v).map C) * A1 ^ 2).coeff j).natDegree ≤ 0 + (D + D) :=
    blocks_mul_le hmapblk hA1sq j
  calc ((C (cubic u v) * A0 ^ 2 - ((cubic u v).map C) * A1 ^ 2).coeff j).natDegree
      = ((C (cubic u v) * A0 ^ 2).coeff j - (((cubic u v).map C) * A1 ^ 2).coeff j).natDegree := by
        rw [coeff_sub]
    _ ≤ max ((C (cubic u v) * A0 ^ 2).coeff j).natDegree
          ((((cubic u v).map C) * A1 ^ 2).coeff j).natDegree := natDegree_sub_le _ _
    _ < q := max_lt (by omega) (by omega)

/-! ## 3. THE S1 STATEMENT: Stepanov independence for the squarefree cubic -/

/-- **S1 (linear independence).**  For `q = |F|` odd, `0, u, v` distinct, coefficient blocks
of degree `≤ D` with `2D + 3 < q`: the auxiliary
`A₀(X, X^q) + f^((q−1)/2) · A₁(X, X^q)` vanishes only for `A₀ = A₁ = 0`.
Specializes `obstruction_forces_trivial` (square-first + base-`q` faithfulness +
integrally-closed) via `cubic_squarefree` and `combined_blocks_lt`. -/
theorem cubic_stepanov_independence
    (hq_odd : Odd (Fintype.card F))
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    {D : ℕ} (hD : 2 * D + 3 < Fintype.card F)
    (A0 A1 : Polynomial (Polynomial F))
    (h0 : ∀ j, (A0.coeff j).natDegree ≤ D) (h1 : ∀ j, (A1.coeff j).natDegree ≤ D)
    (hR : subq (Fintype.card F) A0
      + (cubic u v) ^ ((Fintype.card F - 1) / 2) * subq (Fintype.card F) A1 = 0) :
    A0 = 0 ∧ A1 = 0 :=
  obstruction_forces_trivial (cubic u v) (cubic_squarefree hu hv huv)
    (by rw [cubic_natDegree]; omega) hq_odd A0 A1
    (combined_blocks_lt hD A0 A1 h0 h1) hR

/-- **S1, contrapositive packaging** — the exact `P ≠ 0` input that
`hasseDeriv_stepanov_degree_count` / `stepanov_absurd` (S3) consume. -/
theorem cubic_aux_ne_zero
    (hq_odd : Odd (Fintype.card F))
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    {D : ℕ} (hD : 2 * D + 3 < Fintype.card F)
    (A0 A1 : Polynomial (Polynomial F))
    (h0 : ∀ j, (A0.coeff j).natDegree ≤ D) (h1 : ∀ j, (A1.coeff j).natDegree ≤ D)
    (hne : ¬(A0 = 0 ∧ A1 = 0)) :
    subq (Fintype.card F) A0
      + (cubic u v) ^ ((Fintype.card F - 1) / 2) * subq (Fintype.card F) A1 ≠ 0 :=
  fun h => hne (cubic_stepanov_independence hq_odd hu hv huv hD A0 A1 h0 h1 h)

/-! ## 4. The degree budget for the auxiliary (the other half of the contradiction) -/

/-- Sharpened `natDegree_subq_le`: with blocks `≤ D`, `deg A(X, X^q) ≤ q·deg_Y A + D`. -/
theorem natDegree_subq_le_blocks (q : ℕ) (A : Polynomial (Polynomial F)) {D : ℕ}
    (hblocks : ∀ j, (A.coeff j).natDegree ≤ D) :
    (subq q A).natDegree ≤ q * A.natDegree + D := by
  rw [subq_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply le_trans Polynomial.natDegree_mul_le
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  simp only [Finset.mem_range] at hj
  have h2 : q * j ≤ q * A.natDegree := Nat.mul_le_mul_left q (by omega)
  have := hblocks j
  omega

/-- **The auxiliary degree budget**: `deg P ≤ q·J + 3(q−1)/2 + D` for Y-degrees `≤ J` and
blocks `≤ D`.  Feeds the `m·N⁺ ≤ deg P` contradiction of
`hasseDeriv_stepanov_degree_count`. -/
theorem cubic_aux_natDegree_le (q : ℕ) {u v : F}
    {D J : ℕ} (A0 A1 : Polynomial (Polynomial F))
    (h0 : ∀ j, (A0.coeff j).natDegree ≤ D) (h1 : ∀ j, (A1.coeff j).natDegree ≤ D)
    (hJ0 : A0.natDegree ≤ J) (hJ1 : A1.natDegree ≤ J) :
    (subq q A0 + (cubic u v) ^ ((q - 1) / 2) * subq q A1).natDegree
      ≤ q * J + 3 * ((q - 1) / 2) + D := by
  apply le_trans (Polynomial.natDegree_add_le _ _)
  apply max_le
  · have := natDegree_subq_le_blocks q A0 h0
    have hm : q * A0.natDegree ≤ q * J := Nat.mul_le_mul_left q hJ0
    omega
  · apply le_trans Polynomial.natDegree_mul_le
    have hpow : ((cubic u v) ^ ((q - 1) / 2)).natDegree = 3 * ((q - 1) / 2) := by
      rw [Polynomial.natDegree_pow, cubic_natDegree, Nat.mul_comm]
    have := natDegree_subq_le_blocks q A1 h1
    have hm : q * A1.natDegree ≤ q * J := Nat.mul_le_mul_left q hJ1
    omega

/-! ## 5. The textbook `J = 0` corollary: `1, f^((q−1)/2)` independent over low degrees -/

/-- **Textbook independence**: `a + b·f^((q−1)/2) = 0` in `F[X]` with
`deg a, deg b ≤ D`, `2D + 3 < q` forces `a = b = 0`. -/
theorem one_and_cubic_pow_independent
    (hq_odd : Odd (Fintype.card F))
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    {D : ℕ} (hD : 2 * D + 3 < Fintype.card F)
    (a b : F[X]) (ha : a.natDegree ≤ D) (hb : b.natDegree ≤ D)
    (hrel : a + (cubic u v) ^ ((Fintype.card F - 1) / 2) * b = 0) :
    a = 0 ∧ b = 0 := by
  have hCa : ∀ j, ((Polynomial.C a : Polynomial (Polynomial F)).coeff j).natDegree ≤ D := by
    intro j
    rw [Polynomial.coeff_C]
    split_ifs
    · exact ha
    · simp
  have hCb : ∀ j, ((Polynomial.C b : Polynomial (Polynomial F)).coeff j).natDegree ≤ D := by
    intro j
    rw [Polynomial.coeff_C]
    split_ifs
    · exact hb
    · simp
  have hR : subq (Fintype.card F) (Polynomial.C a)
      + (cubic u v) ^ ((Fintype.card F - 1) / 2)
        * subq (Fintype.card F) (Polynomial.C b) = 0 := by
    rw [subq_C, subq_C]; exact hrel
  obtain ⟨h0, h1⟩ := cubic_stepanov_independence hq_odd hu hv huv hD
    (Polynomial.C a) (Polynomial.C b) hCa hCb hR
  constructor
  · have := congrArg (fun p => Polynomial.coeff p 0) h0
    simpa using this
  · have := congrArg (fun p => Polynomial.coeff p 0) h1
    simpa using this

end ArkLib.ProximityGap.Frontier.R21StepanovS1

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R21StepanovS1.cubic_eval
#print axioms ArkLib.ProximityGap.Frontier.R21StepanovS1.cubic_squarefree
#print axioms ArkLib.ProximityGap.Frontier.R21StepanovS1.cubic_natDegree
#print axioms ArkLib.ProximityGap.Frontier.R21StepanovS1.blocks_mul_le
#print axioms ArkLib.ProximityGap.Frontier.R21StepanovS1.combined_blocks_lt
#print axioms ArkLib.ProximityGap.Frontier.R21StepanovS1.cubic_stepanov_independence
#print axioms ArkLib.ProximityGap.Frontier.R21StepanovS1.cubic_aux_ne_zero
#print axioms ArkLib.ProximityGap.Frontier.R21StepanovS1.natDegree_subq_le_blocks
#print axioms ArkLib.ProximityGap.Frontier.R21StepanovS1.cubic_aux_natDegree_le
#print axioms ArkLib.ProximityGap.Frontier.R21StepanovS1.one_and_cubic_pow_independent
