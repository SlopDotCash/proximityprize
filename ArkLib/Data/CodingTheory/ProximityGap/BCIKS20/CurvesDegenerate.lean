/-
Copyright (c) 2026 William4711. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: William4711
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import Mathlib.FieldTheory.Finite.Basic

/-!
# Why the Johnson-regime curve theorem requires positive degree

`large_agreement_set_on_curve_implies_correlated_agreement'` proves Theorem 6.2 of [BCIKS20] for
positive Reed-Solomon degree, hence positive rate. For a stack of `l` words the bound asks for
more than `((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * ρ ^ (3 / 2)) * n ^ 2 * (l - 1)` close curve
points. At `deg = 0` the code is `{0}` and `ρ = 0`. Lean defines `x / 0 = 0`, so the threshold
becomes `0`, while `δ₀ 0 m = 1`. One close curve point would then satisfy the hypothesis.

Take one coordinate over `ZMod 3`, `u 0 = 0`, `u 1 = 1` and `δ = 0`. The curve point at `z = 0`
is `u 0 = 0`, a codeword. The conclusion asks for codewords `v` with `u i = v i` on at least one
coordinate for both `i`, but `v 1 = 0 ≠ 1 = u 1`.

`UnguardedJohnsonCurve` expresses the historical downstream statement without its positive-rate
guard, using the canonical close-parameter set. `not_unguardedJohnsonCurve` refutes that
statement.

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]
-/

open NNReal
open scoped LinearCode

namespace ProximityGap.CurvesDegenerate

/-- The historical Johnson-regime curve statement without the `0 < ρ` guard. -/
def UnguardedJohnsonCurve : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n] {l : ℕ} [Finite F]
    {m deg : ℕ} {domain : Fin n ↪ F} {δ : ℚ≥0},
    3 ≤ m →
    (δ : ℝ) ≤ δ₀ (ρ (ReedSolomon.code domain deg)) m →
    ∀ {u : Fin l → Fin n → F},
    ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) /
        (3 * (Real.rpow (ρ (ReedSolomon.code domain deg)) (3 / 2 : ℚ)))
      * n ^ 2 * (l - 1) <
      (coeffs_of_close_proximity_curve (F := F) (δ : ℝ≥0) u
        (ReedSolomon.toFinset domain deg)).card →
    ∃ v : Fin l → Fin n → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
        (1 - δ) * n ≤ ({ x : Fin n | ∀ i, u i x = v i x } : Finset _).card

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- One coordinate in `ZMod 3`. -/
def dom : Fin 1 ↪ ZMod 3 := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

lemma code_zero {w : Fin 1 → ZMod 3} (hw : w ∈ ReedSolomon.code dom 0) : w = 0 := by
  obtain ⟨y, hy, rfl⟩ := hw
  have : y = 0 := by simpa [Polynomial.mem_degreeLT] using hy
  subst this
  simp

/-- At `deg = 0` the rate is `0`, so the guard `0 < ρ` excludes this case. -/
lemma rate_zero_deg : ρ (ReedSolomon.code dom 0) = 0 := by
  simp [LinearCode.rate, LinearCode.dim]

/-- `u 0 = 0` and `u 1 = 1`. -/
def u : Fin 2 → Fin 1 → ZMod 3 := ![fun _ => 0, fun _ => 1]

/-- The curve point at `z = 0` is the codeword `0`, so `0` is a close parameter at `δ = 0`. -/
lemma zero_mem_close :
    (0 : ZMod 3) ∈ coeffs_of_close_proximity_curve (F := ZMod 3) (0 : ℝ≥0) u
      (ReedSolomon.toFinset dom 0) := by
  have heval : Curve.polynomialCurveEval (F := ZMod 3) (A := ZMod 3) u 0 = 0 := by
    funext x
    simp [Curve.polynomialCurveEval, Fin.sum_univ_two, u]
  simp only [coeffs_of_close_proximity_curve, Set.mem_toFinset, Set.mem_ofPred_eq, heval,
    ReedSolomon.toFinset, ReedSolomon.RScodeSet, Set.coe_toFinset]
  have h := Code.relDistFromCode_le_relDist_to_mem (0 : Fin 1 → ZMod 3)
    (C := (ReedSolomon.code dom 0 : Set (Fin 1 → ZMod 3))) 0 (Submodule.zero_mem _)
  exact h.trans (by simp [Code.relHammingDist, ← ENNReal.coe_nnratCast])

/-- The unguarded statement is false: it is refuted at `deg = 0`. -/
theorem not_unguardedJohnsonCurve : ¬ UnguardedJohnsonCurve := by
  intro hax
  have hρ := rate_zero_deg
  have hpos : 0 < (coeffs_of_close_proximity_curve (F := ZMod 3) (0 : ℝ≥0) u
      (ReedSolomon.toFinset dom 0)).card :=
    Finset.card_pos.mpr ⟨0, zero_mem_close⟩
  obtain ⟨v, hv, hagree⟩ := hax (F := ZMod 3) (n := 1) (l := 2) (m := 3) (deg := 0)
    (domain := dom) (δ := 0) (by norm_num) (by rw [hρ]; simp [δ₀]) (u := u) (by
      rw [hρ]
      have hrpow : Real.rpow ((0 : ℚ≥0) : ℝ) ((3 / 2 : ℚ) : ℝ) = 0 := by
        rw [NNRat.cast_zero]
        exact Real.zero_rpow (by norm_num)
      rw [hrpow, mul_zero, div_zero, zero_mul, zero_mul]
      exact_mod_cast hpos)
  have h1 : v 1 = 0 := code_zero (hv 1)
  have hempty : ({ x : Fin 1 | ∀ i, u i x = v i x } : Finset (Fin 1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    have := (Finset.mem_filter.mp hx).2 1
    rw [h1] at this
    simp [u] at this
  rw [hempty] at hagree
  norm_num at hagree

end ProximityGap.CurvesDegenerate

#print axioms ProximityGap.CurvesDegenerate.not_unguardedJohnsonCurve
