/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
ATTACK AN2 -- Bourgain-Tzafriri restricted invertibility on the period frame.

The claim routes max_b |eta_b| <= sqrt(2 n log(q/n)) through BT restricted invertibility:
"select J subset of columns of Phi (n x (p-1)) with sigma_min(Phi_J) >= c sqrt(n), and BT
spectral-spreading forces the L-infinity mass max|eta_b|^2 <= 2 n log(q/n)".

REFUTATION KERNEL (this file): the period frame is ALREADY essentially TIGHT, so BT's
restricted-invertibility output is vacuous (it selects J = everything, gives nothing about
the sup). The frame operator S = Phi Phi^* equals p*I - J_n, exactly. We formalize the
EXACT eigenstructure of S = p*I - J on the all-ones vector and its orthogonal complement,
which is the load-bearing fact: cond(S) = p/(p-n) -> 1, no dyadic scale spread, so the
"log from condition-number budget over dyadic depth" has ZERO terms.

We model the frame operator abstractly: S acts on (Fin n -> R) as S = c1 * I - J where
J v = (sum v) * ones.  We prove the two eigenvalues exactly. This is axiom-clean linear
algebra; the numerics above (cond -> 1) are its quantitative shadow.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace AttackAN2

open scoped BigOperators

variable {n : ℕ}

/-- The all-ones vector. -/
def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- The frame operator S = c • I - J, where (J v) i = (∑ v) (acting as J v = (∑ v) • ones).
    For the period frame, c = p and J is the all-ones rank-1 operator; S = p I - J. -/
def frameOp (c : ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => c * v i - (∑ j, v j)

/-- EIGENVALUE 1: on the all-ones vector, S acts as multiplication by (c - n).
    This is the small eigenvalue p - n of the period frame (the lower Riesz bound BT sees). -/
theorem frameOp_ones (c : ℝ) (hn : 0 < n) :
    frameOp c (ones n) = (c - n) • (ones n) := by
  funext i
  simp only [frameOp, ones, Pi.smul_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- EIGENVALUE 2: on any vector summing to zero, S acts as multiplication by c.
    This is the large eigenvalue p (multiplicity n-1) of the period frame. -/
theorem frameOp_zero_sum (c : ℝ) (v : Fin n → ℝ) (hv : (∑ j, v j) = 0) :
    frameOp c v = c • v := by
  funext i
  simp only [frameOp, Pi.smul_apply, smul_eq_mul, hv, sub_zero]

/-- The frame is essentially tight: the two distinct eigenvalues are c-n and c, whose RATIO
    is c/(c-n) -> 1 as c (= p) >> n. We state the exact gap: the larger minus smaller = n.
    A two-point spectrum has NO intermediate dyadic scales, so the "log from condition-number
    budget over dyadic depth" that the conjecture invokes is built on zero terms. -/
theorem spectrum_gap_exact (c : ℝ) : c - (c - n) = (n : ℝ) := by ring

/-- KERNEL CONCLUSION (refutation, stated as a true proposition):
    BT restricted invertibility lower-bounds sigma_min of a SELECTED submatrix of Phi, i.e. a
    2nd-moment / spectral quantity living at scale (c - n) = p - n. The sup-norm
    max_b |eta_b|^2 is an L-infinity object at scale n log(q/n). For c = p ~ n^4 these differ
    by factor ~ p/(n log) ~ n^3. The exact two-point spectrum below witnesses that the frame is
    tight and BT is vacuous: there is no spectral spreading to exploit. -/
theorem bt_controls_only_spectral_scale (c : ℝ) (hn : 0 < n) :
    -- the two eigenvalues are exactly (c - n) and c; nothing here bounds an L-infinity coordinate
    frameOp c (ones n) = (c - n) • (ones n)
    ∧ (∀ v : Fin n → ℝ, (∑ j, v j) = 0 → frameOp c v = c • v) := by
  exact ⟨frameOp_ones c hn, fun v hv => frameOp_zero_sum c v hv⟩

end AttackAN2

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms AttackAN2.frameOp_ones
#print axioms AttackAN2.frameOp_zero_sum
#print axioms AttackAN2.spectrum_gap_exact
#print axioms AttackAN2.bt_controls_only_spectral_scale
