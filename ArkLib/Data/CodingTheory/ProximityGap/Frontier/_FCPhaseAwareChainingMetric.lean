/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Phase-aware chaining metric: the sqrt n validity defect of the L2-embedding metric (#444, FC angle)

Generic chaining bounds `sup_c eta_c` by the Dudley entropy integral with respect to the canonical
metric `d_X(c,c') = ||X_c - X_c'||_2`. The #1 defect for the Gaussian-period family
`eta_b = sum_{x in mu_n} e_p(b x)` is that the L2-embedding metric `||psi_c - psi_c'||_2`
(psi_c : Fin n -> R the n coordinates summed to form eta_c = sum psi_c) is phase-blind (Parseval).

## Proven content

`eta_c = <psi_c, 1>` is the all-ones contraction. For chaining to UPPER-bound the process a valid
majorant `d` needs `|eta_c - eta_c'| <= d(c,c')`. The L2-embedding metric is a factor sqrt n TOO
SMALL:  `(eta_c - eta_c')^2 <= n * ||psi_c - psi_c'||_2^2`  (etaDiff_sq_le), and this is TIGHT in the
constant/antipodal direction (etaDiff_sq_eq_of_const). So scaling `||.||_2` to a valid majorant costs
the full sqrt n, recovering the union bound (l2_embedding_subcanonical).

## Numeric witness (python3, n=16, p=65537 Fermat, exact)

Worst pair (eta_max, eta_min) = (13.838, -12.570), true increment 26.408, L2-embedding distance
6.731, underestimate factor 3.92 ~ sqrt n = 4.000 (Cauchy-Schwarz saturated). Dudley integral under
||.||_2 is 11.9 < M = 13.838 (an INVALID bound, underestimates the max); under canonical d_diff it is
26.3 > 16.3 = union bound. No metric in this class escapes.

## Verdict: REDUCES-TO-WALL

The sqrt n gap between the union bound and the prize target is EXACTLY the Cauchy-Schwarz defect n of
the all-ones contraction. Any metric closing it must be sub-canonical: it would have to know, per
conjugate, that psi_c - psi_c' is NOT aligned with 1 (the n signed coordinates cancel) = the missing
per-conjugate sub-Gaussian right-tail (E_r <= Wick to depth r* ~ log p) = the wall. This file proves
the defect axiom-clean; it does NOT close the prize.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.FCPhaseAwareChainingMetric

open Finset

variable {n : ℕ}

/-- The all-ones contraction `eta(psi) := sum psi`, the value functional whose max over conjugates is
the house `M`. -/
def eta (ψ : Fin n → ℝ) : ℝ := ∑ i, ψ i

/-- The Cauchy-Schwarz validity defect: the squared increment of `eta` is bounded by `n` times the
squared L2-embedding distance. This is why the (phase-blind) L2-embedding metric is sqrt n too small
to be a valid chaining majorant. -/
theorem etaDiff_sq_le (ψ ψ' : Fin n → ℝ) :
    (eta ψ - eta ψ') ^ 2 ≤ (n : ℝ) * ∑ i, (ψ i - ψ' i) ^ 2 := by
  have h : eta ψ - eta ψ' = ∑ i, (ψ i - ψ' i) := by
    simp only [eta, ← Finset.sum_sub_distrib]
  rw [h]
  have key := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => ψ i - ψ' i)
  simpa [Finset.card_univ] using key

/-- Tightness: when `psi - psi'` is the constant `t` in every coordinate (the antipodal direction),
the Cauchy-Schwarz bound is an EQUALITY `(n t)^2 = n * (n t^2)`. The factor `n` (sqrt n in the
metric) is therefore not improvable. -/
theorem etaDiff_sq_eq_of_const (t : ℝ) (ψ ψ' : Fin n → ℝ)
    (hconst : ∀ i, ψ i - ψ' i = t) :
    (eta ψ - eta ψ') ^ 2 = (n : ℝ) * ∑ i, (ψ i - ψ' i) ^ 2 := by
  have hdiff : eta ψ - eta ψ' = ∑ i, (ψ i - ψ' i) := by
    simp only [eta, ← Finset.sum_sub_distrib]
  have hsum : (∑ i, (ψ i - ψ' i)) = (n : ℝ) * t := by
    simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsq : (∑ i, (ψ i - ψ' i) ^ 2) = (n : ℝ) * t ^ 2 := by
    simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hdiff, hsum, hsq]; ring

/-- The L2-embedding metric is sub-canonical: `|eta psi - eta psi'| <= sqrt n * ||psi - psi'||_2`,
and (by etaDiff_sq_eq_of_const) this is sharp. The smallest scalar making `K * ||.||_2` a valid
increment-majorant is `K = sqrt n`, inflating the Dudley integral by sqrt n back to the union bound.
-/
theorem l2_embedding_subcanonical (ψ ψ' : Fin n → ℝ) :
    |eta ψ - eta ψ'| ≤ Real.sqrt (n : ℝ) * Real.sqrt (∑ i, (ψ i - ψ' i) ^ 2) := by
  have hle := etaDiff_sq_le ψ ψ'
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have habs : |eta ψ - eta ψ'| = Real.sqrt ((eta ψ - eta ψ') ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [habs, ← Real.sqrt_mul hn_nonneg]
  exact Real.sqrt_le_sqrt hle

end ArkLib.ProximityGap.Frontier.FCPhaseAwareChainingMetric

#print axioms ArkLib.ProximityGap.Frontier.FCPhaseAwareChainingMetric.etaDiff_sq_le
#print axioms ArkLib.ProximityGap.Frontier.FCPhaseAwareChainingMetric.etaDiff_sq_eq_of_const
#print axioms ArkLib.ProximityGap.Frontier.FCPhaseAwareChainingMetric.l2_embedding_subcanonical
