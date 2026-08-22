/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The Bessel sub-Gaussian bound for `μ_{2^μ}` energy (#389 prize, core inequality)

The proven analytic heart of the Bessel reduction
(`docs/kb/deltastar-bessel-energy-reduction-2026-06-13.md`): the exact
additive energy `E_r^∞(μ_{2^μ}) = (2r)!·Σ_{m:Fin d→ℕ, Σm=r} ∏ 1/(mᵢ!)²` is
`≤ (2r−1)!!·n^r = (2r)!·Σ_{Σm=r} ∏ 1/mᵢ!`, term-by-term, because
`∏ 1/(mᵢ!)² ≤ ∏ 1/mᵢ!` (each factor `1/mᵢ! ≤ 1`).  This is the coefficientwise
`I₀(2x) ≤ e^{x²}` bound that makes the clean-moments Gaussian baseline a
THEOREM (not an assumption) for the exact `p=∞` energy.

`energy_term_le` — the term-by-term factor bound;
`bessel_energy_le_gaussian` — the summed inequality (the energy `≤` clean).
Stated coefficient-level (`ℚ`-valued multinomial sums) so it is self-contained;
the energy/walk identity is probe-verified (`probe_prize_bessel.py`, n=8→168).
-/

open Finset BigOperators

namespace ProximityGap.PrizeWorkbench

/-- The Bessel coefficient `[x^{2r}] I₀(2x)^d` as a `ℚ`-multinomial sum. -/
noncomputable def besselCoeff (d r : ℕ) : ℚ :=
  ∑ m ∈ Finset.Nat.antidiagonalTuple d r,
    ∏ i, (1 : ℚ) / (Nat.factorial (m i))^2

/-- The Gaussian coefficient `[x^{2r}] e^{d x²} = d^r/r!` as the matching
`ℚ`-multinomial sum `Σ ∏ 1/mᵢ!`. -/
noncomputable def gaussianCoeff (d r : ℕ) : ℚ :=
  ∑ m ∈ Finset.Nat.antidiagonalTuple d r,
    ∏ i, (1 : ℚ) / (Nat.factorial (m i))

/-- **Term-by-term factor bound**: `∏ 1/(mᵢ!)² ≤ ∏ 1/mᵢ!` (each `1/mᵢ! ≤ 1`). -/
theorem energy_term_le {d : ℕ} (m : Fin d → ℕ) :
    ∏ i, (1 : ℚ) / (Nat.factorial (m i))^2 ≤ ∏ i, (1 : ℚ) / (Nat.factorial (m i)) := by
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    have hpos : (0 : ℚ) < (Nat.factorial (m i) : ℚ) := by
      exact_mod_cast Nat.factorial_pos _
    have hfac : (1 : ℚ) ≤ (Nat.factorial (m i) : ℚ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hle1 : (1 : ℚ) / (Nat.factorial (m i)) ≤ 1 := by
      rw [div_le_one hpos]; exact hfac
    have hnn : (0 : ℚ) ≤ (1 : ℚ) / (Nat.factorial (m i)) := by positivity
    calc (1 : ℚ) / (Nat.factorial (m i))^2
        = (1 / (Nat.factorial (m i))) * (1 / (Nat.factorial (m i))) := by
          rw [pow_two]; ring
      _ ≤ (1 / (Nat.factorial (m i))) * 1 := by
          exact mul_le_mul_of_nonneg_left hle1 hnn
      _ = 1 / (Nat.factorial (m i)) := mul_one _

/-- **The Bessel sub-Gaussian bound**: the exact-energy coefficient is at most
the Gaussian coefficient — `[x^{2r}]I₀(2x)^d ≤ [x^{2r}]e^{dx²} = d^r/r!`.
Multiplying by `(2r)!` gives `E_r^∞(μ_{2^μ}) ≤ (2r−1)!!·n^r` (the clean
baseline), proven unconditionally for every `d = n/2` and `r`. -/
theorem bessel_energy_le_gaussian (d r : ℕ) :
    besselCoeff d r ≤ gaussianCoeff d r := by
  unfold besselCoeff gaussianCoeff
  apply Finset.sum_le_sum
  intro m _
  exact energy_term_le m

end ProximityGap.PrizeWorkbench

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PrizeWorkbench.energy_term_le
#print axioms ProximityGap.PrizeWorkbench.bessel_energy_le_gaussian
