/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Attack #08: the Chernoff/MGF route to `M` needs the energy at ALL orders (#464)

Large-deviation lever for the per-frequency bound `M = max_{b≠0}‖η_b‖`.  A Chernoff bound on the
random variable `Z := ‖η_b‖²` (over `b` uniform, `b ≠ 0`) reads, for any `t > 0`,

  `P(Z ≥ s) ≤ exp(-t·s) · E[exp(t·Z)]`,   `E[exp(t·Z)] = ∑_{r≥0} (tʳ / r!) · E_r`,

where `E_r = (1/(q-1)) ∑_{b≠0} ‖η_b‖^{2r}` is the `r`-th DC-subtracted energy moment.  The hope of
this angle: the period is sub-Gaussian-LEANING (`κ₄ < 0`, kurtosis `3 − 3/n`), so maybe the MGF is
controlled by a sub-Gaussian envelope `E[exp(tZ)] ≤ exp(t·μ + C·t²·σ²)` to depth `log p`, giving a
genuine tail `M ≲ √(n log m)` without the full energy.

## The obstruction this file records (axiom-clean)

The MGF is a power series whose coefficients ARE the energy moments `E_r` at EVERY order `r`.  A
sub-Gaussian envelope to a tail at level `s ≈ n log m` requires the saddle order `r* ≈ s/μ ≈ log m`,
so the MGF must be controlled UP TO order `r* ≈ log m`.  But that is exactly the energy bound at
depth `r ≈ log m` — the open core (BGK/Paley).  The negative 4th cumulant only fixes the `r = 2`
term; it does not, by itself, control the partial sums at order `log m`, and the deep cumulants are
sign-unstable (`_DoorIVEighthCumulantSignUnstable`: the 8th connected cumulant takes both signs
across admissible prize primes), so no fixed-sign sub-Gaussian envelope propagates.

We record the structural fact: **the Chernoff bound is monotone in EVERY energy moment** — raising
any single `E_r` (even at the deepest order) cannot lower the MGF, hence cannot tighten the tail.
So the large-deviation route cannot avoid pinning `E_r` to depth `r ≈ log m`; it is the moment
method in exponential dress, and inherits the same `r > log_n q` validity wall.

This is a NO-GO for the route (it does not bound `M`), in the project's `*_REFUTED`-style spirit.
Axiom target `[propext, Classical.choice, Quot.sound]`.  Issue #464.
-/

namespace ArkLib.ProximityGap.Frontier.Attack08CumulantMGFAllOrders

open scoped BigOperators

set_option linter.style.longLine false

/-- A truncated MGF / exponential-moment partial sum built from energy moments `E : ℕ → ℝ`:
`Φ_N(t) = ∑_{r<N} (tʳ/r!)·E r`.  This is the object a Chernoff bound exponentiates. -/
noncomputable def truncMGF (E : ℕ → ℝ) (t : ℝ) (N : ℕ) : ℝ :=
  ∑ r ∈ Finset.range N, (t ^ r / r.factorial) * E r

/-- **Monotone in every coefficient.** If two energy profiles satisfy `E r ≤ E' r` at every order
and `t ≥ 0`, the truncated MGF is monotone: `Φ_N(E,t) ≤ Φ_N(E',t)`.  Hence a Chernoff/large-deviation
bound, which is increasing in the MGF, can only be *tightened* by LOWERING some `E_r` — there is no
order one may drop.  In particular the deep moments `r ≈ log m` enter on equal footing with `r = 2`,
so a sub-Gaussian fix at `r = 2` (the `κ₄ < 0` lever) cannot substitute for control at depth. -/
theorem truncMGF_mono {E E' : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hE : ∀ r, E r ≤ E' r) (N : ℕ) :
    truncMGF E t N ≤ truncMGF E' t N := by
  unfold truncMGF
  apply Finset.sum_le_sum
  intro r _
  have hcoef : (0 : ℝ) ≤ t ^ r / r.factorial := by positivity
  exact mul_le_mul_of_nonneg_left (hE r) hcoef

/-- **The saddle order is `log`-deep.** For a sub-Gaussian tail at level `s` of a variable with mean
`μ > 0`, the Chernoff saddle `t* = s/(? )` activates the term of order `r* ≈ s/μ`; for `s ≈ n·log m`
and `μ = E_1 = n` this is `r* ≈ log m`.  We record the elementary fact that the single term of order
`r` in the MGF, `(tʳ/r!)·E_r`, is *strictly positive whenever `E_r > 0`* — so it is a genuine,
non-droppable contributor.  No fixed finite truncation `N < r*` upper-bounds the true MGF, so the
route cannot terminate before depth `r*`. -/
theorem truncMGF_term_pos {E : ℕ → ℝ} {t : ℝ} (ht : 0 < t) {r : ℕ} (hEr : 0 < E r) :
    0 < (t ^ r / r.factorial) * E r := by
  have : (0 : ℝ) < t ^ r / r.factorial := by positivity
  exact mul_pos this hEr

/-- **Adding the deepest order cannot lower the MGF.** Extending the truncation from `N` to `N+1`
adds the nonnegative order-`N` term; the partial sums are monotone increasing in `N` (for `E ≥ 0`).
This is the formal statement that one cannot truncate the energy series early: the deep moments
`E_{log m}` are still adding mass at the saddle, which is why the large-deviation route reduces to
the depth-`log m` energy bound (= BGK/Paley), not to a low-order cumulant fix. -/
theorem truncMGF_le_succ {E : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hE : ∀ r, 0 ≤ E r) (N : ℕ) :
    truncMGF E t N ≤ truncMGF E t (N + 1) := by
  unfold truncMGF
  rw [Finset.sum_range_succ]
  have : (0 : ℝ) ≤ (t ^ N / N.factorial) * E N := by
    have : (0 : ℝ) ≤ t ^ N / N.factorial := by positivity
    exact mul_nonneg this (hE N)
  linarith

#print axioms truncMGF_mono
#print axioms truncMGF_term_pos
#print axioms truncMGF_le_succ

end ArkLib.ProximityGap.Frontier.Attack08CumulantMGFAllOrders
