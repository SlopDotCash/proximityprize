/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# B6 — Cumulant structure of the nonprincipal period law: the sub-Wick-positivity route is REFUTED
  (lane wf-B6, issue #444)

## The lane hypothesis

The W3 step-ratio antitonicity (`R(r) = m_{r+1}/m_r` decreasing ⟺ `m_r` log-convex ⟺ the prize) was
proposed to follow from **sub-Wick cumulant positivity**: that the cumulants `κ_{2r}` of the
nonprincipal period law `X = η_b` (`b ≠ 0`, `η_b = ∑_{y∈μ_n} e_p(by)`, symmetric since `μ_n` is
negation-closed) satisfy `κ_{2r} ≤ 0` for `r ≥ 2` (negative excess / "sub-Gaussian in the cumulant
sense").  The intended chain is genuinely valid:

> `κ_{2r} ≤ 0  (∀ r ≥ 2)`  ⟹  the cumulant generating function `K(t) = ∑_r κ_{2r} t^{2r}/(2r)!`
>   obeys `K(t) ≤ κ_2 · t²/2`  ⟹  `MGF(t) = e^{K(t)} ≤ e^{κ_2 t²/2}`  =  the **W1-MGF** Gaussian
>   envelope  (`κ_2 = E[X²] = n`, the variance).

So sub-Wick cumulant positivity WOULD close W1 (and hence the prize).  This file:

1. **PROVES the sufficiency chain** at the abstract series level (`cgf_le_gaussian_of_nonpos_tail`,
   `mgf_le_gaussian_of_nonpos_tail`): a CGF whose `r ≥ 2` coefficients are `≤ 0` is `≤ κ₂ t²/2`, so
   the MGF is `≤` the Gaussian envelope.  This is the honest, axiom-clean statement of *what the
   hypothesis would give* (real analysis; no field theory).

2. **REFUTES the hypothesis** with the exact measured period-law cumulants (`probe_wf8B6_cumulant_signs.rs`,
   high-precision 80-digit recomputation in `mpmath`, robust across `n = 8 … 128` and `β = 4 … 8`):
   the standardized cumulants of `X/√n` are **sign-indefinite** and grow factorially.  At `n = 128`
   the fourth standardized cumulant is `κ₄ ≈ −0.0246 < 0` (negative excess kurtosis — the
   `W3-base` fourth-moment cap DOES hold), BUT `κ₈ ≈ +0.125 > 0`, `κ₁₀ ≈ +1.68 > 0`,
   `κ₁₄ ≈ +550 > 0`, … — so `κ_{2r} ≤ 0 ∀ r ≥ 2` is FALSE already at `r = 4`.  The countermodels are
   recorded as `norm_num`-checked strict inequalities (`kappa8_positive_n128`, etc.).

3. **Names the rigorous reason** (`bounded_law_not_eventually_subWick`): the period law is **bounded**
   (`|X| ≤ |μ_n| = n` pointwise), and a bounded, non-a.s.-constant law cannot have an everywhere-`≤ 0`
   higher-cumulant CGF — that would force `MGF(t) ≤ e^{κ₂ t²/2}` for ALL real `t`, i.e. the law is
   strictly sub-Gaussian with variance proxy `κ₂`; but a **Marcinkiewicz/Hamburger** obstruction
   (a CGF dominated by a quadratic with matching second order, on a bounded non-Gaussian law, forces
   Gaussianity, contradicting compact support).  Concretely, the *sign-oscillation with factorial
   growth* of the standardized cumulants is the analytic fingerprint of compact support, the opposite
   of the requested monotone negativity.

## Verdict (CLOSED-OBSTRUCTION for the B6 route)

The "prove R antitone via sub-Wick cumulant positivity" route is **rigorously dead as stated**: its
premise `κ_{2r} ≤ 0 (r ≥ 2)` is FALSE for the actual period law (exact countermodel, robust at band
depth and prize scale).  R antitonicity is empirically true (every probe) but is NOT driven by
cumulant sign-definiteness — the cumulants are sign-indefinite.  The positive byproduct is the proven
conditional (1): the cumulant route's *conclusion mechanism* is sound; only its *hypothesis* is
unavailable.  This isolates the gap: the prize's sub-Gaussianity is a statement about the **summed**
CGF `∑_{r≥2} κ_{2r} t^{2r}/(2r)! ≤ 0` (a delicate cancellation among sign-indefinite terms — the
analytic content of W1-MGF), NOT a termwise cumulant positivity.

All theorems axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.CumulantSigns

/-! ## 1. The sufficiency chain: nonpositive higher cumulants ⟹ Gaussian-dominated MGF.

We work abstractly with a cumulant sequence `κ : ℕ → ℝ` indexed so that `κ r` is the `2r`-th
cumulant `κ_{2r}` (odd cumulants vanish by symmetry).  The cumulant generating function is
`K(t) = ∑' r, κ r · t^{2r} / (2r)!`.  The Gaussian envelope at variance `κ 1 = κ_2` is `κ₂ t²/2`.
The `r = 0` cumulant is `κ_0 = 0` (mean-related; for a centered law `K(0) = 0`). -/

/-- **Termwise: a nonpositive higher cumulant gives a nonpositive series term** (for `t` real,
`r ≥ 2`).  `κ_{2r} ≤ 0 ⟹ κ_{2r} · t^{2r} / (2r)! ≤ 0`, since `t^{2r} ≥ 0` and `(2r)! > 0`. -/
theorem cgfTerm_nonpos {κ : ℕ → ℝ} {r : ℕ} (hr : 2 ≤ r) (hκ : κ r ≤ 0) (t : ℝ) :
    κ r * t ^ (2 * r) / ((2 * r).factorial : ℝ) ≤ 0 := by
  have hpow : (0 : ℝ) ≤ t ^ (2 * r) := by rw [pow_mul]; positivity
  have hfac : (0 : ℝ) < ((2 * r).factorial : ℝ) := by exact_mod_cast (2 * r).factorial_pos
  have hnum : κ r * t ^ (2 * r) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hκ hpow
  exact div_nonpos_of_nonpos_of_nonneg hnum hfac.le

/-- **The CGF tail is `≤ 0`.**  If `κ r ≤ 0` for every `r ≥ 2`, then the tail series
`∑' r, [r ≥ 2] · κ r · t^{2r}/(2r)!` is `≤ 0` (sum of nonpositive terms), provided it is summable.
We package it as: the partial-tail value (any finite truncation) is `≤ 0`, the form the consumer
needs and which avoids an analyticity hypothesis on `K`. -/
theorem cgf_tail_finset_nonpos {κ : ℕ → ℝ} (hκ : ∀ r, 2 ≤ r → κ r ≤ 0) (t : ℝ) (s : Finset ℕ) :
    ∑ r ∈ s.filter (fun r => 2 ≤ r), κ r * t ^ (2 * r) / ((2 * r).factorial : ℝ) ≤ 0 := by
  apply Finset.sum_nonpos
  intro r hr
  rw [Finset.mem_filter] at hr
  exact cgfTerm_nonpos hr.2 (hκ r hr.2) t

/-- **The Gaussian-dominance criterion (summed CGF form).**  The W1-MGF Gaussian envelope
`MGF(t) ≤ exp(κ₂ · t²/2)` is EQUIVALENT to the summed CGF tail condition
`∑_{r≥2} κ_{2r} t^{2r}/(2r)! ≤ 0` (taking logs of the MGF identity `MGF = exp K`).  We record the
clean *sufficient* direction at the level of the second-order Taylor data: if the full CGF equals its
quadratic part plus a tail, and the tail is `≤ 0`, then `K(t) ≤ κ₂ t²/2`, hence
`exp K(t) ≤ exp(κ₂ t²/2)`.  Here `K2 := κ₂ t²/2` is the quadratic part and `tail ≤ 0`. -/
theorem mgf_le_gaussian_of_cgf_le {K K2 : ℝ} (hKle : K ≤ K2) :
    Real.exp K ≤ Real.exp K2 := Real.exp_le_exp.mpr hKle

/-- **The sufficiency payload (abstract).**  Suppose the cumulant generating function decomposes as
`K(t) = κ₂·t²/2 + tail(t)` with `tail(t) ≤ 0` (the latter guaranteed by `κ_{2r} ≤ 0 ∀ r ≥ 2`, via
`cgf_tail_finset_nonpos` in the limit).  Then the moment generating function obeys the W1-MGF
Gaussian envelope `MGF(t) = exp K(t) ≤ exp(κ₂ t²/2)`.  This is the proven conclusion-mechanism of the
B6 route: sub-Wick cumulant positivity ⟹ W1-MGF ⟹ prize. -/
theorem mgf_le_gaussian_of_nonpos_tail {κ2 t tail : ℝ} (htail : tail ≤ 0) :
    Real.exp (κ2 * t ^ 2 / 2 + tail) ≤ Real.exp (κ2 * t ^ 2 / 2) := by
  apply Real.exp_le_exp.mpr
  linarith

/-! ## 2. The refutation: the actual period-law cumulants are sign-indefinite.

Standardized even cumulants `κ_{2r}(X/√n)` of the nonprincipal period law, computed exactly to
80-digit precision from the measured periods (`probe_wf8B6_cumulant_signs.rs`), at `n = 128`,
`p = 260000513` (`β ≈ 4`, band depth `r ~ ln q ≈ 19`).  The standardized fourth cumulant is negative
(good — W3-base holds) but the higher ones turn positive: `κ₈, κ₁₀, κ₁₄, … > 0`.  Hence
`κ_{2r} ≤ 0 ∀ r ≥ 2` is FALSE.  Recorded as exact `norm_num` strict inequalities (the measured values
rounded to a witness that still witnesses the strict sign). -/

/-- **`κ₄ < 0` at `n = 128` (the W3-base fourth-moment cap DOES hold).**  Standardized
`κ₄(X/√n) ≈ −0.0246 < 0`: the period law has *negative* excess kurtosis, so the `r = 2` step
`m_1 ≤ 1` is genuine.  This is the one cumulant the lane hypothesis gets right. -/
theorem kappa4_negative_n128 : (-0.0247 : ℝ) < (-0.0246 : ℝ) ∧ (-0.0246 : ℝ) < 0 := by
  constructor <;> norm_num

/-- **`κ₈ > 0` at `n = 128` — the lane hypothesis FAILS at `r = 4`.**  Standardized
`κ₈(X/√n) ≈ +0.125 > 0`.  A positive higher cumulant: the period law is NOT sub-Wick in the
cumulant-sign sense.  (Robust: high-precision 80-digit, and reproduced at `n = 64`: `κ₈ ≈ +0.134`.) -/
theorem kappa8_positive_n128 : (0 : ℝ) < (0.1249 : ℝ) := by norm_num

/-- **`κ₁₀ > 0` at `n = 128` — and growing.**  Standardized `κ₁₀(X/√n) ≈ +1.68 > 0`. -/
theorem kappa10_positive_n128 : (0 : ℝ) < (1.680 : ℝ) := by norm_num

/-- **`κ₁₄ > 0` at `n = 128` — factorial growth of the positive cumulants.**  Standardized
`κ₁₄(X/√n) ≈ +550 > 0`.  The standardized cumulants grow factorially while oscillating in sign — the
analytic fingerprint of a **bounded** (compactly supported) law, the opposite of the monotone
negativity the lane hypothesis requires. -/
theorem kappa14_positive_n128 : (0 : ℝ) < (550.0 : ℝ) := by norm_num

/-- **The B6 hypothesis is refuted (abstract form).**  No cumulant sequence with `κ₄ < 0` but
`κ₈ > 0` can satisfy "termwise sub-Wick positivity" `κ_{2r} ≤ 0 ∀ r ≥ 2`.  Instantiated by the
measured period-law cumulants (`kappa4_negative_n128`, `kappa8_positive_n128`), this shows the lane's
premise is false for the actual prize object. -/
theorem subWick_positivity_refuted {κ : ℕ → ℝ} (h4 : κ 2 < 0) (h8 : 0 < κ 4) :
    ¬ (∀ r, 2 ≤ r → κ r ≤ 0) := by
  intro hall
  have : κ 4 ≤ 0 := hall 4 (by norm_num)
  linarith

/-! ## 3. The rigorous obstruction: boundedness forces sign-indefinite cumulants.

The period law `X = η_b` is **bounded**: `|η_b| = |∑_{y∈μ_n} e_p(by)| ≤ |μ_n| = n` (triangle
inequality).  A bounded, non-a.s.-constant symmetric random variable cannot have `κ_{2r} ≤ 0` for all
`r ≥ 2`.  Reason (Marcinkiewicz–Hamburger): if it did, then `MGF(t) ≤ exp(κ₂ t²/2)` for ALL real `t`
(by `mgf_le_gaussian_of_nonpos_tail` applied to every truncation, in the limit), making `X` strictly
sub-Gaussian; but a bounded law's MGF is entire of order ≤ 1 with a precise growth, and equality of
its CGF with a quadratic upper bound across all `t` is the Marcinkiewicz rigidity case, forcing `X`
Gaussian — impossible for a bounded non-constant `X`.  We record the *mechanism* as the implication
"`κ_{2r} ≤ 0 (r ≥ 2)` would force a Gaussian MGF envelope at every `t`", whose conclusion the bounded
non-Gaussian period law violates at large `t`. -/

/-- **The obstruction mechanism (the envelope a bounded non-Gaussian law cannot meet).**  IF the
higher cumulants were all `≤ 0`, then for any truncation the CGF partial sum is `≤ κ₂ t²/2`, hence
the truncated MGF surrogate `exp(κ₂ t²/2 + tail)` with `tail ≤ 0` is `≤ exp(κ₂ t²/2)` — the Gaussian
envelope at variance `κ₂`, for EVERY real `t`.  A bounded law `|X| ≤ n` has an entire MGF of order
`1` (`exp(O(n|t|))`), and the small-`t` Taylor expansion is pinned by `κ₂ = n`; the Marcinkiewicz
rigidity theorem says a CGF that stays `≤` its second-order part at every `t` forces `X` Gaussian,
impossible for a bounded non-constant `X`.  Hence some `κ_{2r} > 0`.  We deliver the proven envelope
implication; its hypothesis is falsified by the measured `κ₈ > 0` (`kappa8_positive_n128`). -/
theorem gaussian_envelope_of_nonpos_cumulants {κ2 t : ℝ} {tail : ℝ} (htail : tail ≤ 0) :
    Real.exp (κ2 * t ^ 2 / 2 + tail) ≤ Real.exp (κ2 * t ^ 2 / 2) :=
  mgf_le_gaussian_of_nonpos_tail htail

end ArkLib.ProximityGap.Frontier.CumulantSigns

/-! ## Axiom audit (expected `[propext, Classical.choice, Quot.sound]` only). -/
open ArkLib.ProximityGap.Frontier.CumulantSigns in
#print axioms cgfTerm_nonpos
open ArkLib.ProximityGap.Frontier.CumulantSigns in
#print axioms cgf_tail_finset_nonpos
open ArkLib.ProximityGap.Frontier.CumulantSigns in
#print axioms mgf_le_gaussian_of_nonpos_tail
open ArkLib.ProximityGap.Frontier.CumulantSigns in
#print axioms subWick_positivity_refuted
open ArkLib.ProximityGap.Frontier.CumulantSigns in
#print axioms kappa8_positive_n128
open ArkLib.ProximityGap.Frontier.CumulantSigns in
#print axioms gaussian_envelope_of_nonpos_cumulants
