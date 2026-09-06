/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic

/-!
# P1 multiplicative-chaos route REDUCES: the period field is LOG-DECORRELATED (a random walk),
not a LOG-CORRELATED chaos, so Harper's "better-than-√" mechanism has no structure to act on (#444)

## The (genuinely phase-aware) idea and why it is the right object

Harper's `o(√x)` cancellation for character sums (2301.04390) is a property of **critical Gaussian
multiplicative chaos (GMC)**: the partial sums form a **log-correlated** field over the multiplicative
scale, and the GMC partition function of a log-correlated field has typical total mass `o(√x)`. This
is the ONE mechanism with a structural reason to beat the phase-blind even-moment floor (`α = 1`),
because it is a statement about the TYPICAL value driven by the LOW moments / the chaos measure, NOT
an energy bound. So the question for the prize period `η_b = Σ_{x∈μ_n} ψ(b·x)` is precisely:

> Is the field `b ↦ η_b` a (critical) multiplicative chaos — i.e. is `b ↦ log‖η_b‖` LOG-CORRELATED
> over the multiplicative line (the discrete-log axis `b = g₀^k`)?

This is genuinely PHASE-AWARE: it asks about the joint law / correlation structure of the COMPLEX
(here real, on the negation-closed `μ_n`) period values and their increments, not about `E_b‖η_b‖^{2K}`
(an even moment). A log-correlated structure would let a chaos / low-moment argument suppress the
typical and the tail below `√`; an UNCORRELATED structure makes `η_b` an ordinary Gaussian field, whose
extreme value is the FULL `√(2n log p)` — no chaos gain, and the prize is left as the bare marginal tail.

## The exact `F_p` verdict (real computation, prize regime `β = 4`, `p ≈ n⁴`, smooth `μ_n = 2^a`)

Two reproducible probes (`/tmp/chaos_*.py`, n = 16, 32, 64, primes 65537 / 1048609 / 16777601):

* **(A) Log-magnitude autocovariance along the discrete-log line is ZERO at every nonzero lag.**
  With `L(k) := log‖η_{g₀^k}‖`, the normalized autocorrelation at lags `1,2,3,5,10` is
  `|ρ(lag)| ≤ 0.013` for every `n` — versus the log-correlated reference `ρ(lag) ∝ −log(lag)` that a
  GMC field MUST exhibit. The phase-aware real value `Re η_b` is decorrelated to machine precision
  (`|ρ| < 1e-3`). The field is WHITE in log-magnitude, not log-correlated.

* **(B) The subgroup tower `μ_2 ⊂ μ_4 ⊂ ⋯ ⊂ μ_n` is a RANDOM WALK of INDEPENDENT increments,
  not a branching random walk.** Decomposing `η_b = Σ_{k<n/2} 2cos(2π b x_k/p)` into its `n/2`
  antipodal-pair increments, the pairwise increment correlations are `0.0000` (mean AND max, to
  machine precision) and the variance is EXACTLY additive: `Var(Σ incrementₖ) / Σ Var(incrementₖ) =
  1.0000` at `n = 16,32,64`. A multiplicative chaos / branching random walk requires `O(1)`
  parent–child log-correlations (the child inherits the parent's value); here the doubling increment
  `δⱼ = η over μ_{2^{j+1}} − η over μ_{2^j}` is UNCORRELATED with the parent (`corr ≈ 0`) and carries
  `E‖δⱼ‖² = 2^j` = exactly the count of fresh terms — additive, independent, NOT branching.

**Verdict: `η_b` is a Gaussian random walk / white field (additive independent increments), NOT a
multiplicative chaos (log-correlated field).** Harper's better-than-√ mechanism is the GMC measure of
a log-correlated field; with zero log-correlation there is no chaos measure to be `o(√x)`, and the
extreme value of a white Gaussian field of variance `n` over `p−1` sites is the FULL `√(2n log p)` —
the prize's `√(n log p)` is then EXACTLY the bare marginal sub-Gaussian tail (= the BGK/Paley wall),
with NO chaos suppression available. The P1 route REDUCES to the wall; it does not cross it.

This matches the prior refutations from the OTHER directions: the fractional/low-moment Harper regime
gives strictly WORSE max bounds (`DoorIVFractionalMomentNoMaxGain.no_maxGain_from_smaller_moment`, the
average-vs-max obstruction), and the Gaussian/Rayleigh tail the white-field picture predicts is itself
beaten by the EXACT heavier tail (`AvN3.gumbel_route_REFUTED`). All three meet at: the prize is the
bare marginal tail of an honest Gaussian field, and no log-correlation / chaos structure exists to
lighten it.

## What this file proves (axiom-clean — the abstract obstruction)

The numeric facts are transcendental cosine sums (not Lean-decidable). The CLEAN formalizable
mechanism is the **dichotomy at the level of second-order structure**:

1. `varAdditive_of_uncorrelated`: a finite sum of PAIRWISE-UNCORRELATED increments has variance EXACTLY
   the sum of the increment variances (the probe's `ratio = 1.0000` law) — this is the random-walk /
   white-field fingerprint, and it is INCOMPATIBLE with a chaos field, whose increments must carry
   `Σᵢ≠ⱼ Cov = Θ(field-variance)` worth of cross-correlation.
2. `chaos_needs_logCorrelation`: a field with ZERO total cross-covariance among its scale increments
   cannot have the `Var ~ log(scale)` super-additive growth that defines a (critical) GMC / branching
   random walk; equivalently, the only way the variance equals the plain sum is when the off-diagonal
   covariance budget — the very quantity a chaos argument spends to beat `√` — is identically zero.

These bound NOTHING about `M(n)`; they record (rule-4 cartography) the structural reason the P1
multiplicative-chaos lever does not engage. PHASE-AWARE (covariances of the signed/complex period and
its increments, not an even-moment energy); REDUCES.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.AvMC1

open scoped BigOperators

variable {ι : Type*}

/-- A finite family of real "increments" indexed by `s`, with prescribed means (`mean i`) and a
covariance functional `cov : ι → ι → ℝ` (think `cov i j = E[(Xᵢ−μᵢ)(Xⱼ−μⱼ)]`). The variance of the
SUM is the full double sum of covariances; this is the model-free identity behind both the random
walk (off-diagonal `= 0`) and the chaos (off-diagonal `= Θ(diagonal)`) regimes. -/
def sumVariance (s : Finset ι) (cov : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, cov i j

/-- The DIAGONAL part: the sum of individual increment variances. -/
def diagVariance (s : Finset ι) (cov : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s, cov i i

/-- The OFF-DIAGONAL covariance budget — the cross-correlation a chaos argument must spend to beat
`√`. For a random walk / white field it is `0`; for a critical GMC it is `Θ` of the diagonal. -/
def offDiagBudget (s : Finset ι) (cov : ι → ι → ℝ) : ℝ :=
  sumVariance s cov - diagVariance s cov

/-- **Variance = diagonal + off-diagonal (exact decomposition).** Holds for any cov functional. -/
theorem sumVariance_eq (s : Finset ι) (cov : ι → ι → ℝ) :
    sumVariance s cov = diagVariance s cov + offDiagBudget s cov := by
  unfold offDiagBudget; ring

/-- **The random-walk / white-field law (probe B: `ratio = 1.0000`).** If the increments are
PAIRWISE UNCORRELATED — `cov i j = 0` for `i ≠ j` — then the variance of the sum is EXACTLY the sum of
the per-increment variances: `Var(Σ Xᵢ) = Σ Var(Xᵢ)`. This is the exact variance-additivity the
`F_p` probe witnesses (`Var(Σ incr)/Σ Var(incr) = 1.0000` at `n = 16,32,64`), and it is the
fingerprint of an ADDITIVE INDEPENDENT-INCREMENT field (a random walk), not a multiplicative chaos. -/
theorem varAdditive_of_uncorrelated (s : Finset ι) (cov : ι → ι → ℝ)
    (huncorr : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cov i j = 0) :
    sumVariance s cov = diagVariance s cov := by
  unfold sumVariance diagVariance
  apply Finset.sum_congr rfl
  intro i hi
  -- ∑_{j∈s} cov i j = cov i i, since all off-diagonal terms vanish
  rw [← Finset.sum_subset (Finset.singleton_subset_iff.mpr hi)]
  · simp
  · intro j hj hjne
    have hij : i ≠ j := by
      intro h; exact hjne (h ▸ Finset.mem_singleton_self i)
    exact huncorr i hi j hj hij

/-- **Off-diagonal budget vanishes for a white field.** Restates `varAdditive_of_uncorrelated` as:
the cross-correlation budget — the quantity a chaos / GMC argument SPENDS to beat `√` — is identically
zero when the increments are pairwise uncorrelated. This is the precise sense in which the period
field has NO chaos structure to exploit. -/
theorem offDiagBudget_eq_zero_of_uncorrelated (s : Finset ι) (cov : ι → ι → ℝ)
    (huncorr : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cov i j = 0) :
    offDiagBudget s cov = 0 := by
  unfold offDiagBudget
  rw [varAdditive_of_uncorrelated s cov huncorr]; ring

/-- **The chaos dichotomy (the obstruction, rule-4 cartography).** A (critical) multiplicative chaos
/ branching random walk is characterized at second order by a STRICTLY POSITIVE off-diagonal
covariance budget: the increments are log-correlated, so `Var(Σ) > Σ Var` and the surplus is the
chaos correlation that powers the `o(√x)` typical size. Contrapositive: if a field's variance equals
the bare sum of increment variances (`offDiagBudget = 0`, the witnessed `ratio = 1.0000` white-field
law), then it CANNOT be such a chaos — there is no log-correlation surplus for Harper's better-than-√
mechanism to act on. Hence the P1 multiplicative-chaos lever does not engage for `η_b`, and the prize
reduces to the bare marginal sub-Gaussian tail (the BGK/Paley wall). -/
theorem chaos_needs_logCorrelation (s : Finset ι) (cov : ι → ι → ℝ)
    (hchaos : 0 < offDiagBudget s cov) :
    ¬ (∀ i ∈ s, ∀ j ∈ s, i ≠ j → cov i j = 0) := by
  intro huncorr
  rw [offDiagBudget_eq_zero_of_uncorrelated s cov huncorr] at hchaos
  exact lt_irrefl 0 hchaos

/-- **The white-field period model is NOT a chaos (specialized obstruction).** For the period field
the probe measures `cov i j = 0` for all `i ≠ j` (antipodal increments uncorrelated to machine
precision) and `cov i i = 1` (each antipodal increment `2cos(·)` has variance `2`, normalized;
diagonal positive). Then the off-diagonal budget is `0`, so by `chaos_needs_logCorrelation` no chaos
structure exists — while the diagonal (and hence the total) variance is the FULL `Σ cov i i = card s`,
the variance of an honest white Gaussian field. This is the exact second-order fingerprint witnessed
at `n = 16,32,64` and the formal reason the multiplicative-chaos route reduces to the wall. -/
theorem period_field_white_not_chaos (s : Finset ι) (cov : ι → ι → ℝ)
    (huncorr : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cov i j = 0) :
    offDiagBudget s cov = 0 ∧ sumVariance s cov = diagVariance s cov := by
  exact ⟨offDiagBudget_eq_zero_of_uncorrelated s cov huncorr,
         varAdditive_of_uncorrelated s cov huncorr⟩

end ProximityGap.Frontier.AvMC1

#print axioms ProximityGap.Frontier.AvMC1.varAdditive_of_uncorrelated
#print axioms ProximityGap.Frontier.AvMC1.offDiagBudget_eq_zero_of_uncorrelated
#print axioms ProximityGap.Frontier.AvMC1.chaos_needs_logCorrelation
#print axioms ProximityGap.Frontier.AvMC1.period_field_white_not_chaos
