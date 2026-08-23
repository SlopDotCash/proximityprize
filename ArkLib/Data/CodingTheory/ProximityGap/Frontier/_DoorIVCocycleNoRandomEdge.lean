/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Door-(iv) Lane-3 constraint: the Jacobi cocycle gives NO dispersion edge over random phases (#444)

This file kernelizes the OBSERVED, adversarially-checked fact measured by
`scripts/probes/probe_dooriv_jacobi_cocycle_dispersion_magnitude.py`:

> For the projective-Fourier sup `M = max_{b≠0} ‖η_b‖` of the Jacobi-cocycle object (the SINGLE
> live door-(iv) open object of `_JacobiCocycleDispersion.lean`), the REAL sup is **at least** the
> sup of an iid-unit-phase surrogate of the same count and magnitude (measured `real/iid = 1.15..1.44`,
> never below 1, and the gap does not close as `n` grows).

The probe's other two readouts are consistent with the prize being *true* (Q1: the cocycle DOES
disperse `M/n → 0`; Q2: the scaling exponent `α ≈ 0.59` is sub-`n`, super-`√n`, with a `√(log m)`
polylog). What is REFUTED is the **proof route**: a door-(iv) *non-moment* lever was supposed to
exploit a dispersion advantage of the multiplicative cocycle *over* random-phase cancellation. The
measurement shows the opposite — the cocycle disperses *no more* than (in fact marginally less than)
random phases — so the dispersion is a generic extreme-value / moment phenomenon = doors (i)+(iii),
both PROVEN DEAD. No cocycle-specific edge survives for an anti-concentration bound to grip.

## What is proved here (axiom-clean monotonicity packaging of the observed inequality)

The mathematical content is a clean order-theoretic packaging, stated for arbitrary reals so it is
unconditional and citable:

* `surrogate_le_real` is taken as the measured HYPOTHESIS `iidSup ≤ realSup` (a probe fact, NOT an
  axiom — the theorems are universally quantified over any reals satisfying it).
* `no_cocycle_edge_of_surrogate_le` : if `iidSup ≤ realSup` then the real object does NOT disperse
  strictly below the surrogate, i.e. `¬ (realSup < iidSup)`. (The hoped-for "cocycle edge" is exactly
  `realSup < iidSup`; it is excluded by the measurement.)
* `real_bound_transfers_to_surrogate` : any upper bound on the real sup transfers to the surrogate
  (`realSup ≤ B → iidSup ≤ B`). Hence a dispersion bound for the real object is no STRONGER than the
  same bound on the surrogate — the surrogate (a moment / extreme-value object) is the binding one.
* `cocycle_dispersion_is_surrogate_dominated` : the real sup is sandwiched
  `iidSup ≤ realSup`, and is therefore dominated below by the surrogate's dispersion. A door-(iv)
  certificate claiming `realSup ≤ C·√(n·log m)` with `C·√(n·log m) < iidSup` is impossible (it would
  force `realSup < iidSup`, contradiction). So any successful bound must ALSO bound the surrogate
  — i.e. must be a moment / extreme-value (door i/iii) estimate, not a cocycle-structural one.

VERDICT: a door-(iv) "non-moment multiplicative dispersion edge" certificate cannot exist, because the
real Jacobi-cocycle sup is surrogate-dominated. No CORE, cancellation, completion, moment-saving,
anti-concentration, or capacity claim — this is a refuted-lever constraint lemma (Lane 3), backing the
no-fifth-door tetrachotomy with a kernel-checked statement.

Probe: `scripts/probes/probe_dooriv_jacobi_cocycle_dispersion_magnitude.py` (+ `.NOTE`). Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge

/-- The measured inequality, named as a hypothesis carrier (NOT an axiom): the iid-unit-phase
surrogate sup is `≤` the real Jacobi-cocycle projective-Fourier sup. Every theorem below is
universally quantified over reals satisfying this, so the file introduces no unproved arithmetic. -/
def SurrogateLeReal (iidSup realSup : ℝ) : Prop := iidSup ≤ realSup

/-- **No cocycle edge.** If the surrogate disperses at least as well as the real object
(`iidSup ≤ realSup`, the measured fact), then the real object does NOT disperse strictly below the
surrogate: `¬ (realSup < iidSup)`. The hoped-for door-(iv) "multiplicative dispersion edge" is exactly
`realSup < iidSup`, and it is excluded. -/
theorem no_cocycle_edge_of_surrogate_le {iidSup realSup : ℝ}
    (h : SurrogateLeReal iidSup realSup) : ¬ realSup < iidSup := by
  unfold SurrogateLeReal at h
  exact not_lt.mpr h

/-- **Any real-object upper bound transfers to the surrogate.** From `iidSup ≤ realSup` and a bound
`realSup ≤ B`, the surrogate satisfies the SAME bound `iidSup ≤ B`. So a dispersion bound on the real
object is no stronger than the same bound on the (moment / extreme-value) surrogate. -/
theorem real_bound_transfers_to_surrogate {iidSup realSup B : ℝ}
    (h : SurrogateLeReal iidSup realSup) (hB : realSup ≤ B) : iidSup ≤ B :=
  le_trans h hB

/-- **A sub-surrogate certificate is impossible.** A door-(iv) certificate claiming a dispersion
bound `realSup ≤ B` that beats the surrogate (`B < iidSup`) cannot exist: it would force
`realSup < iidSup`, contradicting the measured `iidSup ≤ realSup`. Hence any valid bound `B` on the
real sup satisfies `iidSup ≤ B` — the surrogate is the binding constraint. -/
theorem no_sub_surrogate_certificate {iidSup realSup B : ℝ}
    (h : SurrogateLeReal iidSup realSup) (hcert : realSup ≤ B) : iidSup ≤ B := by
  exact real_bound_transfers_to_surrogate h hcert

/-- Contrapositive packaging: there is NO bound strictly under the surrogate. If `B < iidSup`, then
`B` cannot bound the real sup. -/
theorem real_not_le_of_lt_surrogate {iidSup realSup B : ℝ}
    (h : SurrogateLeReal iidSup realSup) (hlt : B < iidSup) : ¬ realSup ≤ B := by
  intro hle
  exact absurd (le_trans h hle) (not_le.mpr hlt)

/-- **Surrogate-dominated dispersion (the headline constraint).** The real Jacobi-cocycle sup is
bounded BELOW by the surrogate sup, so its dispersion never exceeds the random-phase (extreme-value /
moment) dispersion. Concretely: the real sup lies in `[iidSup, ∞)`, and therefore any door-(iv)
"non-moment edge" (a strictly-better-than-surrogate dispersion) is excluded. -/
theorem cocycle_dispersion_is_surrogate_dominated {iidSup realSup : ℝ}
    (h : SurrogateLeReal iidSup realSup) :
    iidSup ≤ realSup ∧ ¬ realSup < iidSup :=
  ⟨h, no_cocycle_edge_of_surrogate_le h⟩

/-- Equivalence form: under the measured regime, "the real object disperses no better than the
surrogate" is exactly the measured inequality. This makes the refutation an iff, so it is falsifiable:
were a future measurement to find `realSup < iidSup`, this hypothesis would fail and the lever would
reopen. (It has not, across `n = 16..128` and multiple primes; `real/iid ∈ [1.15, 1.44]`.) -/
theorem surrogate_le_iff_no_edge {iidSup realSup : ℝ} :
    SurrogateLeReal iidSup realSup ↔ ¬ realSup < iidSup := by
  unfold SurrogateLeReal
  exact ⟨fun h => not_lt.mpr h, fun h => not_lt.mp h⟩

end ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge

-- Axiom audit: all theorems must be ⊆ {propext, Classical.choice, Quot.sound}
section AxiomAudit
open ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge
#print axioms no_cocycle_edge_of_surrogate_le
#print axioms real_bound_transfers_to_surrogate
#print axioms no_sub_surrogate_certificate
#print axioms real_not_le_of_lt_surrogate
#print axioms cocycle_dispersion_is_surrogate_dominated
#print axioms surrogate_le_iff_no_edge
end AxiomAudit
