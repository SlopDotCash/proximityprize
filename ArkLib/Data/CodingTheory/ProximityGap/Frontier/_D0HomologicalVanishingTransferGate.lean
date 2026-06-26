/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false

/-!
# D0 homological-vanishing transfer gate: topology needs a prime-field comparison

Issue #464 flagged arXiv:2606.26440 as a genuinely new lead: homological vanishing lines for
braid-group configuration spaces give power-saving cancellation for arithmetic sums over
function fields, including Patterson-type Gauss-sum families over `F_q[t]`.

The surrounding #464 audit then identified the load-bearing gap for plain prime-field RS.  The
prize statistic is not just an auxiliary function-field sum.  It is a prime-indexed worst-case
quantity such as the Gauss-period house, wraparound surplus, or high-depth energy at
`p ≡ 1 mod n`.  Existing cohomological files already record the fixed-order Betti/Deligne
obstruction (`_FrontierSwanConductor`, `_JacobiFermatCohomology`,
`_CreateCorrelationLFunction`, `_EquivariantDescentWeightDropREFUTED`): the plain-RS step needs
growing-order, subgroup-scale, worst-case cancellation, not merely a fixed-order convexity bound.

This file records the remaining transfer gate axiom-cleanly.  A homological theorem helps the
prime-field floor only when it supplies:

* a pointwise pullback from each prize prime to the homological model;
* a comparison at the same growing depth used by the prize schedule; and
* a bound whose budget actually fits the subgroup-scale target.

Without those inputs, a bounded homological model is compatible with an arbitrary prime spike.
-/

namespace ArkLib.ProximityGap.Frontier.D0HomologicalVanishingTransferGate

/-- A homological/function-field model bound transfers to every prize prime only through a pointwise
comparison from the actual prime statistic into the auxiliary model statistic. -/
theorem prime_bound_of_homological_transfer
    {P Ω : Type*} (primeStat : P → ℝ) (homStat : Ω → ℝ) (pull : P → Ω) (B : ℝ)
    (hcompare : ∀ p, primeStat p ≤ homStat (pull p))
    (hhom : ∀ ω, homStat ω ≤ B) :
    ∀ p, primeStat p ≤ B := by
  intro p
  exact le_trans (hcompare p) (hhom (pull p))

/-- If the prize statistic is evaluated at a growing depth schedule, a fixed-depth homological
bound transfers only when the schedule is actually that fixed depth.  This is the formal version of
the "fixed-order theorem versus `r ≈ log p`" warning. -/
theorem fixed_depth_bound_transfers_on_matching_schedule
    {P Ω : Type*} (depth : P → ℕ) (primeStat : P → ℝ) (homStat : ℕ → Ω → ℝ)
    (pull : P → Ω) (d₀ : ℕ) (B : ℝ)
    (hdepth : ∀ p, depth p = d₀)
    (hcompare : ∀ p, primeStat p ≤ homStat (depth p) (pull p))
    (hhom : ∀ ω, homStat d₀ ω ≤ B) :
    ∀ p, primeStat p ≤ B := by
  intro p
  calc primeStat p ≤ homStat (depth p) (pull p) := hcompare p
    _ = homStat d₀ (pull p) := by rw [hdepth p]
    _ ≤ B := hhom (pull p)

/-- A depth-`0` homological bound is compatible with a prime spike at depth `1` even when there is
a pointwise comparison at the scheduled depth.  Thus a fixed-order vanishing theorem cannot be
read as a growing-depth prize bound without a uniform-in-depth theorem. -/
theorem fixed_depth_bound_does_not_control_other_depths (B : ℝ) :
    ∃ (depth : Unit → ℕ) (homStat : ℕ → Unit → ℝ) (primeStat : Unit → ℝ)
        (pull : Unit → Unit),
      (∀ ω, homStat 0 ω ≤ B) ∧
      (∀ p, primeStat p ≤ homStat (depth p) (pull p)) ∧
      (∃ p, B < primeStat p) := by
  refine ⟨(fun _ => 1), (fun d _ => if d = 0 then B - 1 else B + 2),
    (fun _ => B + 1), (fun _ => ()), ?_, ?_, ?_⟩
  · intro ω
    simp
  · intro p
    simp
  · exact ⟨(), by linarith⟩

/-- **No-comparison countermodel.** A uniformly bounded homological/function-field statistic is
compatible with an arbitrarily bad prime-field statistic.  Therefore homological vanishing by
itself does not decide the plain-RS floor. -/
theorem uncoupled_homological_bound_does_not_bound_primes
    {P Ω : Type*} [Nonempty P] (B : ℝ) :
    ∃ (homStat : Ω → ℝ) (primeStat : P → ℝ),
      (∀ ω, homStat ω ≤ B) ∧ (∃ p, B < primeStat p) := by
  refine ⟨fun _ => B - 1, fun _ => B + 1, ?_, ?_⟩
  · intro _; linarith
  · obtain ⟨p⟩ := ‹Nonempty P›
    exact ⟨p, by linarith⟩

/-- A convexity/Betti-scale bound `≤ B` is compatible with failure of a smaller target `≤ T`
whenever `T < B`.  A homological envelope therefore needs a genuine budget improvement, not just
a new language for the same larger bound. -/
theorem convexity_envelope_compatible_with_target_failure {B T : ℝ} (hTB : T < B) :
    ∃ stat : Unit → ℝ, (∀ u, stat u ≤ B) ∧ ¬ (∀ u, stat u ≤ T) := by
  refine ⟨fun _ => B, ?_, ?_⟩
  · intro _; rfl
  · intro htarget
    exact not_lt_of_ge (htarget ()) hTB

/-! ## Axiom audit. -/
#print axioms prime_bound_of_homological_transfer
#print axioms fixed_depth_bound_transfers_on_matching_schedule
#print axioms fixed_depth_bound_does_not_control_other_depths
#print axioms uncoupled_homological_bound_does_not_bound_primes
#print axioms convexity_envelope_compatible_with_target_failure

end ArkLib.ProximityGap.Frontier.D0HomologicalVanishingTransferGate
