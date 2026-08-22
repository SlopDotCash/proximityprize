/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G100: per-depth nonnegative caps lose cross-depth DC cancellation

G96's per-depth centered-cap theorem is a valid sufficient consumer for `DCEnergyBound`, but it is
not an equivalence.  Requiring every depth separately to satisfy

```text
q * fiber_s <= q * cap_s + population_s
```

with `cap_s : ℕ` replaces each signed depth anomaly by its positive part.  A positive anomaly at
one depth can be cancelled by a negative anomaly at another depth in the global DC-subtracted
moment; the per-depth cap interface discards that cancellation.

This file gives the minimal two-bin countermodel and records the lossless signed interface over
`ℤ`.  The global anomaly is exactly the sum of signed depth anomalies, with no positive-part loss.
G96 remains correct as a sufficient theorem; only claims that its per-depth hypothesis is an exact
or equivalent formulation are refuted.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G100PerDepthCenteringCancellation

/-- Signed centered anomaly of one depth. -/
def depthAnomaly (q fiber population : ℕ) : ℤ :=
  (q : ℤ) * fiber - population

/-- **Lossless signed decomposition.** The total DC-centered anomaly is exactly the sum of the
per-depth signed anomalies. -/
theorem sum_depthAnomaly
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ℕ) (fiber population : ι → ℕ) :
    ∑ i ∈ S, depthAnomaly q (fiber i) (population i) =
      (q : ℤ) * (∑ i ∈ S, fiber i) - ∑ i ∈ S, population i := by
  simp only [depthAnomaly, Finset.sum_sub_distrib]
  push_cast
  rw [Finset.mul_sum]

/-- The exact global centered bound, expressed through signed depth anomalies. -/
theorem sum_depthAnomaly_le_iff
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q wick : ℕ) (fiber population : ι → ℕ) :
    (∑ i ∈ S, depthAnomaly q (fiber i) (population i) ≤ (q : ℤ) * wick) ↔
      (q : ℤ) * (∑ i ∈ S, fiber i) ≤
        (q : ℤ) * wick + ∑ i ∈ S, population i := by
  rw [sum_depthAnomaly]
  omega

/-- Two-bin data with perfect global DC cancellation: depth zero has anomaly `+2`, depth one has
anomaly `-2`, so the total anomaly and the required global Wick cap are both zero. -/
theorem twoDepth_global_centered_bound :
    (2 : ℕ) * (∑ i : Fin 2, (![1, 0] i : ℕ)) ≤
      2 * 0 + ∑ i : Fin 2, (![0, 2] i : ℕ) := by
  decide

/-- **Countermodel to necessity of nonnegative per-depth caps.**  Although the aggregate centered
bound above holds with Wick cap zero, there is no family of natural per-depth caps of total at most
zero satisfying both binwise centered inequalities. -/
theorem no_nonnegative_perDepth_caps_for_twoDepth_model :
    ¬ ∃ cap : Fin 2 → ℕ,
      (∀ i : Fin 2,
        2 * (![1, 0] i : ℕ) ≤ 2 * cap i + (![0, 2] i : ℕ)) ∧
      (∑ i : Fin 2, cap i) ≤ 0 := by
  rintro ⟨cap, hbin, hsum⟩
  have h0 := hbin 0
  have hcap0 : cap 0 = 0 := by
    have := Finset.single_le_sum (f := cap) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
    have hsum0 : (∑ i : Fin 2, cap i) = 0 := Nat.eq_zero_of_le_zero hsum
    rw [hsum0] at this
    omega
  simp [hcap0] at h0

/-- Hence aggregate DC control does not imply existence of G96-style nonnegative per-depth caps,
even for two depths and zero Wick allowance. -/
theorem aggregate_does_not_imply_perDepth_caps :
    ((2 : ℕ) * (∑ i : Fin 2, (![1, 0] i : ℕ)) ≤
      2 * 0 + ∑ i : Fin 2, (![0, 2] i : ℕ)) ∧
    (¬ ∃ cap : Fin 2 → ℕ,
      (∀ i : Fin 2,
        2 * (![1, 0] i : ℕ) ≤ 2 * cap i + (![0, 2] i : ℕ)) ∧
      (∑ i : Fin 2, cap i) ≤ 0) :=
  ⟨twoDepth_global_centered_bound, no_nonnegative_perDepth_caps_for_twoDepth_model⟩

end ArkLib.ProximityGap.Frontier.G100PerDepthCenteringCancellation

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G100PerDepthCenteringCancellation.sum_depthAnomaly
#print axioms
  ArkLib.ProximityGap.Frontier.G100PerDepthCenteringCancellation.sum_depthAnomaly_le_iff
#print axioms
  ArkLib.ProximityGap.Frontier.G100PerDepthCenteringCancellation.twoDepth_global_centered_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G100PerDepthCenteringCancellation.no_nonnegative_perDepth_caps_for_twoDepth_model
#print axioms
  ArkLib.ProximityGap.Frontier.G100PerDepthCenteringCancellation.aggregate_does_not_imply_perDepth_caps
