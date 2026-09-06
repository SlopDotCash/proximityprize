/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# SAC01: cross-support cancellation in G133 is absent at the first exact test cells

G133 splits the centered fully-disjoint census into the ordinary nonprincipal moment plus a
signed puncture correction.  A proposed cluster-expansion refinement was to decompose that
correction by the support size of the left word and obtain cancellation *between* support sizes.

`scripts/probes/probe_sac_signed_puncture_support.py` computes this decomposition using exact
integer collision counts (no FFT and no floating point).  In every proper `p ≈ n^4` test cell at
`r = 3`, and at `(n,p,r)=(16,65537,4)`, all support corrections have the same (negative) sign.
Consequently their cancellation ratio is exactly one: there is no cross-support cancellation.

This file proves the general same-sign no-go and kernel-checks the `(16,65537,4)` certificate.
It does **not** claim that puncture correction is useless: in fact it almost cancels the ordinary
moment.  The surviving target is a direct, phase-sensitive upper bound on each aggregate support
bucket (or on their sum), not a triangle-saving obtained by coupling different support sizes.

Issue #466.  NO CORE / Paley / proximity-gap closure claim.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SAC01SignedPunctureSupportNoGo

open Finset

/-- If every support-size correction is nonpositive, taking the absolute value after summing
gains nothing over summing the absolute values: the cross-support cancellation ratio is one. -/
theorem abs_sum_eq_sum_abs_of_nonpos {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, c i ≤ 0) :
    |∑ i ∈ s, c i| = ∑ i ∈ s, |c i| := by
  rw [abs_of_nonpos (Finset.sum_nonpos fun i hi => hc i hi)]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (abs_of_nonpos (hc i hi)).symm

/-- Exact probe certificate at `(n,p,r)=(16,65537,4)`.  The four support-size puncture
corrections are all negative and sum to `-282820222144`; hence the absolute sum equals the sum
of absolutes exactly.  These integers are independently determined by the collision formulas
`C_s = p D_s - A_s (n-s)^r - (p E_s - A_s n^r)` printed by the probe. -/
theorem n16_p65537_r4_no_crossSupportCancellation :
    let c : Fin 4 → ℝ := ![-810016, -1370037600, -49285005504, -232164369024]
    (∀ i, c i ≤ 0) ∧
      (∑ i, c i = -282820222144) ∧
      |∑ i, c i| = ∑ i, |c i| := by
  dsimp
  have hc : ∀ i : Fin 4,
      (![(-810016 : ℝ), -1370037600, -49285005504, -232164369024] i) ≤ 0 := by
    intro i
    fin_cases i <;> norm_num
  refine ⟨hc, ?_, ?_⟩
  · simp [Fin.sum_univ_four]
    norm_num
  · simpa using abs_sum_eq_sum_abs_of_nonpos Finset.univ
      (![(-810016 : ℝ), -1370037600, -49285005504, -232164369024])
      (fun i _ => hc i)

#print axioms abs_sum_eq_sum_abs_of_nonpos
#print axioms n16_p65537_r4_no_crossSupportCancellation

end ArkLib.ProximityGap.Frontier.SAC01SignedPunctureSupportNoGo
