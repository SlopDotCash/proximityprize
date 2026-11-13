/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Degree-2 autocorrelation SDP cannot reach the prize with only Weil-scale off-diagonal input

`_AvSDP_AutocorrPowerSaving.lean` records the useful degree-2 SDP envelope

```text
  ||DFT(a)||_inf^2 <= m + (m - 1) * B,
```

where `B` bounds the off-diagonal cyclic autocorrelations of the normalized Gauss-sum phase
sequence.  A Weil/Jacobi input naturally gives `B = Cweil * sqrt m`, producing a genuine
power-saving over completion.  The prize, however, needs the flat-polynomial scale

```text
  ||DFT(a)||_inf^2 <= Cprize * m * log m.
```

This file proves the clean arithmetic obstruction: if the degree-2 envelope is already at prize
scale, then the off-diagonal autocorrelation bound must be logarithmic,

```text
  B <= Cprize * (m / (m - 1)) * log m.
```

Thus a `B = Cweil * sqrt m` input reaches the prize only if `sqrt m <= O(log m)`, up to constants.
At the prize index `m = 2^128`, this is the exact missing `sqrt m -> log m` flat-polynomial gap.

This is a scope theorem: it refutes the hope that the degree-2 SDP plus ordinary Weil-scale
autocorrelation can prove the floor.  The degree-2 SDP is still a real partial improvement over
`sqrt p`; it just cannot be the final prize proof without a stronger high-order phase theorem.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.AvSDPPrizeGap

/-- The degree-2 autocorrelation SDP envelope: diagonal mass `m` plus `m - 1` off-diagonal
autocorrelations, each bounded by `B`. -/
def degreeTwoEnvelope (m B : ℝ) : ℝ := m + (m - 1) * B

/-- The flat-polynomial/prize envelope for the normalized Gauss-sum DFT. -/
noncomputable def prizeEnvelope (m Cprize : ℝ) : ℝ := Cprize * m * Real.log m

/-- **Degree-2 prize gap.** If the degree-2 autocorrelation envelope is already no larger than
the prize envelope, then the off-diagonal autocorrelation bound `B` must be at most logarithmic
in `m` (up to the harmless factor `m/(m-1)`).  This is the quantitative obstruction behind the
SDP verdict: a natural Weil-scale input `B ~ sqrt m` is far too large in the prize regime. -/
theorem offdiag_le_log_of_degreeTwo_le_prize
    {m B Cprize : ℝ}
    (hm : 1 < m)
    (h : degreeTwoEnvelope m B ≤ prizeEnvelope m Cprize) :
    B ≤ Cprize * (m / (m - 1)) * Real.log m := by
  have hmpos : 0 < m := lt_trans zero_lt_one hm
  have hm1pos : 0 < m - 1 := sub_pos.mpr hm
  have hterm : (m - 1) * B ≤ degreeTwoEnvelope m B := by
    unfold degreeTwoEnvelope
    linarith
  have hmul : (m - 1) * B ≤ Cprize * m * Real.log m :=
    le_trans hterm h
  have hdiv : B ≤ (Cprize * m * Real.log m) / (m - 1) := by
    have hmul' : B * (m - 1) ≤ Cprize * m * Real.log m := by
      nlinarith
    exact (le_div_iff₀ hm1pos).2 hmul'
  calc
    B ≤ (Cprize * m * Real.log m) / (m - 1) := hdiv
    _ = Cprize * (m / (m - 1)) * Real.log m := by field_simp [sub_ne_zero.mpr (ne_of_gt hm)]

/-- **Weil-scale corollary.** If the off-diagonal bound has the natural Weil/Jacobi scale
`B = Cweil * sqrt m`, then any degree-2-SDP proof of the prize forces
`sqrt m <= O(log m)`.  This is false asymptotically for fixed constants, and at the deployed
index `m = 2^128` it is the enormous gap between `2^64` and `128 log 2`. -/
theorem sqrt_le_log_of_weil_scale_degreeTwo_prize
    {m B Cprize Cweil : ℝ}
    (hm : 1 < m) (hCweil : 0 < Cweil)
    (hB : B = Cweil * Real.sqrt m)
    (h : degreeTwoEnvelope m B ≤ prizeEnvelope m Cprize) :
    Real.sqrt m ≤ (Cprize / Cweil) * (m / (m - 1)) * Real.log m := by
  have hlog := offdiag_le_log_of_degreeTwo_le_prize (m := m) (B := B)
    (Cprize := Cprize) hm h
  rw [hB] at hlog
  have hdiv : Real.sqrt m ≤ (Cprize * (m / (m - 1)) * Real.log m) / Cweil := by
    have hmul' : Real.sqrt m * Cweil ≤ Cprize * (m / (m - 1)) * Real.log m := by
      nlinarith
    exact (le_div_iff₀ hCweil).2 hmul'
  calc
    Real.sqrt m ≤ (Cprize * (m / (m - 1)) * Real.log m) / Cweil := hdiv
    _ = (Cprize / Cweil) * (m / (m - 1)) * Real.log m := by ring

/-! ## Axiom audit -/

#print axioms offdiag_le_log_of_degreeTwo_le_prize
#print axioms sqrt_le_log_of_weil_scale_degreeTwo_prize

end ArkLib.ProximityGap.Frontier.AvSDPPrizeGap
