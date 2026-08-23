/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Beyond-Johnson placement of the δ* pin — closing audit disclosure O165-#3

The KKH26 pin (`kkh26_deltaStar_pin_of_censusDomination`) gives `δ* = 1 − r/2^μ` for the
production smooth-domain code `evalCode g n ((r−2)m)` (length `n = 2^μ·m`, dimension
`(r−2)m+1`, rate `ρ`). The independent audit (DISPROOF_LOG O165, disclosure #3) found the
"δ* lies beyond the Johnson radius `1 − √ρ`" placement to be NUMERIC-ONLY (no `Real.sqrt`
comparison in-tree). This file supplies it as a theorem, with NO sqrt gap: via
`Real.lt_sqrt` the placement is EXACTLY the elementary inequality `r²·m < 2^μ·((r−2)m+1)`
(`pin_beyond_johnson_iff`), characteristic-free and decidable. The m=1 NTT/FFT regime
(`pin_beyond_johnson_iff_m1`: `r² < 2^μ(r−1)`) is the FRI/STIR-relevant dyadic case.

Honest scope (matching O165-#3): this is an IFF — the pin is beyond Johnson exactly when
the stated inequality holds. It holds throughout the m=1 production regime but can FAIL at
m≥2 with small r (e.g. μ=2,m=2,r=2 gives pin 1/2 below Johnson) — so "beyond Johnson" is
genuinely conditional, now precisely characterized rather than asserted.
-/

namespace ProximityGap.BeyondJohnson

open Real

/-- **Beyond-Johnson placement of the KKH26 δ* pin, as an exact arithmetic criterion.**
For the production smooth-domain code `evalCode g n ((r-2)m)` (length `n = 2^μ·m`, dimension
`(r-2)m+1`, rate `ρ = ((r-2)m+1)/(2^μ m)`), the pinned threshold `δ* = 1 - r/2^μ`
(`kkh26_deltaStar_pin_of_censusDomination`) lies strictly beyond the Johnson radius
`1 - √ρ` **iff** the elementary inequality `r²·m < 2^μ·((r-2)m+1)` holds — no `Real.sqrt`
gap. Closes audit disclosure O165-#3 (beyond-Johnson was numeric-only): an exact,
decidable, characteristic-free condition. -/
theorem pin_beyond_johnson_iff {μ m r : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r) :
    (1 : ℝ) - (r : ℝ) / 2 ^ μ
        > 1 - Real.sqrt (((r - 2) * m + 1 : ℕ) / ((2 ^ μ * m : ℕ) : ℝ))
      ↔ r ^ 2 * m < 2 ^ μ * ((r - 2) * m + 1) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2m : (0 : ℝ) < (2 : ℝ) ^ μ := by positivity
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hxnn : (0 : ℝ) ≤ ((r' + 2 : ℕ) : ℝ) / 2 ^ μ := by positivity
  rw [gt_iff_lt, sub_lt_sub_iff_left, Real.lt_sqrt hxnn, div_pow]
  have hden : (0 : ℝ) < ((2 ^ μ * m : ℕ) : ℝ) := by push_cast; positivity
  rw [div_lt_div_iff₀ (by positivity) hden]
  push_cast
  rw [pow_two ((2:ℝ)^μ)]
  rw [show ((r':ℝ)+2)^2 * (2^μ * m) = 2^μ * (((r':ℝ)+2)^2 * m) by ring,
     show ((r':ℝ)*m+1) * (2^μ * 2^μ) = 2^μ * (2^μ * ((r':ℝ)*m+1)) by ring,
     mul_lt_mul_iff_of_pos_left h2m]
  constructor
  · intro h; exact_mod_cast h
  · intro h
    have := (Nat.cast_lt (α := ℝ)).mpr h
    push_cast at this; linarith [this]

/-- **m = 1 (NTT/FFT production regime): pin beyond Johnson iff `r² < 2^μ(r-1)`.**
The FRI/STIR-relevant dyadic case (`n = 2^μ`), where the audit's numeric "beyond
Johnson" observation now holds as a theorem under the explicit condition. -/
theorem pin_beyond_johnson_iff_m1 {μ r : ℕ} (hr : 2 ≤ r) :
    (1 : ℝ) - (r : ℝ) / 2 ^ μ
        > 1 - Real.sqrt (((r - 1 : ℕ)) / ((2 ^ μ : ℕ) : ℝ))
      ↔ r ^ 2 < 2 ^ μ * (r - 1) := by
  have he : (r - 2) * 1 + 1 = r - 1 := by omega
  have h := pin_beyond_johnson_iff (μ := μ) (m := 1) (r := r) le_rfl hr
  rw [he] at h
  simpa using h

end ProximityGap.BeyondJohnson
