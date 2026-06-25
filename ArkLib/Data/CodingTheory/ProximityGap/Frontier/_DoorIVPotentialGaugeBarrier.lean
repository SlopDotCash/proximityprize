/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#464)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv): a potential/gauge barrier for dyadic descent

This scratch frontier file records a small obstruction for the remaining Door-IV hope after the
worst-frequency half-mass and gap-combinatorial probes.

The new attempted tool is a *gauge* or *potential* `Phi` for the dyadic recursion.  Instead of trying
to prove a direct contraction

`M_top <= K * M_child`,

one might hope to change variables and prove

`Phi_top <= K * Phi_child`

where `Phi` is comparable to the true magnitude `M`.  The theorem below says exactly how much such a
gauge must distort the magnitude scale.  If the true object already has a per-level floor
`c * M_child <= M_top`, and `Phi_top >= lo * M_top`, `Phi_child <= hi * M_child`, then any claimed
`K`-contraction forces

`lo * c <= K * hi`.

So a normalized potential (`lo = hi = 1`) cannot prove a contraction below the real per-level floor.
In particular, if probes put the floor above the prize `sqrt2` step, a `sqrt2` descent can only be
rescued by a potential whose distortion `hi / lo` is already large enough to hide that excess.  This
does not prove any core cancellation bound; it is a constraint on one possible proof architecture.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVPotentialGaugeBarrier

/-- **Gauge contraction forces distortion.**  Suppose the true magnitudes satisfy a per-level floor
`c * M_child <= M_top`.  Suppose a proposed gauge/potential `Phi` is comparable to true magnitudes by
`lo * M_top <= Phi_top` and `Phi_child <= hi * M_child`.  Then any one-step contraction
`Phi_top <= K * Phi_child` forces `lo * c <= K * hi`.

This is the exact obstruction for a Door-IV potential method: improving the recursive factor `K`
below the measured magnitude floor `c` requires paying for it in the gauge distortion `hi / lo`. -/
theorem gauge_contraction_forces_distortion
    {M_top M_child Phi_top Phi_child c K lo hi : ℝ}
    (hchild : 0 < M_child) (hlo : 0 < lo) (hK : 0 ≤ K)
    (hfloor : c * M_child ≤ M_top)
    (hPhi_top : lo * M_top ≤ Phi_top)
    (hPhi_child : Phi_child ≤ hi * M_child)
    (hcontract : Phi_top ≤ K * Phi_child) :
    lo * c ≤ K * hi := by
  have hchain : (lo * c) * M_child ≤ (K * hi) * M_child := by
    calc
      (lo * c) * M_child = lo * (c * M_child) := by ring
      _ ≤ lo * M_top := mul_le_mul_of_nonneg_left hfloor (le_of_lt hlo)
      _ ≤ Phi_top := hPhi_top
      _ ≤ K * Phi_child := hcontract
      _ ≤ K * (hi * M_child) := mul_le_mul_of_nonneg_left hPhi_child hK
      _ = (K * hi) * M_child := by ring
  exact le_of_mul_le_mul_right hchain hchild

/-- **Contrapositive form.**  If `K * hi < lo * c`, then no gauge satisfying the stated comparison
bounds can prove `Phi_top <= K * Phi_child`. -/
theorem no_gauge_contraction_below_distorted_floor
    {M_top M_child Phi_top Phi_child c K lo hi : ℝ}
    (hchild : 0 < M_child) (hlo : 0 < lo) (hK : 0 ≤ K)
    (hfloor : c * M_child ≤ M_top)
    (hPhi_top : lo * M_top ≤ Phi_top)
    (hPhi_child : Phi_child ≤ hi * M_child)
    (hbad : K * hi < lo * c) :
    ¬ Phi_top ≤ K * Phi_child := by
  intro hcontract
  exact (not_lt_of_ge
    (gauge_contraction_forces_distortion hchild hlo hK hfloor hPhi_top hPhi_child hcontract))
    hbad

/-- **Normalized gauges cannot beat the true floor.**  If the gauge has no scale distortion
(`M_top <= Phi_top`, `Phi_child <= M_child`), every one-step `K`-contraction forces `c <= K`. -/
theorem normalized_contraction_forces_K_ge_floor
    {M_top M_child Phi_top Phi_child c K : ℝ}
    (hchild : 0 < M_child) (hK : 0 ≤ K)
    (hfloor : c * M_child ≤ M_top)
    (hPhi_top : M_top ≤ Phi_top)
    (hPhi_child : Phi_child ≤ M_child)
    (hcontract : Phi_top ≤ K * Phi_child) :
    c ≤ K := by
  have h := gauge_contraction_forces_distortion
    (M_top := M_top) (M_child := M_child) (Phi_top := Phi_top) (Phi_child := Phi_child)
    (c := c) (K := K) (lo := 1) (hi := 1)
    hchild (by norm_num) hK
    (by simpa using hfloor)
    (by simpa using hPhi_top)
    (by simpa using hPhi_child)
    hcontract
  simpa using h

/-- **Prize-threshold version.**  A normalized gauge cannot prove a `sqrtTwo`-step contraction if the
actual per-level floor `c` is strictly larger than `sqrtTwo`.  The name `sqrtTwo` is just a real
parameter; downstream files can instantiate it with `Real.sqrt 2`. -/
theorem no_normalized_sqrt_two_contraction
    {M_top M_child Phi_top Phi_child c sqrtTwo : ℝ}
    (hchild : 0 < M_child) (hsqrtTwo : 0 ≤ sqrtTwo)
    (hfloor : c * M_child ≤ M_top)
    (hPhi_top : M_top ≤ Phi_top)
    (hPhi_child : Phi_child ≤ M_child)
    (hgt : sqrtTwo < c) :
    ¬ Phi_top ≤ sqrtTwo * Phi_child := by
  intro hcontract
  have hle := normalized_contraction_forces_K_ge_floor
    (M_top := M_top) (M_child := M_child) (Phi_top := Phi_top) (Phi_child := Phi_child)
    (c := c) (K := sqrtTwo)
    hchild hsqrtTwo hfloor hPhi_top hPhi_child hcontract
  exact (not_lt_of_ge hle) hgt

/-- **How much distortion a gauge must pay.**  If a proof wants a contraction factor `K` below a true
floor `c`, then any successful gauge comparison must have `hi / lo >= c / K`; multiplication form
avoids division and is usable when `K` or `lo` are later instantiated by awkward constants. -/
theorem gauge_distortion_must_cover_floor
    {M_top M_child Phi_top Phi_child c K lo hi : ℝ}
    (hchild : 0 < M_child) (hlo : 0 < lo) (hK : 0 ≤ K)
    (hfloor : c * M_child ≤ M_top)
    (hPhi_top : lo * M_top ≤ Phi_top)
    (hPhi_child : Phi_child ≤ hi * M_child)
    (hcontract : Phi_top ≤ K * Phi_child) :
    c * lo ≤ hi * K := by
  have h := gauge_contraction_forces_distortion hchild hlo hK hfloor hPhi_top hPhi_child hcontract
  linarith

end ArkLib.ProximityGap.Frontier.DoorIVPotentialGaugeBarrier

#print axioms ArkLib.ProximityGap.Frontier.DoorIVPotentialGaugeBarrier.gauge_contraction_forces_distortion
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPotentialGaugeBarrier.no_gauge_contraction_below_distorted_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPotentialGaugeBarrier.normalized_contraction_forces_K_ge_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPotentialGaugeBarrier.no_normalized_sqrt_two_contraction
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPotentialGaugeBarrier.gauge_distortion_must_cover_floor
