import Mathlib

/-!
# R325: additive-Cayley Stein variance contains the period maximum

For an exact-regression exchangeable pair with nonpositive eigenvalue `c`, the
conditional squared-jump proxy already pointwise dominates one quarter of the
square of the observable. Thus a uniform variance-proxy estimate at the prize
scale is not an independent route to the prize bound.
-/

namespace ProximityGap.R325

theorem half_sq_le_steinVariance
    {X PX2 c J V : ℝ}
    (hc : c ≤ 0) (hPX2 : 0 ≤ PX2)
    (hJ : J = PX2 + (1 - 2 * c) * X ^ 2)
    (hV : V = J / (2 * (1 - c))) :
    X ^ 2 / 2 ≤ V := by
  have hden : 0 < 2 * (1 - c) := by linarith
  have hJX : X ^ 2 ≤ J := by
    rw [hJ]
    nlinarith [sq_nonneg X]
  rw [hV]
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg X]

theorem maxPeriod_of_steinVariance
    {X V budget : ℝ}
    (hhalf : X ^ 2 / 2 ≤ V) (hV : V ≤ budget) :
    X ^ 2 ≤ 2 * budget := by
  linarith

end ProximityGap.R325
