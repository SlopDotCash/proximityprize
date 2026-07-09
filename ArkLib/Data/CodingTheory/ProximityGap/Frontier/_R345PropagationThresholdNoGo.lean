import Mathlib

/-!
# R345: local-variance propagation starts only at the three-quarter scale

For the normalized `H - 1` quotient walk, the period fixed-point identity gives
neighbor mean `(M^2-n)/(n-1)` at a state of height `M`.  If the conditional
standard deviation has its natural scale `sqrt n`, then a constant signal to
noise ratio requires `M^2-n` to have size `(n-1)sqrt n`, hence
`M` has size `n^(3/4)`.  This is polynomially above the prize target
`sqrt(n log m)`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R345PropagationThresholdNoGo

/-- Exact algebraic threshold for the neighbor mean to dominate `c * sqrt n`. -/
theorem neighbor_mean_ge_sqrt_threshold
    {M n c : ℝ} (hn : 1 < n) (hc : 0 ≤ c) :
    c * Real.sqrt n ≤ (M ^ 2 - n) / (n - 1) ↔
      n + c * (n - 1) * Real.sqrt n ≤ M ^ 2 := by
  rw [le_div_iff₀ (sub_pos.mpr hn)]
  constructor <;> intro h <;> nlinarith

/-- At the prize-shaped value `M^2 = C*n*logm`, propagation at natural
`sqrt n` noise would require `sqrt n` to be no larger than a logarithmic
quantity.  This records the exact necessary inequality. -/
theorem prize_scale_propagation_requires_sqrt_le_log
    {n C logm : ℝ} (hn : 1 < n) (hC : 0 ≤ C) (hlog : 0 ≤ logm)
    {M : ℝ} (hM : M ^ 2 = C * n * logm)
    (hprop : Real.sqrt n ≤ (M ^ 2 - n) / (n - 1)) :
    Real.sqrt n ≤ C * logm := by
  have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hn0 : 0 ≤ n := le_trans (by norm_num) (le_of_lt hn)
  have hsqrt_sq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn0
  rw [hM] at hprop
  rw [le_div_iff₀ (sub_pos.mpr hn)] at hprop
  nlinarith

end ArkLib.ProximityGap.Frontier.R345PropagationThresholdNoGo

#print axioms
  ArkLib.ProximityGap.Frontier.R345PropagationThresholdNoGo.neighbor_mean_ge_sqrt_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R345PropagationThresholdNoGo
    .prize_scale_propagation_requires_sqrt_le_log
