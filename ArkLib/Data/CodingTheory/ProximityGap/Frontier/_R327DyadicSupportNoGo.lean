import Mathlib

/-!
# R327: dyadic Fourier-support separation does not imply half-CS

On the cyclic group of order four, let `A = (1,-1,1,-1)` and
`B = (1,1,-1,-1)`.  The first is the coarse frequency two character, while the
second has only odd Fourier frequencies.  Nevertheless `A^2 = B^2 = 1`
pointwise, so their square profiles are identical and the mixed quartic
Cauchy--Schwarz ratio is one, not one half.

Thus valuation-shell separation, even supplemented by reality and mean zero,
cannot by itself supply the live `MixedMainResHalfCS(1/2)` input.  Any winning
argument along this route must use arithmetic constraints on the coefficients.
-/

namespace ProximityGap.R327

/-- Exact four-point countermodel to support-only half-CS decoupling. -/
theorem dyadic_support_separation_half_cs_countermodel :
    let A : Fin 4 -> Real := fun i => ![1, -1, 1, -1] i
    let B : Fin 4 -> Real := fun i => ![1, 1, -1, -1] i
    (sum i, A i) = 0 /\
      (sum i, B i) = 0 /\
      (sum i, (A i) ^ 2 * (B i) ^ 2) = 4 /\
      (sum i, (A i) ^ 4) = 4 /\
      (sum i, (B i) ^ 4) = 4 /\
      (1 / 2 : Real) * Real.sqrt (sum i, (A i) ^ 4) *
          Real.sqrt (sum i, (B i) ^ 4) <
        sum i, (A i) ^ 2 * (B i) ^ 2 := by
  norm_num [Fin.sum_univ_four]

end ProximityGap.R327
