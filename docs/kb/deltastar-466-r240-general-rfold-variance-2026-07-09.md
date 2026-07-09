# R240: general r-fold variance identity

Issue: #466. Date: 2026-07-09.

## Context

Rounds 55--57 rewrote the depth-3 DC-subtracted energy as the flatness
variance of the 3-fold additive representation function:

```text
rep3 G c = #{(x1,x2,x3) in G^3 : x1+x2+x3 = c}
```

That was structurally useful, but the prize wall is not depth 3.  It is the
joint limit at logarithmic depth.

## Lean socket

New file:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R240GeneralRFoldVariance.lean
```

It introduces the arbitrary-depth representation function:

```text
repR G r c = #{v : G^r | sum_i v_i = c}
```

and proves:

```text
sum_vectors_weight
sum_repR
rEnergy_eq_sum_repR_sq
variance_identity
dc_floor
dcEnergyBound_iff_variance
dcEnergyBound_iff_dcGap_bound
dcEnergyBound_of_dcGap_bound
dcGap_bound_of_dcEnergyBound
not_dcEnergyBound_of_dcGap_gt
not_dcEnergyBound_of_dcGap_lower_bound_gt
DCEnergyBoundWithConstant
DCEnergyWallWithConstant
DCEnergyWallWithConstantUpTo
DCEnergyCeilWallWithConstant
dcEnergyBoundWithConstant_one_iff
dcEnergyBoundWithConstant_one_of_dcEnergyBound
dcEnergyBound_of_dcEnergyBoundWithConstant_one
dcEnergyBoundWithConstant_iff_sum_nonzero_moment
dcEnergyBound_iff_sum_nonzero_moment
dcEnergyWallWithConstant_iff_forall_sum_nonzero_moment
dcEnergyWallWithConstantUpTo_iff_forall_sum_nonzero_moment
dcEnergyCeilWallWithConstant_iff_sum_nonzero_moment
dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_bound
dcEnergyWall_iff_forall_sum_nonzero_moment
not_dcEnergyWallWithConstant_of_sum_nonzero_moment_gt
not_dcEnergyWallWithConstant_of_sum_nonzero_moment_lower_bound_gt
not_dcEnergyWallWithConstantUpTo_of_sum_nonzero_moment_gt
not_dcEnergyWallWithConstantUpTo_of_sum_nonzero_moment_lower_bound_gt
not_dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_gt
not_dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_lower_bound_gt
eta_pow_le_of_dcEnergyBoundWithConstant
eta_sq_le_dcOptimizedWithConstant
eta_le_sqrt_floor_of_dcEnergyBoundWithConstant
eta_le_sqrt_floor_of_dcEnergyWallWithConstant
forall_eta_le_sqrt_floor_of_dcEnergyWallWithConstant
eta_le_sqrt_floor_of_dcEnergyWallWithConstantUpTo
forall_eta_le_sqrt_floor_of_dcEnergyWallWithConstantUpTo
eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant
forall_eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant
DCEnergyBoundWithConstant.mono_pow
DCEnergyBoundWithConstant.mono
dcEnergyBoundWithConstant_of_dcEnergyBound_of_one_le
dcEnergyWallWithConstant_one_iff
DCEnergyWallWithConstant.mono_pow
DCEnergyWallWithConstant.mono
dcEnergyWallWithConstant_of_dcEnergyWall_of_one_le
DCEnergyWallWithConstant.to_upTo
DCEnergyWallWithConstantUpTo.mono_depth
DCEnergyWallWithConstantUpTo.mono_pow
DCEnergyWallWithConstant.to_ceil
DCEnergyWallWithConstantUpTo.to_ceil
dcEnergyCeilWallWithConstant_one_iff
DCEnergyCeilWallWithConstant.mono_pow
DCEnergyCeilWallWithConstant.mono
dcEnergyCeilWallWithConstant_of_dcEnergyBound_of_one_le
dcEnergyWallWithConstantUpTo_one_iff
dcEnergyWallWithConstantUpTo_of_dcEnergyWallUpTo_of_one_le
dcEnergyBound_of_variance
variance_bound_of_dcEnergyBound
deviationR
sum_deviationR_sq_eq_card_mul_dcGap
dcGap_eq_sum_deviationR_sq_div_card
sum_deviationR_zero
repR_smul
varianceSummand_smul
deviationR_smul
centeredRepR_smul
repR_sub_mean_smul
deficit_ge_orbit
centered_deficit_ge_orbit
repR_sub_mean_variance_ge_orbit
energy_ge_orbit
orbit_deviation_budget_of_dcEnergyBound
deviation_sq_le_of_dcEnergyBound
normalized_deviation_sq_le_of_dcEnergyBound
normalized_variance_bound_of_dcEnergyBound
dcEnergyBound_iff_normalized_variance
centeredRepR
centeredRepR_eq_deviation_div
deviationR_eq_card_mul_centeredRepR
deviationR_sq_eq_card_sq_mul_centeredRepR_sq
abs_deviationR_eq_card_mul_abs_centeredRepR
centeredRepR_eq_repR_sub_mean
centeredRepR_sq_eq_repR_sub_mean_sq
abs_centeredRepR_eq_abs_repR_sub_mean
sum_centeredRepR_zero
sum_repR_sub_mean_zero
sum_centeredRepR_sq_eq_normalized_variance
sum_repR_sub_mean_sq_eq_normalized_variance
sum_deviationR_sq_eq_card_sq_mul_sum_centeredRepR_sq
sum_deviationR_sq_eq_card_sq_mul_sum_repR_sub_mean_sq
dcGap_eq_card_mul_sum_centeredRepR_sq
dcGap_eq_card_mul_sum_repR_sub_mean_sq
dcEnergyBoundWithConstant_iff_centeredRepR_variance
dcEnergyBoundWithConstant_iff_repR_sub_mean_variance
deviation_variance_bound_iff_centered_variance_bound
deviation_variance_bound_iff_repR_sub_mean_variance_bound
dcEnergyBoundWithConstant_iff_deviation_variance
dcEnergyCeilWallWithConstant_iff_centeredRepR_variance
dcEnergyCeilWallWithConstant_iff_repR_sub_mean_variance
dcEnergyCeilWallWithConstant_iff_deviation_variance
dcEnergyCeilWallWithConstant_of_centered_variance_bound
dcEnergyCeilWallWithConstant_of_repR_sub_mean_variance_bound
dcEnergyCeilWallWithConstant_of_deviation_variance_bound
dcEnergyWallWithConstant_iff_forall_centeredRepR_variance
dcEnergyWallWithConstant_iff_forall_repR_sub_mean_variance
dcEnergyWallWithConstant_iff_forall_deviation_variance
dcEnergyWallWithConstantUpTo_iff_forall_centeredRepR_variance
dcEnergyWallWithConstantUpTo_iff_forall_repR_sub_mean_variance
dcEnergyWallWithConstantUpTo_iff_forall_deviation_variance
not_dcEnergyWallWithConstant_of_centered_variance_gt
not_dcEnergyWallWithConstant_of_centered_variance_lower_bound_gt
not_dcEnergyWallWithConstant_of_repR_sub_mean_variance_gt
not_dcEnergyWallWithConstant_of_deviation_variance_gt
not_dcEnergyWallWithConstantUpTo_of_centered_variance_gt
not_dcEnergyWallWithConstantUpTo_of_centered_variance_lower_bound_gt
not_dcEnergyWallWithConstantUpTo_of_repR_sub_mean_variance_gt
not_dcEnergyWallWithConstantUpTo_of_deviation_variance_gt
not_dcEnergyCeilWallWithConstant_of_centered_variance_gt
not_dcEnergyCeilWallWithConstant_of_centered_variance_lower_bound_gt
not_dcEnergyCeilWallWithConstant_of_repR_sub_mean_variance_gt
not_dcEnergyCeilWallWithConstant_of_deviation_variance_gt
dcEnergyBoundWithConstant_of_deviation_variance_bound
not_dcEnergyBoundWithConstant_of_deviation_variance_gt
not_dcEnergyBoundWithConstant_of_deviation_variance_lower_bound_gt
dcEnergyBoundWithConstant_of_centered_variance_bound
dcEnergyBoundWithConstant_of_repR_sub_mean_variance_bound
not_dcEnergyBoundWithConstant_of_centered_variance_gt
not_dcEnergyBoundWithConstant_of_repR_sub_mean_variance_gt
not_dcEnergyBoundWithConstant_of_centered_variance_lower_bound_gt
not_dcEnergyBoundWithConstant_of_repR_sub_mean_variance_lower_bound_gt
centered_variance_bound_of_deviation_variance_bound
deviation_variance_bound_of_centered_variance_bound
repR_sub_mean_variance_bound_of_deviation_variance_bound
deviation_variance_bound_of_repR_sub_mean_variance_bound
sum_centeredRepR_sq_eq_sum_repR_sub_mean_sq
centered_variance_bound_iff_repR_sub_mean_variance_bound
dcEnergyBound_iff_centeredRepR_variance
centered_variance_bound_of_dcEnergyBound
dcEnergyBound_of_centered_variance
not_dcEnergyBound_of_centered_variance_gt
not_dcEnergyBound_of_centered_variance_lower_bound_gt
dcEnergyBound_iff_repR_sub_mean_variance
repR_sub_mean_variance_bound_of_dcEnergyBound
dcEnergyBound_of_repR_sub_mean_variance
not_dcEnergyBound_of_repR_sub_mean_variance_gt
not_dcEnergyBound_of_repR_sub_mean_variance_lower_bound_gt
dcEnergyBound_of_repR_sub_mean_variance_bound
dcEnergyBound_iff_deviation_variance
dcEnergyBound_of_deviation_variance
dcEnergyBound_of_deviation_variance_bound
deviation_variance_bound_of_dcEnergyBound
not_dcEnergyBound_of_deviation_variance_gt
not_dcEnergyBound_of_deviation_variance_lower_bound_gt
centered_sq_le_of_centered_variance_bound_global
abs_centeredRepR_le_sqrt_of_centered_variance_bound_global
repR_sub_mean_sq_le_of_centered_variance_bound_global
repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound_global
abs_repR_sub_mean_le_sqrt_of_centered_variance_bound_global
abs_repR_sub_mean_le_sqrt_of_repR_sub_mean_variance_bound_global
card_filter_abs_centeredRepR_ge_le_variance_div
card_filter_abs_centeredRepR_ge_le_of_centered_variance_bound
card_filter_abs_centeredRepR_ge_le_of_dcEnergyBound
card_filter_nonzero_abs_centeredRepR_ge_le_of_centered_variance_bound
card_filter_nonzero_abs_centeredRepR_ge_le_of_dcEnergyBound
card_filter_abs_repR_sub_mean_ge_le_of_centered_variance_bound
card_filter_abs_repR_sub_mean_ge_le_of_repR_sub_mean_variance_bound
card_filter_abs_repR_sub_mean_ge_le_of_dcEnergyBound
card_filter_nonzero_abs_repR_sub_mean_ge_le_of_centered_variance_bound
card_filter_nonzero_abs_repR_sub_mean_ge_le_of_repR_sub_mean_variance_bound
card_filter_nonzero_abs_repR_sub_mean_ge_le_of_dcEnergyBound
centered_sq_le_of_dcEnergyBound_global
abs_centeredRepR_le_sqrt_of_dcEnergyBound_global
repR_sub_mean_sq_le_of_dcEnergyBound_global
abs_repR_sub_mean_le_sqrt_of_dcEnergyBound_global
centered_orbit_budget_of_centered_variance_bound
repR_sub_mean_orbit_budget_of_centered_variance_bound
repR_sub_mean_orbit_budget_of_repR_sub_mean_variance_bound
not_centered_variance_bound_of_repR_sub_mean_orbit_budget_gt
not_repR_sub_mean_variance_bound_of_orbit_budget_gt
orbit_budget_of_large_abs_centeredRepR
orbit_budget_of_large_abs_centeredRepR_of_dcEnergyBound
not_dcEnergyBound_of_large_abs_centeredRepR
no_large_abs_centeredRepR_of_dcEnergyBound
orbit_budget_of_large_abs_repR_sub_mean
orbit_budget_of_large_abs_repR_sub_mean_of_repR_sub_mean_variance_bound
no_large_abs_repR_sub_mean_of_repR_sub_mean_variance_bound
no_large_abs_repR_sub_mean_of_centered_variance_bound
orbit_budget_of_large_abs_repR_sub_mean_of_dcEnergyBound
not_dcEnergyBound_of_large_abs_repR_sub_mean
no_large_abs_repR_sub_mean_of_dcEnergyBound
centered_sq_le_of_centered_variance_bound
abs_centeredRepR_le_sqrt_of_centered_variance_bound
centered_orbit_budget_of_dcEnergyBound
centered_sq_le_of_dcEnergyBound
repR_sub_mean_sq_le_of_centered_variance_bound
abs_repR_sub_mean_le_sqrt_of_centered_variance_bound
repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound
repR_sub_mean_sq_le_of_dcEnergyBound
abs_centeredRepR_le_sqrt_of_dcEnergyBound
abs_repR_sub_mean_le_sqrt_of_repR_sub_mean_variance_bound
forall_nonzero_centered_sq_le_of_dcEnergyBound
forall_nonzero_abs_repR_sub_mean_le_sqrt_of_centered_variance_bound
forall_nonzero_repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound
forall_nonzero_repR_sub_mean_sq_le_of_dcEnergyBound
repR_sub_mean_orbit_budget_of_dcEnergyBound
not_dcEnergyBound_of_repR_sub_mean_orbit_budget_gt
forall_nonzero_repR_sub_mean_orbit_budget_of_dcEnergyBound
forall_nonzero_abs_centeredRepR_le_sqrt_of_dcEnergyBound
forall_nonzero_abs_repR_sub_mean_le_sqrt_of_repR_sub_mean_variance_bound
abs_repR_sub_mean_le_sqrt_of_dcEnergyBound
forall_nonzero_abs_repR_sub_mean_le_sqrt_of_dcEnergyBound
centered_variance_bound_of_uniform_abs_centeredRepR
dcEnergyBound_of_uniform_abs_centeredRepR
centered_variance_bound_of_uniform_abs_repR_sub_mean
repR_sub_mean_variance_bound_of_uniform_abs_repR_sub_mean
dcEnergyBound_of_uniform_abs_repR_sub_mean
centered_variance_bound_of_zero_and_nonzero_abs_centeredRepR
dcEnergyBound_of_zero_and_nonzero_abs_centeredRepR
centered_variance_bound_of_zero_and_nonzero_abs_repR_sub_mean
repR_sub_mean_variance_bound_of_zero_and_nonzero_abs_repR_sub_mean
dcEnergyBound_of_zero_and_nonzero_abs_repR_sub_mean
abs_centeredRepR_zero_le_card_sub_one_mul_of_nonzero_abs
abs_repR_sub_mean_zero_le_card_sub_one_mul_of_nonzero_abs
repR_sub_mean_zero_sq_le_card_sub_one_mul_sq_of_nonzero_abs
centered_variance_bound_of_nonzero_abs_centeredRepR
dcEnergyBound_of_nonzero_abs_centeredRepR
centered_variance_bound_of_nonzero_abs_repR_sub_mean
repR_sub_mean_variance_bound_of_nonzero_abs_repR_sub_mean
dcEnergyBound_of_nonzero_abs_repR_sub_mean
```

The main identity is:

```text
sum_c (q * repR G r c - |G|^r)^2
  = q * (q * rEnergy G r - |G|^(2*r)).

Equivalently, in named deviation language:

sum_c deviationR(G,r,c)^2
  = q * (q * rEnergy G r - |G|^(2*r)).

q * rEnergy G r - |G|^(2*r)
  = sum_c deviationR(G,r,c)^2 / q.

q * rEnergy G r - |G|^(2*r)
  = q * sum_c centeredRepR(G,r,c)^2.

q * rEnergy G r - |G|^(2*r)
  = q * sum_c (repR(G,r,c) - |G|^r/q)^2.
```

The original DC-gap form is also named directly:

```text
DCEnergyBound G r
  iff
q * rEnergy G r - |G|^(2*r)
  <= q * (2r-1)!! * |G|^r.

q * rEnergy G r - |G|^(2*r) <= B
  and B <= q * (2r-1)!! * |G|^r
  -> DCEnergyBound G r.

q * (2r-1)!! * |G|^r < q * rEnergy G r - |G|^(2*r)
  -> not DCEnergyBound G r.

B <= q * rEnergy G r - |G|^(2*r)
  and q * (2r-1)!! * |G|^r < B
  -> not DCEnergyBound G r.
```

The dossier's constant-power form is available as:

```text
DCEnergyBoundWithConstant G r K
  := q * rEnergy G r - |G|^(2*r)
       <= q * (K^r * (2r-1)!! * |G|^r).

DCEnergyWallWithConstant G K
  := forall r, DCEnergyBoundWithConstant G r K.

DCEnergyWallWithConstantUpTo G K R
  := forall r <= R, DCEnergyBoundWithConstant G r K.

DCEnergyCeilWallWithConstant G K
  := DCEnergyBoundWithConstant G ceil(log q) K.

DCEnergyBoundWithConstant G r 1 iff DCEnergyBound G r.

DCEnergyWallWithConstant G 1 iff forall r, DCEnergyBound G r.

DCEnergyWallWithConstantUpTo G 1 R iff forall r <= R, DCEnergyBound G r.

DCEnergyCeilWallWithConstant G 1 iff DCEnergyBound G ceil(log q).

DCEnergyBoundWithConstant G r K
  iff
sum_{b != 0} |eta_b(G)|^(2r)
  <= q * K^r * (2r-1)!! * |G|^r.

DCEnergyBound G r
  iff
sum_{b != 0} |eta_b(G)|^(2r)
  <= q * (2r-1)!! * |G|^r.

DCEnergyWallWithConstant G K
  iff
forall r,
  sum_{b != 0} |eta_b(G)|^(2r)
    <= q * K^r * (2r-1)!! * |G|^r.

DCEnergyWallWithConstantUpTo G K R
  iff
forall r <= R,
  sum_{b != 0} |eta_b(G)|^(2r)
    <= q * K^r * (2r-1)!! * |G|^r.

DCEnergyCeilWallWithConstant G K
  iff
sum_{b != 0} |eta_b(G)|^(2 ceil(log q))
  <= q * K^(ceil(log q)) * (2 ceil(log q)-1)!! * |G|^(ceil(log q)).

The right-hand side moment inequality directly proves
DCEnergyCeilWallWithConstant G K.

q * K^(ceil(log q)) * (2 ceil(log q)-1)!! * |G|^(ceil(log q))
  < sum_{b != 0} |eta_b(G)|^(2 ceil(log q))
  -> not DCEnergyCeilWallWithConstant G K.

forall r, DCEnergyBound G r
  iff
forall r,
  sum_{b != 0} |eta_b(G)|^(2r)
    <= q * (2r-1)!! * |G|^r.

q * K^r * (2r-1)!! * |G|^r
  < sum_{b != 0} |eta_b(G)|^(2r)
  -> not DCEnergyWallWithConstant G K.

If r <= R, then
q * K^r * (2r-1)!! * |G|^r
  < sum_{b != 0} |eta_b(G)|^(2r)
  -> not DCEnergyWallWithConstantUpTo G K R.

DCEnergyBoundWithConstant G r K and K^r <= K'^r
  -> DCEnergyBoundWithConstant G r K'.

DCEnergyBoundWithConstant G r K and 0 <= K and K <= K'
  -> DCEnergyBoundWithConstant G r K'.

DCEnergyBound G r and 1 <= K
  -> DCEnergyBoundWithConstant G r K.

DCEnergyWallWithConstant G K and forall r, K^r <= K'^r
  -> DCEnergyWallWithConstant G K'.

DCEnergyWallWithConstant G K and 0 <= K and K <= K'
  -> DCEnergyWallWithConstant G K'.

(forall r, DCEnergyBound G r) and 1 <= K
  -> DCEnergyWallWithConstant G K.

(forall r <= R, DCEnergyBound G r) and 1 <= K
  -> DCEnergyWallWithConstantUpTo G K R.

DCEnergyBound G ceil(log q) and 1 <= K
  -> DCEnergyCeilWallWithConstant G K.

DCEnergyBoundWithConstant G r K
  -> |eta_b(G)|^(2r) <= q * K^r * (2r-1)!! * |G|^r, b != 0.

DCEnergyBoundWithConstant G r K and r >= 1 and log q <= r and 0 <= K
  -> |eta_b(G)|^2 <= 2e * K * |G| * r, b != 0.

DCEnergyBoundWithConstant G ceil(log q) K and 0 <= K
  -> |eta_b(G)| <= sqrt(2e * K * |G| * (log q + 1)), b != 0.

DCEnergyWallWithConstant G K and q >= e and 0 <= K
  -> forall b != 0,
     |eta_b(G)| <= sqrt(2e * K * |G| * (log q + 1)).

DCEnergyWallWithConstantUpTo G K R and ceil(log q) <= R and q >= e and 0 <= K
  -> forall b != 0,
     |eta_b(G)| <= sqrt(2e * K * |G| * (log q + 1)).

DCEnergyCeilWallWithConstant G K and q >= e and 0 <= K
  -> forall b != 0,
     |eta_b(G)| <= sqrt(2e * K * |G| * (log q + 1)).

DCEnergyBoundWithConstant G r K
  iff
sum_c centeredRepR(G,r,c)^2
  <= K^r * (2r-1)!! * |G|^r.

DCEnergyWallWithConstant G K
  iff
forall r,
  sum_c centeredRepR(G,r,c)^2
    <= K^r * (2r-1)!! * |G|^r.

DCEnergyWallWithConstantUpTo G K R
  iff
forall r <= R,
  sum_c centeredRepR(G,r,c)^2
    <= K^r * (2r-1)!! * |G|^r.

DCEnergyCeilWallWithConstant G K
  iff
sum_c centeredRepR(G,ceil(log q),c)^2
  <= K^(ceil(log q)) * (2 ceil(log q)-1)!! * |G|^(ceil(log q)).

DCEnergyBoundWithConstant G r K
  iff
sum_c (repR(G,r,c) - |G|^r/q)^2
  <= K^r * (2r-1)!! * |G|^r.

DCEnergyWallWithConstant G K
  iff
forall r,
  sum_c (repR(G,r,c) - |G|^r/q)^2
    <= K^r * (2r-1)!! * |G|^r.

DCEnergyWallWithConstantUpTo G K R
  iff
forall r <= R,
  sum_c (repR(G,r,c) - |G|^r/q)^2
    <= K^r * (2r-1)!! * |G|^r.

DCEnergyCeilWallWithConstant G K
  iff
sum_c (repR(G,ceil(log q),c) - |G|^(ceil(log q))/q)^2
  <= K^(ceil(log q)) * (2 ceil(log q)-1)!! * |G|^(ceil(log q)).

DCEnergyBoundWithConstant G r K
  iff
sum_c deviationR(G,r,c)^2
  <= q^2 * K^r * (2r-1)!! * |G|^r.

DCEnergyWallWithConstant G K
  iff
forall r,
  sum_c deviationR(G,r,c)^2
    <= q^2 * K^r * (2r-1)!! * |G|^r.

DCEnergyWallWithConstantUpTo G K R
  iff
forall r <= R,
  sum_c deviationR(G,r,c)^2
    <= q^2 * K^r * (2r-1)!! * |G|^r.

DCEnergyCeilWallWithConstant G K
  iff
sum_c deviationR(G,ceil(log q),c)^2
  <= q^2 * K^(ceil(log q)) * (2 ceil(log q)-1)!! * |G|^(ceil(log q)).

The corresponding centered / raw repR-sub-mean / deviation upper bounds at
r = ceil(log q) directly prove DCEnergyCeilWallWithConstant G K.

The corresponding over-budget centered / raw repR-sub-mean / deviation
inequalities at r = ceil(log q) refute DCEnergyCeilWallWithConstant G K.

K^r * (2r-1)!! * |G|^r
  < sum_c centeredRepR(G,r,c)^2
  -> not DCEnergyWallWithConstant G K.

K^r * (2r-1)!! * |G|^r
  < sum_c (repR(G,r,c) - |G|^r/q)^2
  -> not DCEnergyWallWithConstant G K.

q^2 * K^r * (2r-1)!! * |G|^r
  < sum_c deviationR(G,r,c)^2
  -> not DCEnergyWallWithConstant G K.

If r <= R, the same centered/repR-sub-mean/deviation inequalities refute
DCEnergyWallWithConstantUpTo G K R.

sum_c deviationR(G,r,c)^2 <= B
  and B <= q^2 * K^r * (2r-1)!! * |G|^r
  -> DCEnergyBoundWithConstant G r K.

q^2 * K^r * (2r-1)!! * |G|^r < sum_c deviationR(G,r,c)^2
  -> not DCEnergyBoundWithConstant G r K.

sum_c centeredRepR(G,r,c)^2 <= B
  and B <= K^r * (2r-1)!! * |G|^r
  -> DCEnergyBoundWithConstant G r K.

sum_c (repR(G,r,c) - |G|^r/q)^2 <= B
  and B <= K^r * (2r-1)!! * |G|^r
  -> DCEnergyBoundWithConstant G r K.

K^r * (2r-1)!! * |G|^r < sum_c centeredRepR(G,r,c)^2
  -> not DCEnergyBoundWithConstant G r K.

K^r * (2r-1)!! * |G|^r
    < sum_c (repR(G,r,c) - |G|^r/q)^2
  -> not DCEnergyBoundWithConstant G r K.
```

This is the exact arbitrary-depth analogue of the R55 depth-3 identity.  The
file also proves multiplicative invariance for subgroup-shaped `G`:

```text
repR G r (a*c) = repR G r c,  a in G,
repR G r (a*c) - |G|^r/q = repR G r c - |G|^r/q,  a in G,
```

so the deep flatness summand is constant on multiplicative `G`-orbits, matching
the R56/R57 coset normalization at every depth.

The strengthened consumer theorem is:

```text
DCEnergyBound G r
  iff
sum_c (q * repR G r c - |G|^r)^2
  <= q^2 * (2r-1)!! * |G|^r.
```

Thus any future equidistribution/large-sieve estimate on the `r`-fold
representation function can feed the existing corrected moment stack directly.
At ceiling depth the direct consumers
`forall_eta_le_sqrt_floor_of_sum_nonzero_moment_bound`,
`forall_eta_le_sqrt_floor_of_centered_variance_bound`,
`forall_eta_le_sqrt_floor_of_repR_sub_mean_variance_bound`, and
`forall_eta_le_sqrt_floor_of_deviation_variance_bound` now turn those estimates
into the final optimized nonzero-frequency bound without an extra manual bridge.

Finally, the file ports the R57 orbit-multiplicity argument to every depth:

```text
|G| * deviationR(G,r,b)^2 <= sum_c deviationR(G,r,c)^2
```

for `b != 0` and subgroup-shaped `G`.  In energy form this becomes:

```text
|G| * deviationR(G,r,b)^2
  <= q * (q * rEnergy G r - |G|^(2*r)).
```

So one large flatness deviation forces a whole multiplicative orbit of
variance at logarithmic depth as well, not only at depth 3.

Composing this with `DCEnergyBound` gives the pointwise budget:

```text
|G| * deviationR(G,r,b)^2
  <= q^2 * (2r-1)!! * |G|^r
```

and, when `G` is nonempty, the divided form:

```text
deviationR(G,r,b)^2
  <= q^2 * (2r-1)!! * |G|^r / |G|.
```

This is the expected `/ |G|` orbit-saving in the pointwise deviation language.
The normalized version also lands:

```text
deviationR(G,r,b)^2 / q^2
  <= (2r-1)!! * |G|^r / |G|.
```

This is the flatness/probability scale for future large-deviation inputs.
The global normalized form is also available:

```text
sum_c deviationR(G,r,c)^2 / q^2
  <= (2r-1)!! * |G|^r.
```

So `DCEnergyBound` is now exposed both as a raw variance inequality and as a
probability-scale flatness bound.  The probability-scale form is an iff:

```text
DCEnergyBound G r
  iff
sum_c deviationR(G,r,c)^2 / q^2
  <= (2r-1)!! * |G|^r.
```

The same statement is now available in the centered representation language:

```text
centeredRepR(G,r,c) = repR(G,r,c) - |G|^r / q.
```

This centered function is mean-zero, equals `deviationR(G,r,c) / q`, and has
the same square-sum as the normalized deviation variance.  The consumer-facing
iff is:

```text
deviationR(G,r,c) = q * centeredRepR(G,r,c)

deviationR(G,r,c)^2 = q^2 * centeredRepR(G,r,c)^2

|deviationR(G,r,c)| = q * |centeredRepR(G,r,c)|

DCEnergyBound G r
  iff
sum_c centeredRepR(G,r,c)^2
  <= (2r-1)!! * |G|^r.
```

Equivalently, the centered alias can now be avoided entirely:

```text
sum_c (repR(G,r,c) - |G|^r / q) = 0.
```

and

```text
centeredRepR(G,r,c) = repR(G,r,c) - |G|^r / q.

centeredRepR(G,r,c)^2 = (repR(G,r,c) - |G|^r / q)^2.

|centeredRepR(G,r,c)| = |repR(G,r,c) - |G|^r / q|.

sum_c (repR(G,r,c) - |G|^r / q)^2
  = sum_c deviationR(G,r,c)^2 / q^2.

sum_c deviationR(G,r,c)^2
  = q^2 * sum_c centeredRepR(G,r,c)^2.

sum_c deviationR(G,r,c)^2
  = q^2 * sum_c (repR(G,r,c) - |G|^r / q)^2.

sum_c deviationR(G,r,c)^2 <= q^2 * B
  iff
sum_c centeredRepR(G,r,c)^2 <= B.

sum_c deviationR(G,r,c)^2 <= q^2 * B
  iff
sum_c (repR(G,r,c) - |G|^r / q)^2 <= B.

sum_c deviationR(G,r,c)^2 <= q^2 * B
  -> sum_c centeredRepR(G,r,c)^2 <= B.

sum_c centeredRepR(G,r,c)^2 <= B
  -> sum_c deviationR(G,r,c)^2 <= q^2 * B.

sum_c deviationR(G,r,c)^2 <= q^2 * B
  -> sum_c (repR(G,r,c) - |G|^r / q)^2 <= B.

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  -> sum_c deviationR(G,r,c)^2 <= q^2 * B.

sum_c centeredRepR(G,r,c)^2
  = sum_c (repR(G,r,c) - |G|^r / q)^2.

sum_c centeredRepR(G,r,c)^2 <= B
  iff
sum_c (repR(G,r,c) - |G|^r / q)^2 <= B.
```

```text
DCEnergyBound G r
  iff
sum_c (repR(G,r,c) - |G|^r / q)^2
  <= (2r-1)!! * |G|^r.

DCEnergyBound G r
  iff
sum_c deviationR(G,r,c)^2
  <= q^2 * (2r-1)!! * |G|^r.

DCEnergyBound G r
  -> sum_c deviationR(G,r,c)^2 <= q^2 * (2r-1)!! * |G|^r.

q^2 * (2r-1)!! * |G|^r < sum_c deviationR(G,r,c)^2
  -> not DCEnergyBound G r.

(2r-1)!! * |G|^r < sum_c centeredRepR(G,r,c)^2
  -> not DCEnergyBound G r.

(2r-1)!! * |G|^r < sum_c (repR(G,r,c) - |G|^r/q)^2
  -> not DCEnergyBound G r.

B <= sum_c deviationR(G,r,c)^2
  and q^2 * (2r-1)!! * |G|^r < B
  -> not DCEnergyBound G r.

B <= sum_c centeredRepR(G,r,c)^2
  and (2r-1)!! * |G|^r < B
  -> not DCEnergyBound G r.

B <= sum_c (repR(G,r,c) - |G|^r/q)^2
  and (2r-1)!! * |G|^r < B
  -> not DCEnergyBound G r.
```

The budgeted consumer form is also available:

```text
sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  and B <= (2r-1)!! * |G|^r
  -> DCEnergyBound G r.

sum_c deviationR(G,r,c)^2 <= B
  and B <= q^2 * (2r-1)!! * |G|^r
  -> DCEnergyBound G r.
```

This is the clean top-level target for analytic flatness work: prove an
`L^2` bound for the raw `r`-fold additive representation function around its
uniform mean, and the corrected Wick/DC moment bound follows.

The centered form also carries the multiplicative orbit saving directly:

```text
|G| * centeredRepR(G,r,b)^2
  <= sum_c centeredRepR(G,r,c)^2,    b != 0.

|G| * (repR(G,r,b) - |G|^r/q)^2
  <= sum_c (repR(G,r,c) - |G|^r/q)^2,    b != 0.
```

Composed with `DCEnergyBound`, this gives the pointwise probability-scale
budget:

```text
centeredRepR(G,r,b)^2
  <= (2r-1)!! * |G|^r / |G|.
```

This is the cleanest consumer interface for a future large-deviation or
equidistribution estimate on the centered `r`-fold additive convolution.

For consumers that do not yet use subgroup orbit structure, the file now also
exposes the one-way centered forms explicitly.  These include both the
`DCEnergyBound` wrappers and the more general versions that accept a direct
centered variance hypothesis:

```text
DCEnergyBound G r
  -> sum_c centeredRepR(G,r,c)^2 <= (2r-1)!! * |G|^r

sum_c centeredRepR(G,r,c)^2 <= (2r-1)!! * |G|^r
  -> DCEnergyBound G r

sum_c centeredRepR(G,r,c)^2 <= B
  -> centeredRepR(G,r,c0)^2 <= B

sum_c centeredRepR(G,r,c)^2 <= B
  -> (repR(G,r,c0) - |G|^r / q)^2 <= B

sum_c centeredRepR(G,r,c)^2 <= B
  and c0 != 0
  -> |repR(G,r,c0) - |G|^r / q| <= sqrt(B / |G|)

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  -> (repR(G,r,c0) - |G|^r / q)^2 <= B

sum_c centeredRepR(G,r,c)^2 <= B
  -> |repR(G,r,c0) - |G|^r / q| <= sqrt(B)

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  -> |repR(G,r,c0) - |G|^r / q| <= sqrt(B)

sum_c centeredRepR(G,r,c)^2 <= B
  and a > 0
  -> #{c : a <= |centeredRepR(G,r,c)|} <= B / a^2

sum_c centeredRepR(G,r,c)^2 <= B
  and a > 0
  -> #{c : a <= |repR(G,r,c) - |G|^r / q|} <= B / a^2

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  and a > 0
  -> #{c : a <= |repR(G,r,c) - |G|^r / q|} <= B / a^2

sum_c centeredRepR(G,r,c)^2 <= B
  and a > 0
  -> #{c != 0 : a <= |centeredRepR(G,r,c)|} <= B / a^2

sum_c centeredRepR(G,r,c)^2 <= B
  and a > 0
  -> #{c != 0 : a <= |repR(G,r,c) - |G|^r / q|} <= B / a^2

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  and a > 0
  -> #{c != 0 : a <= |repR(G,r,c) - |G|^r / q|} <= B / a^2

sum_c centeredRepR(G,r,c)^2 <= B
  and a <= |centeredRepR(G,r,b)|, b != 0, subgroup-shaped G
  -> |G| * a^2 <= B

sum_c centeredRepR(G,r,c)^2 <= B
  and a <= |repR(G,r,b) - |G|^r / q|, b != 0, subgroup-shaped G
  -> |G| * a^2 <= B

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  and a <= |repR(G,r,b) - |G|^r / q|, b != 0, subgroup-shaped G
  -> |G| * a^2 <= B

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  and B < |G| * a^2
  -> no b != 0 has a <= |repR(G,r,b) - |G|^r / q|

sum_c centeredRepR(G,r,c)^2 <= B
  and B < |G| * a^2
  -> no b != 0 has a <= |repR(G,r,b) - |G|^r / q|

a <= |centeredRepR(G,r,b)|, b != 0, subgroup-shaped G
  and (2r-1)!! * |G|^r < |G| * a^2
  -> not DCEnergyBound G r

a <= |repR(G,r,b) - |G|^r / q|, b != 0, subgroup-shaped G
  and (2r-1)!! * |G|^r < |G| * a^2
  -> not DCEnergyBound G r

DCEnergyBound G r
  and (2r-1)!! * |G|^r < |G| * a^2
  -> no b != 0 has a <= |centeredRepR(G,r,b)|

DCEnergyBound G r
  and (2r-1)!! * |G|^r < |G| * a^2
  -> no b != 0 has a <= |repR(G,r,b) - |G|^r / q|

sum_c centeredRepR(G,r,c)^2 <= B
  -> centeredRepR(G,r,b)^2 <= B / |G|,  b != 0, subgroup-shaped G.

sum_c centeredRepR(G,r,c)^2 <= B
  -> |G| * (repR(G,r,b) - |G|^r / q)^2 <= B,
     b != 0, subgroup-shaped G.

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  -> |G| * (repR(G,r,b) - |G|^r / q)^2 <= B,
     b != 0, subgroup-shaped G.

|G| * (repR(G,r,b) - |G|^r / q)^2 > B
  -> not (sum_c centeredRepR(G,r,c)^2 <= B),
     b != 0, subgroup-shaped G.

|G| * (repR(G,r,b) - |G|^r / q)^2 > B
  -> not (sum_c (repR(G,r,c) - |G|^r / q)^2 <= B),
     b != 0, subgroup-shaped G.

sum_c centeredRepR(G,r,c)^2 <= B
  -> (repR(G,r,b) - |G|^r / q)^2 <= B / |G|,
     b != 0, subgroup-shaped G.

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  -> (repR(G,r,b) - |G|^r / q)^2 <= B / |G|,
     b != 0, subgroup-shaped G.

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  -> forall b != 0,
     (repR(G,r,b) - |G|^r / q)^2 <= B / |G|,
     subgroup-shaped G.

sum_c centeredRepR(G,r,c)^2 <= B
  -> |centeredRepR(G,r,b)| <= sqrt(B / |G|),  b != 0, subgroup-shaped G.

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  -> |repR(G,r,b) - |G|^r / q| <= sqrt(B / |G|),
     b != 0, subgroup-shaped G.

sum_c (repR(G,r,c) - |G|^r / q)^2 <= B
  -> forall b != 0,
     |repR(G,r,b) - |G|^r / q| <= sqrt(B / |G|),
     subgroup-shaped G.

DCEnergyBound G r
  -> forall b != 0,
     (repR(G,r,b) - |G|^r / q)^2 <= (2r-1)!! * |G|^r / |G|

DCEnergyBound G r
  -> forall b != 0,
     |G| * (repR(G,r,b) - |G|^r / q)^2 <= (2r-1)!! * |G|^r

|G| * (repR(G,r,b) - |G|^r / q)^2 > (2r-1)!! * |G|^r
  -> not DCEnergyBound G r,
     b != 0, subgroup-shaped G.

DCEnergyBound G r
  -> forall c,
     (repR(G,r,c) - |G|^r / q)^2 <= (2r-1)!! * |G|^r

DCEnergyBound G r
  -> forall b != 0,
     |centeredRepR(G,r,b)| <= sqrt((2r-1)!! * |G|^r / |G|)

DCEnergyBound G r
  -> forall b != 0,
     |repR(G,r,b) - |G|^r / q| <= sqrt((2r-1)!! * |G|^r / |G|)

forall c, |centeredRepR(G,r,c)| <= A
  -> sum_c centeredRepR(G,r,c)^2 <= q * A^2

forall c, |centeredRepR(G,r,c)| <= A
  and q * A^2 <= (2r-1)!! * |G|^r
  -> DCEnergyBound G r.

forall c, |repR(G,r,c) - |G|^r / q| <= A
  -> sum_c (repR(G,r,c) - |G|^r / q)^2 <= q * A^2

forall c, |repR(G,r,c) - |G|^r / q| <= A
  and q * A^2 <= (2r-1)!! * |G|^r
  -> DCEnergyBound G r.

centeredRepR(G,r,0)^2 <= Z
  and forall c != 0, |centeredRepR(G,r,c)| <= A
  -> sum_c centeredRepR(G,r,c)^2 <= Z + (q - 1) * A^2

|repR(G,r,0) - |G|^r / q|^2 <= Z
  and forall c != 0, |repR(G,r,c) - |G|^r / q| <= A
  -> sum_c centeredRepR(G,r,c)^2 <= Z + (q - 1) * A^2

|repR(G,r,0) - |G|^r / q|^2 <= Z
  and forall c != 0, |repR(G,r,c) - |G|^r / q| <= A
  -> sum_c (repR(G,r,c) - |G|^r / q)^2 <= Z + (q - 1) * A^2

centeredRepR(G,r,0)^2 <= Z
  and forall c != 0, |centeredRepR(G,r,c)| <= A
  and Z + (q - 1) * A^2 <= (2r-1)!! * |G|^r
  -> DCEnergyBound G r.

|repR(G,r,0) - |G|^r / q|^2 <= Z
  and forall c != 0, |repR(G,r,c) - |G|^r / q| <= A
  and Z + (q - 1) * A^2 <= (2r-1)!! * |G|^r
  -> DCEnergyBound G r.

forall c != 0, |centeredRepR(G,r,c)| <= A
  -> |centeredRepR(G,r,0)| <= (q - 1) * A

forall c != 0, |repR(G,r,c) - |G|^r / q| <= A
  -> |repR(G,r,0) - |G|^r / q| <= (q - 1) * A

forall c != 0, |repR(G,r,c) - |G|^r / q| <= A
  -> (repR(G,r,0) - |G|^r / q)^2 <= ((q - 1) * A)^2

forall c != 0, |centeredRepR(G,r,c)| <= A
  -> sum_c centeredRepR(G,r,c)^2 <= ((q - 1) * A)^2 + (q - 1) * A^2.

forall c != 0, |repR(G,r,c) - |G|^r / q| <= A
  -> sum_c centeredRepR(G,r,c)^2 <= ((q - 1) * A)^2 + (q - 1) * A^2

forall c != 0, |repR(G,r,c) - |G|^r / q| <= A
  -> sum_c (repR(G,r,c) - |G|^r / q)^2
     <= ((q - 1) * A)^2 + (q - 1) * A^2

forall c != 0, |repR(G,r,c) - |G|^r / q| <= A
  and ((q - 1) * A)^2 + (q - 1) * A^2 <= (2r-1)!! * |G|^r
  -> DCEnergyBound G r.
```

The first `B`-bound is the no-subgroup fallback; the tail-count line is the
finite Chebyshev/Markov consumer for large-deviation arguments; the large-offset
line records that one nonzero spike already costs an entire multiplicative
orbit; the subgroup-shaped nonzero-offset theorem improves it by the orbit factor `/ |G|`.  The
`DCEnergyBound` pointwise lemmas are now thin corollaries of these direct
variance-hypothesis consumers.  The final uniform lines are the analytic
sup-norm entry point: a uniform raw representation-function flatness estimate
first gives the raw `L^2` target, and is enough for `DCEnergyBound` when its
`q * A^2` variance budget fits the Wick bound.  The zero/nonzero split lets a
future proof treat the special zero offset separately from the nonzero
Gauss-period orbit regime.  If only the nonzero estimate is available, the
mean-zero identity still controls the zero offset at the displayed cost.  The
latest direct `repR - |G|^r/q` aliases make each of those tail and split
interfaces available without unfolding `centeredRepR`.  The same is now true
for the orbit-spike obstruction: an analytic lower bound on one nonzero
`repR` deviation can directly refute `DCEnergyBound` when its orbit cost exceeds
the Wick budget.  The no-subgroup global fallback is also available directly in
`repR` language; subgroup structure only enters when upgrading from the global
bound to the orbit-saved `/ |G|` form.

## Verification

Command:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R240GeneralRFoldVariance.lean
```

Result:

```text
OK (25s)
```

The axiom audit prints the standard frontier dependencies only:

```text
[propext, Classical.choice, Quot.sound]
```

## Meaning

This does not prove the proximity prize.  It upgrades the variance/equidistribution
interface from a depth-3 diagnostic to the actual deep-r object:

```text
DC-subtracted Wick at depth r
  <=> flatness of the r-fold additive convolution of 1_G at Wick scale.
```

The remaining hard input is analytic: prove the flatness bound uniformly at
`r ~= log q` for the dyadic subgroup regime.
