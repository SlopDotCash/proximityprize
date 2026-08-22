/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G229: sponsor-prime quotient-Jacobi fanout constants (#466)

G228 rewrote the shared Mellin factor

```text
S_χ = ∑_{u ∈ G} conj(χ)(2 - u)
```

as a quotient-Jacobi average.  This is the correct analytic coordinate system, but it does not
thin the problem.  If `n = |G|`, `m = (p - 1) / n`, and `2 ∉ G`, Parseval gives the RMS lower bound

```text
RMS(What) ≥ n * sqrt (n * (m - n) / (m - 1)),    What(χ) = n*S_χ,
```

while any one inner Jacobi summand contributes at most `n * sqrt p / m`.  Therefore the square
of the one-summand RMS fraction is bounded by

```text
p * (m - 1) / (m^2 * n * (m - n)).
```

This file kernel-checks the production constants for the two certified sponsor primes from the #466
campaign:

```text
P1 = 2^30 * (2^128 + 192) + 1,
P2 = 2^30 * (2^129 + 13)  + 1.
```

The exact half-recovery arithmetic is the useful no-go.  At `P1`, every selected family of at most
`2^63 - 1` inner Jacobi summands is still strictly below half of the full RMS mass under the G228
universal summand bound.  At `P2`, the corresponding exact lower floor is
`13043817825332782212` terms, and in particular `2^63` terms are still below half.  This is a
calibrated numeric consumer of the G228 fanout identity, not a new character-sum estimate and not a
claim that the CORE target is closed.
-/
set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G229JacobiFanoutSponsorBounds

/-- The production subgroup order used by the sponsor primes. -/
def sponsorN : ℕ := 2 ^ 30

/-- The quotient size `(P1 - 1) / sponsorN`. -/
def sponsorM1 : ℕ := 2 ^ 128 + 192

/-- The first certified sponsor prime from the #466 campaign. -/
def sponsorP1 : ℕ := sponsorN * sponsorM1 + 1

/-- The quotient size `(P2 - 1) / sponsorN`. -/
def sponsorM2 : ℕ := 2 ^ 129 + 13

/-- The second certified sponsor prime from the #466 campaign. -/
def sponsorP2 : ℕ := sponsorN * sponsorM2 + 1

/-- Numerator of the G228 squared one-Jacobi-summand RMS fraction bound. -/
def oneJacobiSqNum (p m : ℕ) : ℕ := p * (m - 1)

/-- Denominator of the G228 squared one-Jacobi-summand RMS fraction bound. -/
def oneJacobiSqDen (n m : ℕ) : ℕ := m ^ 2 * n * (m - n)

/-- The squared fraction bound is at most `2^{-e}`, written without division. -/
def OneJacobiSqLePow2 (n p m e : ℕ) : Prop :=
  oneJacobiSqNum p m * 2 ^ e ≤ oneJacobiSqDen n m

/-- `K` selected inner Jacobi summands are still strictly below a half-RMS recovery, using the G228
universal bound, written as a squared integer inequality. -/
def HalfRecoveryBlocked (n p m K : ℕ) : Prop :=
  4 * K ^ 2 * oneJacobiSqNum p m < oneJacobiSqDen n m

/-- Sanity check: `P1 - 1 = n*m`. -/
theorem sponsorP1_sub_one : sponsorP1 - 1 = sponsorN * sponsorM1 := by decide

/-- Sanity check: `P2 - 1 = n*m`. -/
theorem sponsorP2_sub_one : sponsorP2 - 1 = sponsorN * sponsorM2 := by decide

/-- At the first sponsor prime, the G228 one-inner-Jacobi RMS fraction squared is below `2^-127`.
The sharper decimal report is essentially `2^-128`; the exact `+1` in `p = nm+1` puts it just
above the closed dyadic inequality at exponent `128`. -/
theorem p1_one_jacobi_sq_le_two_pow_neg_127 :
    OneJacobiSqLePow2 sponsorN sponsorP1 sponsorM1 127 := by
  norm_num [OneJacobiSqLePow2, oneJacobiSqNum, oneJacobiSqDen, sponsorN, sponsorP1, sponsorM1]

/-- At the second sponsor prime, the G228 one-inner-Jacobi RMS fraction squared is below `2^-128`.
The sharper decimal report is essentially `2^-129`, again just above the closed dyadic exponent due
to the exact sponsor arithmetic. -/
theorem p2_one_jacobi_sq_le_two_pow_neg_128 :
    OneJacobiSqLePow2 sponsorN sponsorP2 sponsorM2 128 := by
  norm_num [OneJacobiSqLePow2, oneJacobiSqNum, oneJacobiSqDen, sponsorN, sponsorP2, sponsorM2]

/-- Exact `P1` half-recovery floor: `2^63 - 1` selected inner Jacobi summands are still strictly
below half of the full `What` RMS mass under the G228 universal bound.  Thus strict half recovery at
`P1` requires at least `2^63` inner Jacobi summands. -/
theorem p1_two_pow_63_sub_one_terms_below_half :
    HalfRecoveryBlocked sponsorN sponsorP1 sponsorM1 (2 ^ 63 - 1) := by
  norm_num [HalfRecoveryBlocked, oneJacobiSqNum, oneJacobiSqDen, sponsorN, sponsorP1, sponsorM1]

/-- At `P1`, the next integer `2^63` is no longer certified below half by the squared G228 bound;
this records the exact sharp integer threshold for the half-RMS obstruction. -/
theorem p1_two_pow_63_terms_not_below_half :
    ¬ HalfRecoveryBlocked sponsorN sponsorP1 sponsorM1 (2 ^ 63) := by
  norm_num [HalfRecoveryBlocked, oneJacobiSqNum, oneJacobiSqDen, sponsorN, sponsorP1, sponsorM1]

/-- Exact integer floor for the `P2` half-recovery obstruction. -/
def p2HalfRecoveryFloor : ℕ := 13043817825332782212

/-- `P2` calibrated fanout: the exact floor number of selected inner Jacobi summands is still
strictly below half of the full `What` RMS mass under the G228 universal bound. -/
theorem p2_half_recovery_floor_terms_below_half :
    HalfRecoveryBlocked sponsorN sponsorP2 sponsorM2 p2HalfRecoveryFloor := by
  norm_num [p2HalfRecoveryFloor, HalfRecoveryBlocked, oneJacobiSqNum, oneJacobiSqDen, sponsorN,
    sponsorP2, sponsorM2]

/-- At `P2`, the successor of the floor is not certified below half; this pins the exact threshold
reported by the G228 probe. -/
theorem p2_half_recovery_floor_succ_not_below_half :
    ¬ HalfRecoveryBlocked sponsorN sponsorP2 sponsorM2 (p2HalfRecoveryFloor + 1) := by
  norm_num [p2HalfRecoveryFloor, HalfRecoveryBlocked, oneJacobiSqNum, oneJacobiSqDen, sponsorN,
    sponsorP2, sponsorM2]

/-- In particular, `2^63` selected inner Jacobi summands are still below half at `P2`. -/
theorem p2_two_pow_63_terms_still_below_half :
    HalfRecoveryBlocked sponsorN sponsorP2 sponsorM2 (2 ^ 63) := by
  norm_num [HalfRecoveryBlocked, oneJacobiSqNum, oneJacobiSqDen, sponsorN, sponsorP2, sponsorM2]

/-- The first sponsor quotient is larger than the subgroup order, so the Parseval lower-bound
denominator is genuinely positive in the G228 formula. -/
theorem sponsorM1_gt_sponsorN : sponsorN < sponsorM1 := by decide

/-- The second sponsor quotient is larger than the subgroup order, so the Parseval lower-bound
denominator is genuinely positive in the G228 formula. -/
theorem sponsorM2_gt_sponsorN : sponsorN < sponsorM2 := by decide

#print axioms p1_one_jacobi_sq_le_two_pow_neg_127
#print axioms p2_one_jacobi_sq_le_two_pow_neg_128
#print axioms p1_two_pow_63_sub_one_terms_below_half
#print axioms p1_two_pow_63_terms_not_below_half
#print axioms p2_half_recovery_floor_terms_below_half
#print axioms p2_half_recovery_floor_succ_not_below_half
#print axioms p2_two_pow_63_terms_still_below_half

end ArkLib.ProximityGap.Frontier.G229JacobiFanoutSponsorBounds
