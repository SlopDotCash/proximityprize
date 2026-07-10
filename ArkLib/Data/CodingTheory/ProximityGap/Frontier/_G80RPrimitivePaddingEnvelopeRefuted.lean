/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# G80R: the proposed primitive-padding envelope is false at the saddle

R369 proposed, and the G80 lane attempted to formalize, the ordered-tuple sector estimate

`W_r^(s) <= J_s * (r descFactorial s)^2 * n^(r-s)`.

It is false because maximal common cancellation identifies a common *multiset*, while the two
endpoint tuples order that multiset independently.  The exact companion probe enumerates the
counterexample `mu_4` in `F_3001` at the saddle `r=ceil(log 3001)=9`, primitive depth `s=2`:

`J_2=8`, `W_9^(2)=1148084928 > 679477248 = J_2*(9 descFactorial 2)^2*4^7`.

This file kernel-checks the finite-field primitive relation and the decisive exact arithmetic.
The enumeration is reproducible in `scripts/probes/probe_466_g80_padding_envelope_refutation.py`.
A safe universal reconstruction needs an additional permutation of `Fin (r-s)`, hence an extra
factor `(r-s)!`, or must work with permutation-quotiented/`Multiset.countPerms` weights.

This refutes the padding mechanism, not `FourthPowerSaddleDCEnergy` or production delta-star.
Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G80RPrimitivePaddingEnvelopeRefuted

local instance : Fact (Nat.Prime 3001) := ⟨by norm_num⟩

/-- `1353` is a primitive fourth root modulo `3001`: its square is `-1`. -/
theorem root_sq_eq_neg_one : (1353 : ZMod 3001) ^ 2 = -1 := by decide

theorem root_order_eq_four : orderOf (1353 : ZMod 3001) = 4 := by
  have hnot : ¬(1353 : ZMod 3001) ^ (2 : ℕ) ^ 1 = 1 := by decide
  have hfin : (1353 : ZMod 3001) ^ (2 : ℕ) ^ (1 + 1) = 1 := by decide
  simpa using orderOf_eq_prime_pow hnot hfin

/-- The two disjoint antipodal depth-two cores have equal additive sum (both are zero).
Their two orientations and the reversal of the endpoint pair give `J_2=8` ordered cores. -/
theorem antipodal_core_relation :
    (1 : ZMod 3001) + 1353 ^ 2 = 1353 + 1353 ^ 3 := by
  decide

/-- The exact value of the envelope claimed by R369/G80. -/
theorem claimed_envelope_value :
    8 * ((9 : ℕ).descFactorial 2) ^ 2 * 4 ^ (9 - 2) = 679477248 := by norm_num

/-- **Exact saddle counterexample arithmetic.**  The count-vector probe's exact sector mass is
strictly larger than the proposed envelope. -/
theorem primitive_padding_envelope_fails :
    679477248 < 1148084928 := by norm_num

/-- Adding the missing independent padding permutation gives a safe ceiling on this witness. -/
theorem factorial_corrected_envelope_survives :
    1148084928 ≤ 679477248 * ((9 - 2 : ℕ).factorial) := by norm_num

/-- **The factorial repair destroys the production absorption test.**  For a single linear-size
depth-two orbit (`J ≤ n`), G79S would need

`r^2 * (r-2)! ≤ n`

after inserting the missing padding-permutation factor.  At the nominal production values
`n=2^30`, `r=110`, the inequality is reversed by an enormous margin. -/
theorem factorial_repair_breaks_production_depth_two_absorption :
    2 ^ 30 < 110 ^ 2 * ((108 : ℕ).factorial) := by norm_num

end ArkLib.ProximityGap.Frontier.G80RPrimitivePaddingEnvelopeRefuted

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G80RPrimitivePaddingEnvelopeRefuted.root_order_eq_four
#print axioms ArkLib.ProximityGap.Frontier.G80RPrimitivePaddingEnvelopeRefuted.antipodal_core_relation
#print axioms ArkLib.ProximityGap.Frontier.G80RPrimitivePaddingEnvelopeRefuted.claimed_envelope_value
#print axioms ArkLib.ProximityGap.Frontier.G80RPrimitivePaddingEnvelopeRefuted.primitive_padding_envelope_fails
#print axioms ArkLib.ProximityGap.Frontier.G80RPrimitivePaddingEnvelopeRefuted.factorial_corrected_envelope_survives
#print axioms
  ArkLib.ProximityGap.Frontier.G80RPrimitivePaddingEnvelopeRefuted.factorial_repair_breaks_production_depth_two_absorption
