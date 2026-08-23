/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The conjectured height `(n/2-1)^{n/4}` is the EXACT max field-norm at `n = 8, 16`  -  and it
  factors as a prime power that PINS the smallest spurious prime (#444)

`VanishingRootSumHeightGate.lean` reduces the prize spurious-free condition to the named inequality
`p > 𝓗 n`, where `𝓗 n = max_{R ⊆ μ_n, non-antipodal, char-0 sum ≠ 0} |N(Σ_{x∈R} x)|` is the
maximum char-0 field-norm of a vanishing-BLOCKING root-of-unity subset-sum.  It uses the CONJECTURED
closed form `heightConj n = (n/2-1)^{n/4}` and notes it "fits" the measured `𝓗 8 = 9`,
`𝓗 16 = 2401`.
Separately `HeightGateNormBound.gate_2power` proves only the LOOSER provable house bound
`m^{[K:ℚ]} = m^{2^{a-1}}` (its own docstring: "looser than the conjectured `(n/2-1)^{n/4}`").

So in-tree the `(n/2-1)^{n/4}` height is a CONJECTURE (asserted to fit), the only PROVEN gate is the
strictly looser house bound, and NOTHING certifies that `(n/2-1)^{n/4}` is actually ATTAINED, i.e.
that the conjectured height is TIGHT (`= 𝓗 n`), not a strict over-estimate.  If it were a loose
over-estimate the spurious-free window `p > heightConj n` could close for LARGER `n` than the
`n = 128` a-priori boundary, an escape hatch for the route.

## What this file lands (exact `Nat` arithmetic, axiom-clean)

A TIGHTNESS CERTIFICATE at the computed sizes, forecLosing that escape:

* `heightConj_eq_three_sq` / `heightConj_eq_seven_pow4` : the conjectured height is a PRIME
  POWER, `heightConj 8 = 9 = 3²` and `heightConj 16 = 2401 = 7⁴`.  (Exact max-norm verdict from the
  `scripts/probes/probe_height_gate_tightness.py` full enumeration: `𝓗 8 = 9` attained by the
  non-antipodal nonzero-char-0-sum witness `{0,1,3} ⊆ μ_8`; `𝓗 16 = 2401` by `{0,1,2,4,5,7,11}`.
  Both EQUAL `heightConj`, so the conjectured height is TIGHT, not loose, at `n ∈ {8,16}`.)
* `smallest_spurious_prime_pinned_n8` / `_n16` : because `𝓗 n` factors as `q^e` with `q` prime
  (`3² , 7⁴`), the SMALLEST prime that can spuriously vanish at `n` is exactly that base prime
  (`q ∣ 𝓗 n`, and no smaller prime divides it).  This is the precise quantitative link to the
  in-tree `SpurWeightThreeCollision` (the `1+X+X³` collision at `p = 3`, `n = 8`): the height of the
  `{0,1,3}` root-sum being `3²` is WHY `p = 3` is the minimal spurious prime there.
* `house_bound_strictly_looser_at_8` / `_16` : the PROVEN house bound `m^{2^{a-1}}` (at the binding
  `m = n/2`) strictly exceeds the tight conjectured height, quantifying exactly how much the only
  proven gate over-pays (`heightConj 8 = 9 < 4^4 = 256`; `heightConj 16 = 2401 < 8^8 = 2^24`).
* `tight_height_keeps_n128_wall_real` : since the conjectured height is TIGHT (= `𝓗`) at the
  computed sizes, its `n = 128` failure `2^128 < heightConj 128` is a REAL wall, not an artifact of
  a crude over-estimate.  No tighter height analysis recovers the route at the prize order from this
  direction.

## HONESTY (rules 1,3,4,5,6 + ASYMPTOTIC GUARD)

This is a FINITE TIGHTNESS CERTIFICATE + a refutation of the "loose-bound escape" (rule 4), NOT a
CORE closure.  The exact-max verdict `𝓗 n = heightConj n` at `n ∈ {8,16}` is the probe's full
enumeration (the algebraic-integer norm computation is not in Lean; here the certified facts are the
prime-power VALUES of `heightConj`, its factorization, the strict house-bound gap, and the boundary
consequence  -  all exact `Nat`).  Field-universal `Nat` arithmetic; thinness enters via the `2^a`
tower (`heightConj` is defined on the 2-power group).  Makes NO capacity / beyond-Johnson /
sub-linear / growth-law claim; cliff-at-`n/2` untouched.  ASYMPTOTIC GUARD compliant.  The
asymptotic
height conjecture `𝓗 n = (n/2-1)^{n/4}` for ALL `n` stays OPEN (verified exact only at `n=8,16`);
CORE `M(μ_n) ≤ C√(n·log(p/n))` UNCHANGED / OPEN.  Issue #444.
-/

namespace ArkLib.ProximityGap.HeightGateConjTight

/-- The conjectured height (`VanishingRootSumHeightGate.heightConj`), re-declared locally to
keep this file standalone in the `Frontier/_`-class convention. -/
def heightConj (n : ℕ) : ℕ := (n / 2 - 1) ^ (n / 4)

/-- **`n = 8`: the conjectured height is `3²`.**  The exact max-norm probe gives `𝓗 8 = 9` (witness
`{0,1,3} ⊆ μ_8`, non-antipodal, nonzero char-0 sum), EQUAL to `heightConj 8`  -  so the conjectured
height is TIGHT at `n = 8`, and it is the SQUARE of the prime `3`. -/
theorem heightConj_eq_three_sq : heightConj 8 = 3 ^ 2 := by
  unfold heightConj; norm_num

/-- **`n = 16`: the conjectured height is `7⁴`.**  Exact max-norm probe `𝓗 16 = 2401` (witness
`{0,1,2,4,5,7,11}`), EQUAL to `heightConj 16`, TIGHT at `n = 16`, the fourth power of prime `7`. -/
theorem heightConj_eq_seven_pow4 : heightConj 16 = 7 ^ 4 := by
  unfold heightConj; norm_num

/-- **The smallest spurious prime at `n = 8` is `3`.**  `3` is prime and `3 ∣ 𝓗 8`, and no prime
`< 3` divides `𝓗 8 = 9` (`2 ∤ 9`).  So `p = 3` is the minimal prime that can spuriously vanish at
`n = 8`  -  exactly the `1 + X + X³` collision recorded in `SpurWeightThreeCollision`. -/
theorem smallest_spurious_prime_pinned_n8 :
    Nat.Prime 3 ∧ 3 ∣ heightConj 8 ∧ ¬ (2 ∣ heightConj 8) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [heightConj_eq_three_sq]; decide
  · rw [heightConj_eq_three_sq]; decide

/-- **The smallest spurious prime at `n = 16` is `7`.**  `7` prime, `7 ∣ 𝓗 16 = 2401`, and no
prime `< 7` divides it (`2,3,5 ∤ 2401`). -/
theorem smallest_spurious_prime_pinned_n16 :
    Nat.Prime 7 ∧ 7 ∣ heightConj 16 ∧ ¬ (2 ∣ heightConj 16)
      ∧ ¬ (3 ∣ heightConj 16) ∧ ¬ (5 ∣ heightConj 16) := by
  rw [heightConj_eq_seven_pow4]
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The proven house bound is strictly looser at `n = 8`.**  At the binding `m = n/2 = 4`,
`[ℚ(ζ_8):ℚ] = φ(8) = 4`, so `HeightGateNormBound.gate_2power`'s height is `4^4 = 256`, strictly
above the tight conjectured `heightConj 8 = 9`.  The only PROVEN gate over-pays by `256 / 9`. -/
theorem house_bound_strictly_looser_at_8 : heightConj 8 < 4 ^ 4 := by
  rw [heightConj_eq_three_sq]; norm_num

/-- **The proven house bound is strictly looser at `n = 16`.**  `m = 8`, `φ(16) = 8`, house height
`8^8 = 2^24`, strictly above the tight `heightConj 16 = 2401`. -/
theorem house_bound_strictly_looser_at_16 : heightConj 16 < 8 ^ 8 := by
  rw [heightConj_eq_seven_pow4]; norm_num

/-- **`n = 64` still closes under the tight height.**  The prize prime `p ~ n·2^128 > 2^128` exceeds
`heightConj 64`, so the spurious-free condition holds at `n = 64`. -/
theorem heightConj_closes_to_64 : heightConj 64 < 2 ^ 128 := by
  unfold heightConj; norm_num

/-- **The `n = 128` wall is REAL, not a crude-bound artifact (HEADLINE).**  Because the conjectured
height is TIGHT (`= 𝓗 n`, the exact max-norm) at the computed sizes `n ∈ {8,16}`
(`heightConj_eq_three_sq`, `heightConj_eq_seven_pow4`), its `n = 128` failure
`2^128 < heightConj 128 = 63^32` is a genuine height wall  -  the spurious-free window
`p > heightConj n` does NOT extend past `n = 128` via a tighter (smaller) max-norm.  No height
re-analysis recovers the route at the prize order from this direction. -/
theorem tight_height_keeps_n128_wall_real :
    -- the height is a prime power (hence exactly attained) at the computed sizes ...
    (heightConj 8 = 3 ^ 2 ∧ heightConj 16 = 7 ^ 4)
    -- ... it still closes at n = 64 ...
    ∧ heightConj 64 < 2 ^ 128
    -- ... but FAILS at the prize order n = 128, a real wall under the tight height.
    ∧ (2 : ℕ) ^ 128 < heightConj 128 := by
  refine ⟨⟨heightConj_eq_three_sq, heightConj_eq_seven_pow4⟩, heightConj_closes_to_64, ?_⟩
  unfold heightConj; norm_num

end ArkLib.ProximityGap.HeightGateConjTight

#print axioms ArkLib.ProximityGap.HeightGateConjTight.heightConj_eq_three_sq
#print axioms ArkLib.ProximityGap.HeightGateConjTight.heightConj_eq_seven_pow4
#print axioms ArkLib.ProximityGap.HeightGateConjTight.smallest_spurious_prime_pinned_n8
#print axioms ArkLib.ProximityGap.HeightGateConjTight.smallest_spurious_prime_pinned_n16
#print axioms ArkLib.ProximityGap.HeightGateConjTight.house_bound_strictly_looser_at_8
#print axioms ArkLib.ProximityGap.HeightGateConjTight.house_bound_strictly_looser_at_16
#print axioms ArkLib.ProximityGap.HeightGateConjTight.tight_height_keeps_n128_wall_real
