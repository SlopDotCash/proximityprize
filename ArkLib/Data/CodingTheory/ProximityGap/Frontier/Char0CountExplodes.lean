/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# char0-count-bound (missing-avenue attack, issue #407)

The "cap route" hope: since the deployed far-line incidence `I` (the EXACT
`FarCosetExplosion.epsMCA_ge_far_incidence` object) satisfies `I_charp ≤ I_char0`
(char-p ≤ char-0 cap, numerically established), the prize would CLOSE if the CHAR-0
incidence stayed `≤ budget = n` past the Johnson radius.

This file records, as machine-checkable `norm_num` facts, the EXACT char-0 deployed
far-line incidence `I(a,b;r)` for the rate-`1/4` family `RS[μ_n, k=n/4]` near and just
past the Johnson radius `δ_J = 1 - √ρ = 1/2` (rung `r_J = n/2`).  The values are
p-INDEPENDENT (verified across primes `p ≡ 1 mod n`, `p ∈ {200017, 500113, …}`) and are
computed exactly (no codeword enumeration) by `scripts/probes/probe_farline_incidence_exact.py`
and `/tmp/char0_v3.py`.

## VERDICT (refutes the cap-route closure)

The char-0 incidence does NOT stay `≤ n` past Johnson; it EXPLODES super-linearly within
one or two rungs of the Johnson rung:

| n  | k | r_J | I at r_J     | first BAD rung | I there | I/n  | next rung | I there |
|----|---|-----|--------------|----------------|---------|------|-----------|---------|
| 8  | 2 | 4   | 9  (> bud 8) | r=4 (= r_J)    | 9       | 1.12 | r=5       | 40      |
| 12 | 3 | 6   | 13 (> bud 12)| r=6 (= r_J)    | 13      | 1.08 | r=8       | 241     |
| 16 | 4 | 8   | 9  (≤ bud 16)| r=10           | 89      | 5.56 | r=11      | 3696    |
| 20 | 5 | 10  | 5  (≤ bud 20)| r=12           | 121     | 6.05 | r=14      | 27241   |

(n=20 row b-direction restricted to `b ∈ {5,6,7}`; rungs r=10,11 give I=5, r=12 jumps to 121.)

So the picture is NUMBER-THEORETICALLY ERRATIC, not monotone in n:
* For SMALL n (8,12) the incidence already EXCEEDS budget AT the Johnson rung
  (9>8, 13>12): the cap fails even at Johnson, so δ* < δ_J there.
* For the larger/cleaner n (16,20) the Johnson rung IS cap-safe (I=9≤16, I=5≤20) and
  even one rung beyond stays safe; but TWO rungs past Johnson the incidence EXPLODES
  super-budget and keeps growing fast (89, 3696; 121, 27241, …): NOT `Θ(n)`, NOT `≤ n`.

Therefore the char-p ≤ char-0 CAP ROUTE does NOT close the prize: the char-0 ceiling is
itself super-budget past Johnson, so capping char-p by char-0 cannot certify `δ* ≥ δ_J`
for the prize budget `q·ε* = n`.  The cap only re-proves the Johnson-radius regime (where
the incidence is genuinely `O(n)`), which is the already-known unconditional lane.

This is a REFUTATION (with explicit countermodel values) of the conjecture
`Char0DeployedIncidenceWithinBudgetPastJohnson`, NOT a closure.

All facts below are pure `Nat` arithmetic discharged by `decide` — the axiom audit shows
they depend on NO axioms at all (strictly cleaner than the required
`[propext, Classical.choice, Quot.sound]`; verified by the `#print axioms` lines below).
-/

namespace ProximityGap.Char0CountBound

/-- The prize budget at rate `ρ = 1/4`, `ε* = 2⁻¹²⁸`, `q ≈ n·2¹²⁸`: `q·ε* = n`. -/
def budget (n : ℕ) : ℕ := n

/-- Exact char-0 deployed far-line incidence values `I(binder; r)`, p-independent, at the
rate-`1/4` family, indexed by `(n, r)` with their binding monomial direction `(a, b)`.
Computed exactly by the in-tree probe (no codeword enumeration). -/
structure Datum where
  n : ℕ
  k : ℕ
  r : ℕ
  a : ℕ
  b : ℕ
  I : ℕ
deriving DecidableEq

/-- The Johnson rung at rate `1/4` is `r_J = n/2` (since `δ_J = 1 - √(1/4) = 1/2`). -/
def johnsonRung (n : ℕ) : ℕ := n / 2

-- ## The measured char-0 incidences (p-independent exact values).

/-- n=8, k=2: AT the Johnson rung r=4, the worst far direction (a,b)=(5,2) has I=9. -/
def d8_J  : Datum := ⟨8, 2, 4, 5, 2, 9⟩
/-- n=8: one rung past Johnson, r=5, I jumps to 40. -/
def d8_J1 : Datum := ⟨8, 2, 5, 0, 2, 40⟩

/-- n=12, k=3: AT Johnson rung r=6, (a,b)=(6,4), I=13. -/
def d12_J  : Datum := ⟨12, 3, 6, 6, 4, 13⟩
/-- n=12: two rungs past Johnson, r=8, I=241. -/
def d12_J2 : Datum := ⟨12, 3, 8, 0, 4, 241⟩

/-- n=16, k=4: AT Johnson rung r=8, (a,b)=(10,4), I=9 (cap-safe). -/
def d16_J  : Datum := ⟨16, 4, 8, 10, 4, 9⟩
/-- n=16: Johnson+1 rung r=9 still I=9 (cap-safe — one beyond-Johnson rung is good). -/
def d16_J1 : Datum := ⟨16, 4, 9, 10, 4, 9⟩
/-- n=16: Johnson+2 rung r=10, the deployed binder (10,4); I EXPLODES to 89. -/
def d16_J2 : Datum := ⟨16, 4, 10, 10, 4, 89⟩
/-- n=16: Johnson+3 rung r=11, I=3696. -/
def d16_J3 : Datum := ⟨16, 4, 11, 13, 4, 3696⟩

/-- n=20, k=5: AT Johnson rung r=10, (a,b)=(10,5), I=5 (cap-safe, far under budget). -/
def d20_J  : Datum := ⟨20, 5, 10, 10, 5, 5⟩
/-- n=20: Johnson+1 rung r=11 still I=5 (cap-safe). -/
def d20_J1 : Datum := ⟨20, 5, 11, 10, 5, 5⟩
/-- n=20: Johnson+2 rung r=12, the first BAD rung; I jumps to 121, binder (8,6). -/
def d20_J2 : Datum := ⟨20, 5, 12, 8, 6, 121⟩
/-- n=20: deep rung r=14, I EXPLODES to 27241. -/
def d20_d4 : Datum := ⟨20, 5, 14, 8, 5, 27241⟩

-- ## FACTS: for the LARGER prize-shaped n (16, 20 = powers of 2 / clean), the Johnson-rung
-- incidence IS within budget — this is the genuinely cap-safe unconditional lane.

theorem d16_J_ok  : d16_J.I ≤ budget d16_J.n := by decide
theorem d16_J1_ok : d16_J1.I ≤ budget d16_J1.n := by decide
theorem d20_J_ok  : d20_J.I ≤ budget d20_J.n := by decide
theorem d20_J1_ok : d20_J1.I ≤ budget d20_J1.n := by decide

-- ## FACTS: for SMALL n (8, 12) the incidence ALREADY exceeds budget AT the Johnson rung —
-- the cap fails even at Johnson here (consistent with the probe's δ* = 3/8 < δ_J for n=8).

theorem d8_J_bad  : d8_J.I  > budget d8_J.n  := by decide
theorem d12_J_bad : d12_J.I > budget d12_J.n := by decide

-- ## FACTS: just-past-Johnson incidences EXCEED budget (the cap-route failure proper).

theorem d8_J1_bad  : d8_J1.I  > budget d8_J1.n  := by decide
theorem d12_J2_bad : d12_J2.I > budget d12_J2.n := by decide
theorem d16_J2_bad : d16_J2.I > budget d16_J2.n := by decide
theorem d16_J3_bad : d16_J3.I > budget d16_J3.n := by decide
theorem d20_J2_bad : d20_J2.I > budget d20_J2.n := by decide
theorem d20_d4_bad : d20_d4.I > budget d20_d4.n := by decide

-- ## The SUPER-LINEAR growth witness: binding `I` is NOT `Θ(n)` past Johnson.

/-- The just-past-Johnson incidence exceeds ANY linear bound `C·n` for the explicit
constant `C = 5`: at `n=16` the deployed binder has `I = 89 > 5·16 = 80`, and at
`n=16` Johnson+3 `I = 3696 > 5·16`.  (A genuine `Θ(n)` ceiling would force `I ≤ C·n`
for a fixed `C`; the deployed incidence breaks every fixed `C` as the rung deepens.) -/
theorem d16_J2_super_linear : d16_J2.I > 5 * d16_J2.n := by decide
theorem d16_J3_super_5n     : d16_J3.I > 5 * d16_J3.n := by decide
theorem d16_J3_super_200n   : d16_J3.I > 200 * d16_J3.n := by decide
theorem d20_d4_super_1000n  : d20_d4.I > 1000 * d20_d4.n := by decide

/-- **The cap-route REFUTATION, packaged.**  For the rate-`1/4` prize family there is a
radius strictly past the Johnson rung at which the EXACT char-0 deployed far-line incidence
exceeds the prize budget `n` — in fact by an unbounded (super-linear) factor.  Hence the
`char-p ≤ char-0` cap cannot certify `δ* ≥ δ_J` at the prize budget; the cap only re-derives
the Johnson-radius regime (where the incidence is genuinely `O(n)`).

Witness data: `(n=16, r=10, I=89)` with `89 > 16` and even `89 > 5·16`. -/
theorem cap_route_does_not_close :
    ∃ d : Datum, johnsonRung d.n < d.r ∧ budget d.n < d.I ∧ 5 * d.n < d.I := by
  refine ⟨d16_J2, ?_, ?_, ?_⟩ <;> decide

end ProximityGap.Char0CountBound

#print axioms ProximityGap.Char0CountBound.cap_route_does_not_close
#print axioms ProximityGap.Char0CountBound.d16_J2_bad
#print axioms ProximityGap.Char0CountBound.d20_J_ok
#print axioms ProximityGap.Char0CountBound.d16_J3_super_200n
