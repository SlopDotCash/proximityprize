/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# char0-count-bound (missing-avenue attack, issue #407)

The "cap route" hope: if the deployed far-line incidence `I` (intended to be the
`FarCosetExplosion.epsMCA_ge_far_incidence` object) satisfies `I_charp ≤ I_char0`
(a char-p ≤ char-0 cap that is only NUMERICALLY observed, not proved), the prize would close if
the CHAR-0 incidence stayed `≤ budget = n` past the Johnson radius.

## Scope of the formal content (read first)

`Datum` below is a record of six UNCONSTRAINED natural numbers. No field is linked in Lean to an
evaluation domain, RS code, pencil, incidence count, prime, radius or characteristic-zero count.
The `decide` proofs certify only comparisons between the entered integers; they do NOT certify
that any entered `I` is the exact deployed count, nor the char-p ≤ char-0 cap. The values were
recorded from probe runs (the cited `scripts/probes/probe_farline_incidence_exact.py` is not in
this tree, and `/tmp/char0_v3.py` is an ephemeral scratch file), over primes `p ≡ 1 mod n`
such as `200017, 500113`; their p-independence is an empirical observation. The pencil / radius /
domain convention that produced them (the meaning of the direction `(a, b)`) is not specified
here, and no theorem identifies a row with an actual count. Treat every row as PROVENANCE DATA.

**Retired row (contradicts the standard monomial reading).** The former row
`d8_J1 = (n=8, k=2, r=5, a=0, b=2, I=40)` is inconsistent with the natural reading "pencil
`X^a + γ·X^b` on `8` distinct nodes, MCA radius `r/n`". At `r/n = 5/8` the required agreement is
`3`. For `1 + γX²` with `γ ≠ 0`, the difference from any degree-`< 2` codeword is a nonzero
polynomial of degree exactly `2`, so it agrees on at most `2` nodes; at `γ = 0` the word `1` is a
codeword, and the `X²` row cannot be jointly explained on `3` nodes either. So under that reading
the bad-scalar set is exactly `{0}` (size `1`, over every compatible field), not `40`. The row has
been removed; if a different pencil convention was intended, it must be stated and checked before
the value is reused. (This is a source-level argument, not a Lean theorem in this file.)

## Recorded data (provenance, not proved counts)

The recorded char-0 values, as reported by the probe, near the Johnson rung:

| n  | k | r_J | I at r_J     | first BAD rung | I there | I/n  | next rung | I there |
|----|---|-----|--------------|----------------|---------|------|-----------|---------|
| 8  | 2 | 4   | 9  (> bud 8) | r=4 (= r_J)    | 9       | 1.12 | r=5       | retired |
| 12 | 3 | 6   | 13 (> bud 12)| r=6 (= r_J)    | 13      | 1.08 | r=8       | 241     |
| 16 | 4 | 8   | 9  (≤ bud 16)| r=10           | 89      | 5.56 | r=11      | 3696    |
| 20 | 5 | 10  | 5  (≤ bud 20)| r=12           | 121     | 6.05 | r=14      | 27241   |

(n=20 row b-direction restricted to `b ∈ {5,6,7}`; rungs r=10,11 give I=5, r=12 jumps to 121.)

Reading of the recorded values (empirical, conditional on the rows being the intended counts):
* For SMALL n (8,12) the recorded incidence exceeds budget AT the Johnson rung (9>8, 13>12).
  A bad point at the Johnson radius gives only `δ* ≤ δ_J` for the supremum-defined threshold;
  a strict `δ* < δ_J` needs a separate endpoint argument (the good radii below can have
  supremum equal to the bad boundary).
* For n = 16, 20 the recorded Johnson-rung values are within budget (I=9≤16, I=5≤20), as is one
  rung beyond; two rungs past Johnson the recorded values exceed budget (89, 3696; 121, 27241).
* The ratios `89/16`, `3696/16`, `27241/20` are finitely many comparisons at fixed block
  lengths. They do NOT refute every fixed linear constant or a `Θ(n)` asymptotic: at a fixed
  block length and radius grid there are only finitely many values.

What this suggests (not proved): the char-0 upper envelope, at these recorded radii, does not
certify the prize budget `q·ε* = n` two rungs past Johnson. A failed char-0 certificate at one
deeper radius does not preclude the same route proving a smaller improvement above Johnson, and
a literal prize-field budget must be checked with its exact correction. This is recorded
evidence AGAINST the conjecture `Char0DeployedIncidenceWithinBudgetPastJohnson` at the stated
rows, not a Lean refutation of it (the conjecture's objects do not appear in this file).

All facts below are pure `Nat` arithmetic on the entered rows, discharged by `decide`, and
depend on no axioms (verified by the `#print axioms` lines below).
-/

namespace ProximityGap.Char0CountBound

/-- The prize budget at rate `ρ = 1/4`, `ε* = 2⁻¹²⁸`, `q ≈ n·2¹²⁸`: `q·ε* = n`. -/
def budget (n : ℕ) : ℕ := n

/-- A recorded probe row: six unconstrained natural numbers `(n, k, r, a, b, I)`, intended as
the char-0 far-line incidence `I` at rung `r` for direction `(a, b)` in the rate-`1/4` family.
Nothing in this structure ties the fields to an actual code, pencil, radius or count; the
intended meaning is provenance only (see the module docstring). -/
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

-- ## The recorded char-0 incidences (probe provenance; not proved counts).

/-- n=8, k=2: AT the Johnson rung r=4, the worst far direction (a,b)=(5,2) has I=9. -/
def d8_J  : Datum := ⟨8, 2, 4, 5, 2, 9⟩
-- The former row `d8_J1 = ⟨8, 2, 5, 0, 2, 40⟩` (and its comparison `d8_J1_bad`) is retired: under
-- the monomial pencil `1 + γX²` reading its bad-scalar set has size `1`, not `40` (module doc).

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

-- ## Arithmetic on the entered rows: for n = 16, 20 the recorded Johnson-rung values are within
-- budget (a comparison of entered integers, not a proved incidence bound).

theorem d16_J_ok  : d16_J.I ≤ budget d16_J.n := by decide
theorem d16_J1_ok : d16_J1.I ≤ budget d16_J1.n := by decide
theorem d20_J_ok  : d20_J.I ≤ budget d20_J.n := by decide
theorem d20_J1_ok : d20_J1.I ≤ budget d20_J1.n := by decide

-- ## Arithmetic on the entered rows: for n = 8, 12 the recorded Johnson-rung values exceed the
-- budget. If those rows are the actual counts, a bad point at δ_J gives only δ* ≤ δ_J (strict
-- `<` needs an endpoint argument); the probe's separate δ* = 3/8 report for n=8 is not proved here.

theorem d8_J_bad  : d8_J.I  > budget d8_J.n  := by decide
theorem d12_J_bad : d12_J.I > budget d12_J.n := by decide

-- ## Arithmetic on the entered rows: recorded past-Johnson values exceed the budget.

theorem d12_J2_bad : d12_J2.I > budget d12_J2.n := by decide
theorem d16_J2_bad : d16_J2.I > budget d16_J2.n := by decide
theorem d16_J3_bad : d16_J3.I > budget d16_J3.n := by decide
theorem d20_J2_bad : d20_J2.I > budget d20_J2.n := by decide
theorem d20_d4_bad : d20_d4.I > budget d20_d4.n := by decide

-- ## Finite ratio comparisons on the entered rows.

/-- Finite comparisons of entered rows with explicit multiples of `n`: `89 > 5·16`,
`3696 > 5·16`, `3696 > 200·16`, `27241 > 1000·20`. These are single comparisons at fixed block
lengths; they do NOT refute any fixed linear constant `C` or a `Θ(n)` asymptotic law (that would
need an infinite family of actual counts). -/
theorem d16_J2_super_linear : d16_J2.I > 5 * d16_J2.n := by decide
theorem d16_J3_super_5n     : d16_J3.I > 5 * d16_J3.n := by decide
theorem d16_J3_super_200n   : d16_J3.I > 200 * d16_J3.n := by decide
theorem d20_d4_super_1000n  : d20_d4.I > 1000 * d20_d4.n := by decide

/-- **Existence of an over-budget recorded row past the Johnson rung.** Some `Datum` has
`r > n/2`, `I > n` and `I > 5n`; the witness is the recorded row `(n=16, r=10, I=89)`.

Because `Datum` is unconstrained, this statement is satisfiable by an arbitrary record and has
no prize content by itself: it does NOT prove that the actual char-0 deployed incidence exceeds
the budget, that the `char-p ≤ char-0` cap fails, or any asymptotic growth. Its mathematical
reading depends entirely on the unproved identification of `d16_J2` with an actual count. -/
theorem exists_recorded_datum_past_johnson_over_budget :
    ∃ d : Datum, johnsonRung d.n < d.r ∧ budget d.n < d.I ∧ 5 * d.n < d.I := by
  refine ⟨d16_J2, ?_, ?_, ?_⟩ <;> decide

/-- Historical name of `exists_recorded_datum_past_johnson_over_budget`. The old name overstated
the content (it is an existential over unconstrained data, not a refutation of the cap route). -/
@[deprecated exists_recorded_datum_past_johnson_over_budget (since := "2026-10-28")]
theorem cap_route_does_not_close :
    ∃ d : Datum, johnsonRung d.n < d.r ∧ budget d.n < d.I ∧ 5 * d.n < d.I :=
  exists_recorded_datum_past_johnson_over_budget

end ProximityGap.Char0CountBound

#print axioms ProximityGap.Char0CountBound.exists_recorded_datum_past_johnson_over_budget
#print axioms ProximityGap.Char0CountBound.d16_J2_bad
#print axioms ProximityGap.Char0CountBound.d20_J_ok
#print axioms ProximityGap.Char0CountBound.d16_J3_super_200n
