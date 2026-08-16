/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NormNum

/-!
# E₃ closed form for 2-power roots of unity — the r=2 rung producer (#444)

## What this file is

The δ\* prize reduces (proven spines) to the char-`p` validity of the DC-subtracted Wick
bound `A_r = E_r − n^{2r}/q ≤ (2r−1)‼·n^r` at depth `r ≈ log m`. The SHALLOW rungs
(`r ≤ rMax ≈ 2β`) are provable in char `p` and DISCHARGE part of the spine. The `r = 1`
rung is already discharged from `E_2(μ_n) = 3n² − 3n` (`additiveEnergy_eq_of_sidonModNeg`).
**The r=2 rung's entire remaining producer obstruction** is the `r=3` analogue:

> `E_3(μ_{2^μ}) = zeroSumCount(μ_n, 6) = 15 n³ − 45 n² + 40 n`  exactly, for 2-power `n`.

(`E_3(μ_n)` = additive energy of order 3 = `#{6-tuples of n-th roots summing to 0}` after
the `(v,w) ↦ (v,−w)` negation bijection — `zeroSumCount G 6` in
`NegationClosedWalkBound.lean`.)

## The clean combinatorial reduction (this file's content)

The count factors into a **field-independent combinatorial identity** over the exponent
group `ZMod n`, plus ONE deep char-0 structural input (Lam–Leung), exactly mirroring how
the `E_2 = 3n²−3n` anchor was built. Write `n`-th roots as exponents in `ZMod n`, with the
antipode `−ζ^a = ζ^{a + n/2}` being the shift `+ n/2`.

* **`matchable n t`** — a 6-tuple of exponents `t : Fin 6 → ZMod n` is *antipodally
  matchable* iff its value-distribution is invariant under the antipodal shift `+ n/2`:
  for every value `x`, `#{i : t i = x} = #{i : t i = x + n/2}`. (Machine-verified in
  `scripts/probes/probe_e3_decomp.py` to coincide with "the 6 positions partition into 3
  antipodal pairs"; the slick distribution form is what makes the count tractable.)

* **`matchableCount n`** — the number of matchable 6-tuples over `ZMod n`. This is the
  PURELY COMBINATORIAL object: it has nothing to do with the prime `p`.

* **THE COUNT** (`MatchableCountClosedForm`, this file's combinatorial core) —
  `matchableCount n = 15 n³ − 45 n² + 40 n` for every even `n`. Proof skeleton (the
  generating-function count, fully verified numerically in
  `scripts/probes/probe_e3_inclexcl.py` and `probe_e3_closedform.py`):
  with `m = n/2` antipodal classes, a matchable tuple chooses, for each class `j`, a count
  `k_j ≥ 0` of antipodal pairs landing in it, with `∑ k_j = 3`, then distributes the 6
  labelled positions as `6! / ∏_j (k_j!)²`. Only three shapes of `(k_j)` sum to 3:
  `120 m³ − 180 m² + 80 m = 20·m + 180·m(m−1) + 120·m(m−1)(m−2)`, and `m = n/2` gives
  `15 n³ − 45 n² + 40 n`. **Base cases `n = 2` and `n = 4` are proven here axiom-clean by
  `decide`** (`matchableCount_two`, `matchableCount_four`); the general identity is the named
  combinatorial residual (`decide` cannot reach `n ≥ 8`: `8^6 = 262144` tuples overflow the
  kernel — an honest Lean-tooling limit, not a mathematical gap; the closed form is
  machine-checked exact for `n = 2,4,8,16,32`).

* **`LamLeungAntipodalMatchable`** — the deep char-0 input: for 2-power `n`, every zero-sum
  6-tuple of `n`-th roots is antipodally matchable. This is **Lam–Leung on vanishing sums of
  roots of unity** (the only ℤ-relations among `2^μ`-th roots are antipodal pairs). Mathlib
  lacks Lam–Leung; this is the SAME named char-0 wall the whole programme rests on
  (`NegationClosedWalkBound` calls it "the no-genuine-relation residual"). It is FALSE for
  `3 ∣ n` (then `1 + ζ₃ + ζ₃² = 0` supplies non-matchable zero-sum tuples), which is exactly
  why the closed form FAILS for `3 ∣ n` — machine-verified: `zeroSumCount(μ_12,6) = 23160 ≠
  19920` (`probe_e3_closedform.py`). Hence the strict 2-power restriction.

## The bridge (proven axiom-clean here)

`E3_closed_form_of_inputs`: the two named inputs above (`MatchableCountClosedForm` over
`ZMod n` + `LamLeungAntipodalMatchable` for 2-power `n`) give
`zeroSumCount(μ_n, 6) = 15 n³ − 45 n² + 40 n` — **discharging the r=2 rung's producer
obstruction modulo exactly those two named hypotheses**, one of which (`MatchableCount-
ClosedForm`) is a finite field-independent combinatorial identity (proven for `n=2`,
machine-checked for the tower) and the other (`LamLeungAntipodalMatchable`) is the standing
char-0 Lam–Leung input the programme already names everywhere.

## Honesty status

PROVEN axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`):
`matchableCount_two` (the `n=2` base value `= 20`), the definitions, and the bridge
`E3_closed_form_of_inputs`. NAMED open inputs (not claimed proven): the general
`MatchableCountClosedForm` (combinatorial, `n=2` discharged, tower machine-checked) and
`LamLeungAntipodalMatchable` (the char-0 Lam–Leung wall). This is a clean
*reduces-to-named-inputs*, not a closure — but the inputs are sharply isolated and one is a
pure finite combinatorial fact.

## References
* `NegationClosedWalkBound.lean` (`zeroSumCount`, the K1 upper bound `≤ (2r−1)‼·n^r`).
* `AdditiveEnergySidonModNeg.lean` (`additiveEnergy_eq_of_sidonModNeg`, the `E_2` anchor).
* Probes: `probe_e3_closedform.py`, `probe_e3_decomp.py`, `probe_e3_inclexcl.py`.
-/

set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.E3ClosedForm

/-! ## The field-independent combinatorial object over the exponent group -/

/-- A 6-tuple of exponents `t : Fin 6 → ZMod n` is **antipodally matchable** iff its
value-distribution is invariant under the antipodal shift `x ↦ x + n/2`: for every value
`x`, the number of positions mapping to `x` equals the number mapping to its antipode
`x + n/2`. (Machine-verified equivalent to "the 6 positions partition into 3 antipodal
pairs"; see `probe_e3_decomp.py`.) -/
def matchable (n : ℕ) [NeZero n] (t : Fin 6 → ZMod n) : Prop :=
  ∀ x : ZMod n, (Finset.univ.filter (fun i => t i = x)).card
              = (Finset.univ.filter (fun i => t i = x + (n / 2 : ℕ))).card

instance (n : ℕ) [NeZero n] (t : Fin 6 → ZMod n) : Decidable (matchable n t) := by
  unfold matchable; infer_instance

/-- The **matchable count**: the number of antipodally-matchable 6-tuples over `ZMod n`.
This is the purely combinatorial object — independent of the field/prime. -/
def matchableCount (n : ℕ) [NeZero n] : ℕ :=
  (Finset.univ.filter (fun t : Fin 6 → ZMod n => matchable n t)).card

/-- The target cubic `15 n³ − 45 n² + 40 n`, phrased over `ℤ` to avoid `Nat`-truncation
pitfalls with the intermediate subtraction. (The value is a nonnegative integer for all `n`:
it factors as `5n(3n² − 9n + 8)` with `3n² − 9n + 8 > 0` always.) -/
def e3Cubic (n : ℕ) : ℤ := 15 * (n : ℤ) ^ 3 - 45 * (n : ℤ) ^ 2 + 40 * (n : ℤ)

/-! ## Axiom-clean base case: `n = 2` -/

/-- **Base case `n = 2`, proven axiom-clean by `decide`.** The matchable count for `n = 2`
is `20`, matching `e3Cubic 2 = 15·8 − 45·4 + 40·2 = 120 − 180 + 80 = 20`. This is the
smallest instance of the prize 2-power tower (`2^6 = 64` tuples). -/
theorem matchableCount_two : matchableCount 2 = 20 := by decide

/- **Second 2-power instance `n = 4`, proven axiom-clean by `decide`** (`matchableCount_four`
below). The matchable count for `n = 4` is `400 = e3Cubic 4 = 15·64 − 45·16 + 40·4 = 960 −
720 + 160`. (`4^6 = 4096` tuples; reachable by the kernel with the raised recursion/heartbeat
limits below. `n ≥ 8` — `8^6 = 262144` tuples — is over the kernel's brute-force ceiling, an
honest *tooling* limit, not a math gap: the closed form is machine-checked exact for
`n = 8,16,32` in `probe_e3_closedform.py`.) -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem matchableCount_four : matchableCount 4 = 400 := by decide

/-- `e3Cubic 2 = 20`: the base value matches the cubic. -/
theorem e3Cubic_two : e3Cubic 2 = 20 := by decide

/-- `e3Cubic 4 = 400`: the `n=4` value matches the cubic. -/
theorem e3Cubic_four : e3Cubic 4 = 400 := by decide

/-- The base case stated against the closed form: `matchableCount 2 = e3Cubic 2`. -/
theorem matchableCount_two_eq_cubic : (matchableCount 2 : ℤ) = e3Cubic 2 := by
  rw [matchableCount_two, e3Cubic_two]; norm_num

/-- The `n=4` case stated against the closed form: `matchableCount 4 = e3Cubic 4`. -/
theorem matchableCount_four_eq_cubic : (matchableCount 4 : ℤ) = e3Cubic 4 := by
  rw [matchableCount_four, e3Cubic_four]; norm_num

/-! ## The named combinatorial residual (general closed form) -/

/-- **The combinatorial core** (named open input, `n = 2` discharged above, machine-checked
exact for `n = 2,4,8,16,32` in `probe_e3_closedform.py`). For every even `n`, the matchable
count equals the cubic `15 n³ − 45 n² + 40 n`. This is a FINITE, FIELD-INDEPENDENT
combinatorial identity (the generating-function count over `n/2` antipodal classes); it is
NOT the deep char-0 wall — that is `LamLeungAntipodalMatchable` below. -/
def MatchableCountClosedForm : Prop :=
  ∀ (n : ℕ) [NeZero n], Even n → (matchableCount n : ℤ) = e3Cubic n

/-! ## The deep char-0 structural input (Lam–Leung)

**The Lam–Leung antipodal-matchability input** (named char-0 wall). For 2-power `n`, under
any faithful realization of `μ_n` in a field of characteristic 0 (or large enough char),
every zero-sum 6-tuple of `n`-th roots, transported to its exponent tuple
`t : Fin 6 → ZMod n`, is antipodally matchable — and this transport is a *bijection* onto
the matchable tuples. Hence the realized zero-sum 6-tuple count of `μ_n` equals
`matchableCount n`. This is Lam–Leung on vanishing sums of roots of unity (the only
ℤ-relations among `2^μ`-th roots are antipodal pairs); Mathlib lacks it. It is the SAME
named char-0 input the programme rests on (`NegationClosedWalkBound`'s "no-genuine-relation
residual"). It is FALSE for `3 ∣ n` (`1 + ζ₃ + ζ₃² = 0` gives non-matchable zero-sum
tuples), which is exactly why the closed form fails for `3 ∣ n`.

We do NOT axiomatize a vacuous wrapper for it. Instead the bridge below consumes its precise
content — the equality `Z = matchableCount n` — as an explicit hypothesis `hLL`, so the
open input is named exactly where it is used and nowhere laundered. -/

/-! ## The bridge: named inputs ⟹ the E₃ closed form

We state the bridge at the level of the abstract zero-sum count `Z`. The consumer supplies
`Z = zeroSumCount(μ_n, 6)` and the Lam–Leung identity `Z = matchableCount n`; the
combinatorial closed form then pins `Z = e3Cubic n`. -/

/-- **The bridge (proven axiom-clean).** If the general combinatorial closed form holds and
the realized zero-sum count of `μ_n` equals the matchable count (the Lam–Leung transport),
then `Z = 15 n³ − 45 n² + 40 n`. For 2-power `n` both hypotheses are the named inputs above;
this discharges the r=2 rung's producer obstruction modulo exactly those. -/
theorem E3_closed_form_of_inputs (n : ℕ) [NeZero n] (hn : Even n)
    (hcomb : MatchableCountClosedForm)
    (Z : ℕ) (hLL : Z = matchableCount n) :
    (Z : ℤ) = e3Cubic n := by
  rw [hLL]
  exact hcomb n hn

/-- **Discharged base instance of the bridge (`n = 2`).** The bridge fires *without* the
named combinatorial residual, because the base case is proven: any realized zero-sum count
equal to the matchable count is `20 = e3Cubic 2`. So at `n = 2` the r=2 rung's producer
obstruction reduces to ONLY the Lam–Leung input (`Z = matchableCount 2`). -/
theorem E3_closed_form_two (Z : ℕ) (hLL : Z = matchableCount 2) :
    (Z : ℤ) = e3Cubic 2 := by
  rw [hLL, matchableCount_two_eq_cubic]

/-- **Discharged instance of the bridge (`n = 4`).** Same as `E3_closed_form_two` but for
the second 2-power instance: the combinatorial residual is proven (`matchableCount 4 = 400`),
so at `n = 4` the obstruction reduces to ONLY the Lam–Leung input. -/
theorem E3_closed_form_four (Z : ℕ) (hLL : Z = matchableCount 4) :
    (Z : ℤ) = e3Cubic 4 := by
  rw [hLL, matchableCount_four_eq_cubic]

/-! ## Source audit -/

#print axioms matchableCount_two
#print axioms matchableCount_four
#print axioms matchableCount_two_eq_cubic
#print axioms matchableCount_four_eq_cubic
#print axioms E3_closed_form_of_inputs
#print axioms E3_closed_form_two
#print axioms E3_closed_form_four

end ArkLib.ProximityGap.E3ClosedForm
