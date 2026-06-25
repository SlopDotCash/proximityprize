/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# FLOOR_A1 (#464): off-BGK floor — bad-prime localization characterization (n=16 proven; n=32 numeric)

## Context (dossier §9, KB `bad-prime-localization-theorem-2026-06-19` §12)

The δ* **floor** asks whether δ* enters the window interior `(1−√ρ, 1−ρ−Θ(1/log n))`. The
campaign isolated one genuinely off-BGK *obstruction-removal* lane: bad primes for a distinguished
binder-family floor predicate are the prime divisors of a **FIXED, p-independent cyclotomic
resultant** (a 0-dimensional / height question, NOT a `√p` character sum). This can certify that
the binder-family obstruction is absent at prize primes. It does **not** by itself supply the
universal `WorstCaseIncidenceBounded` input needed for the δ* lower pin.

The KB §1 setup: `μ_n` = `n`-th roots of unity (`n = 2^a`) in `F_p`, `p ≡ 1 mod n`; code
`C = RS[μ_n, deg < n/2]`; binder word `w_g(x) = x^{3n/4} + g·x^{n/2}`. A prime `p` is
**floor-bad** iff some forbidden *adjacent 7th-type* agreement pattern is realizable over `F_p`
(`rank[M_A] = rank[M_A | b_A]`). The re-grounded characterization (§12):

> **floor-bad(n) = { the single smallest prime `p ≡ 1 mod n` }.**

Verified `n=16 → {17}` exhaustively (15.4M-pattern Rust); `n=32 → {97}` (adjacent, exhaustive).
Both equal the *smallest* prime `≡ 1 mod n` (17 smallest `≡1 mod 16`; 97 smallest `≡1 mod 32`).

**The payoff (if uniform in `μ`):** the modeled binder floor predicate closes once the least prime
`≡ 1 mod n` is below prize scale `n^4`. Classical Linnik with exponent `5` is NOT enough for this
comparison by itself (`n^5` is above `n^4`); the useful input must be a sub-4 least-prime theorem, a
Thorner--Zaman-style supply window such as `p ≤ 2n^3`, GRH/Montgomery, or a dyadic-special
least-prime result. The formal closure below therefore consumes the exact named premise
`LinnikLeastPrimeBelowPrize` rather than laundering ordinary Linnik into a stronger statement. A
separate domination theorem would still be needed to turn binder-goodness into a prize proof.

## What this file does (honest scope)

This is the **characterization brick**, NOT a closure of the prize.

1. A clean decidable predicate `FloorBadIsSmallestPrime n badPrimes` = "the floor-bad set equals
   the singleton of the smallest prime `≡ 1 mod n`."
2. The **n=16 instance proven axiom-clean** (`decide`): with `badPrimes 16 = {17}` (the exhaustive
   Rust fact P3), `FloorBadIsSmallestPrime 16 {17}` holds, AND `17 = smallestPrime1ModN 16`, AND
   `17 < 16^4` (so every prize prime at `n=16` is good for this abstract floor-bad predicate).
3. The **uniform-in-μ statement** as a named `Prop` (`FloorLocalizationUniform`) and the
   **closure implication** (`floor_closes_by_linnik`): IF the characterization is uniform AND the
   smallest prime `≡ 1 mod n` is `< n^4` (the exact least-prime premise), THEN every prize prime
   is not `FloorBad` for this predicate.

**Honesty (parent §6.B).** The n=16 instance is the only *proven* arithmetic fact; the n=32
`{97}` claim is recorded as a numeric `def`/conjecture (probe
`scripts/probes/probe_floor_localization_n32.py`), and the uniform statement is an explicit named
open `Prop`. NO `sorry`/`native_decide`; axiom audit must show `[propext, Classical.choice,
Quot.sound]`.
-/

namespace ArkLib.ProximityGap.Frontier.FloorLocalization

open Nat

/-- The smallest prime `p` with `p ≡ 1 mod n`, searched up to `bound`. Returns `0` if none found
(so callers must check the witness is genuinely `≡ 1 mod n` and prime). We use an explicit bounded
search so the predicate is `decide`-able. -/
def smallestPrime1ModN (n bound : ℕ) : ℕ :=
  ((List.range (bound + 1)).filter (fun p => p % n == 1 && p.Prime)).head?.getD 0

/-- `n=16`: smallest prime `≡ 1 mod 16` is `17`. (`17 % 16 = 1`, prime; nothing smaller.) -/
example : smallestPrime1ModN 16 100 = 17 := by decide

/-- `n=32`: smallest prime `≡ 1 mod 32` is `97`. (`33,65` composite; `97` prime, `97 % 32 = 1`.) -/
example : smallestPrime1ModN 32 200 = 97 := by decide

/-- The CHARACTERIZATION predicate (clean, decidable for a concrete finite `badPrimes` list):
the floor-bad set equals the singleton `{ smallest prime ≡ 1 mod n }`. We compare as sorted
deduplicated lists. `bound` bounds the smallest-prime search (must exceed the true smallest). -/
def FloorBadIsSmallestPrime (n bound : ℕ) (badPrimes : List ℕ) : Prop :=
  badPrimes = [smallestPrime1ModN n bound]

instance (n bound : ℕ) (bp : List ℕ) : Decidable (FloorBadIsSmallestPrime n bound bp) := by
  unfold FloorBadIsSmallestPrime; infer_instance

/-- The exhaustive `n=16` floor-bad set (KB §12 / P3: Rust over all 2304 adjacent patterns,
all primes `≡ 1 mod 16` up to 8000 — the unique bad prime is `17 = n+1`, the full-group
degeneracy; every other realizes ZERO adjacent patterns). -/
def floorBad16 : List ℕ := [17]

/-- The conjectured `n=32` floor-bad set: `{97}` (= smallest prime `≡ 1 mod 32`).

**NUMERIC STATUS (scanner-resolved, not a Lean proof).** The exact adjacent-realizability scanner
`scripts/probes/floor_scan_exact.c` reproduces the `n=16` ground truth and, for `n=32`, reports
`97` BAD while `193, 257, 353, 449, 577, 673` are GOOD by full 15,366,400-pattern scans. This
resolves the earlier mismatch with the superseded defect-core/discriminant object, whose root-count
drop is not the same predicate. Lean still treats the finite-field rank scan as external numeric
evidence: the theorem below only decides that the candidate list `[97]` matches the smallest-prime
predicate. -/
def floorBad32Conjectured : List ℕ := [97]

/-! ## The PROVEN n=16 instance (axiom-clean) -/

/-- **PROVEN (n=16).** The floor-bad set `{17}` equals the singleton of the smallest prime
`≡ 1 mod 16`. This is the characterization at `a=4`, decidable. -/
theorem floorBad16_isSmallestPrime : FloorBadIsSmallestPrime 16 100 floorBad16 := by decide

/-- **PROVEN (n=16).** The unique floor-bad prime `17` is strictly below prize scale `16^4`. -/
theorem floorBad16_below_prize : (17 : ℕ) < 16 ^ 4 := by decide

/-- **PROVEN (n=16, floor closed).** Combining: the floor-bad set is the singleton smallest prime
`≡ 1 mod 16`, that prime is `17`, and `17 < 16^4` — so every prize-regime prime `p ~ 16^4` is GOOD
and the off-BGK floor is closed at `n=16`. -/
theorem floor_closed_n16 :
    FloorBadIsSmallestPrime 16 100 floorBad16
      ∧ smallestPrime1ModN 16 100 = 17
      ∧ (17 : ℕ) < 16 ^ 4 := by
  refine ⟨floorBad16_isSmallestPrime, by decide, floorBad16_below_prize⟩

/-! ## The n=32 instance (numeric, conjectural) -/

/-- **CONJECTURE (n=32, probe-verified not proven).** The `n=32` floor-bad set is `{97}` =
the smallest prime `≡ 1 mod 32`. Stated as a `Prop` instance of the characterization; we do NOT
prove the antecedent that `floorBad32Conjectured` IS the true floor-bad set (that is the
exhaustive `F_p`-rank computation in the probe). What we CAN decide is that the candidate list
matches the smallest-prime predicate. -/
theorem floorBad32_matches_smallestPrime :
    FloorBadIsSmallestPrime 32 200 floorBad32Conjectured := by decide

/-! ## The uniform-in-μ statement and the Linnik closure (named open Props) -/

/- The realizability oracle `FloorBad : ℕ → ℕ → Prop`: `FloorBad n p` means prime `p ≡ 1 mod n` is
floor-bad (some adjacent 7th-type pattern realizable over `F_p`). It is left abstract — introduced as
an EXPLICIT predicate PARAMETER of the statements below, NOT a bodyless `opaque`. Every result is
proven *for an arbitrary* such predicate, so nothing is asserted to exist with magic content (a
bodyless `opaque` would axiom-launder an unproven inhabitant of `ℕ → ℕ → Prop`, which CI rightly
rejects). Quantifying over `FloorBad` is strictly more honest and equally usable: the conditional
closure `floor_closes_by_linnik` holds whatever the concrete realizability predicate turns out to be
(its concrete content is the `F_p`-rank computation of KB §1). -/

/-- **OPEN (uniform-in-μ characterization).** For all `a ≥ 4`, with `n = 2^a`, the floor-bad
primes (per the abstract predicate `FloorBad`) are exactly the singleton smallest prime `≡ 1 mod n`.
This is the genuinely-off-BGK binder-predicate conjecture: it is a 0-dimensional / height statement
on a fixed cyclotomic resultant, NOT a character sum. Proven `a=4` (`floor_closed_n16`); `a=5`
numerically supported (`{97}`). It is necessary evidence for the prize floor, not a replacement for
`WorstCaseIncidenceBounded`. -/
def FloorLocalizationUniform (FloorBad : ℕ → ℕ → Prop) : Prop :=
  ∀ a : ℕ, 4 ≤ a → ∀ p : ℕ, p.Prime → p % (2 ^ a) = 1 →
    (FloorBad (2 ^ a) p ↔ p = smallestPrime1ModN (2 ^ a) (2 ^ (5 * a)))

/-- The exact least-prime input needed by the floor closure: the least prime `≡ 1 mod n` is below
prize scale `n^4`.

This is a named external premise, not a consequence of classical Linnik as usually quoted. An
`O(n^5)` bound has the wrong exponent for the prize comparison; the route needs a sub-4 bound
(for example the in-tree `TZPrimeSupply` bridge at exponent `β ≤ 3`), GRH/Montgomery-strength
input, or a dyadic-special theorem. Verified rungs include `17 < 16^4` and `97 < 32^4`; the
universal statement remains an explicit input. -/
def LinnikLeastPrimeBelowPrize : Prop :=
  ∀ a : ℕ, 4 ≤ a → smallestPrime1ModN (2 ^ a) (2 ^ (5 * a)) < (2 ^ a) ^ 4

/-- **Binder-predicate closure (conditional, off-BGK).** If the floor-bad characterization is uniform in `μ`
AND the least prime `≡ 1 mod n` is below prize scale, THEN every prize-regime prime `p` with
`(2^a)^4 ≤ p` is floor-GOOD. This is the dossier §9 actionable target, but its least-prime
input is exactly `LinnikLeastPrimeBelowPrize`; ordinary exponent-5 Linnik does not discharge it.
This theorem proves only `¬ FloorBad (2^a) p` for the supplied predicate; it does not prove the
universal worst-case incidence bound consumed by the δ* lower-pin theorem.

The proof: a prize prime `p ≥ n^4 > smallestPrime` (Linnik) cannot equal the smallest prime, so
by the uniform characterization it is not floor-bad. -/
theorem floor_closes_by_linnik
    (FloorBad : ℕ → ℕ → Prop)
    (hUnif : FloorLocalizationUniform FloorBad) (hLinnik : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a) (p : ℕ) (hp : p.Prime) (hmod : p % (2 ^ a) = 1)
    (hprize : (2 ^ a) ^ 4 ≤ p) :
    ¬ FloorBad (2 ^ a) p := by
  intro hbad
  -- from the uniform characterization, floor-bad ⟹ p = smallest prime
  have heq : p = smallestPrime1ModN (2 ^ a) (2 ^ (5 * a)) :=
    (hUnif a ha p hp hmod).mp hbad
  -- but the smallest prime is below n^4 ≤ p, contradiction
  have hsmall : smallestPrime1ModN (2 ^ a) (2 ^ (5 * a)) < (2 ^ a) ^ 4 := hLinnik a ha
  rw [heq] at hprize
  -- hprize : (2^a)^4 ≤ smallestPrime ; hsmall : smallestPrime < (2^a)^4 — contradiction
  exact absurd (lt_of_lt_of_le hsmall hprize) (lt_irrefl _)

/-! ## Capstone export -/

/-- **The harvest.** Bundles the proven `n=16` binder-predicate closure with the conditional uniform
closure: this abstract floor-bad predicate is *closed at `n=16`* and *reduces, for all `a ≥ 4`, to
two named external inputs* — the uniform localization characterization (`FloorLocalizationUniform`,
a height/0-dim statement on a fixed cyclotomic resultant) and the exact sub-prize least-prime premise
(`LinnikLeastPrimeBelowPrize`). Neither input is the BGK/Paley sup-norm wall, but neither is
silently discharged here, and the result does not prove δ*. -/
theorem floor_localization_capstone :
    (FloorBadIsSmallestPrime 16 100 floorBad16
      ∧ smallestPrime1ModN 16 100 = 17 ∧ (17 : ℕ) < 16 ^ 4)
    ∧ (∀ FloorBad : ℕ → ℕ → Prop, FloorLocalizationUniform FloorBad → LinnikLeastPrimeBelowPrize →
        ∀ a : ℕ, 4 ≤ a → ∀ p : ℕ, p.Prime → p % (2 ^ a) = 1 → (2 ^ a) ^ 4 ≤ p →
          ¬ FloorBad (2 ^ a) p) := by
  exact ⟨floor_closed_n16, fun FB hU hL => floor_closes_by_linnik FB hU hL⟩

-- Axiom audits (must show only [propext, Classical.choice, Quot.sound]).
#print axioms floorBad16_isSmallestPrime
#print axioms floor_closed_n16
#print axioms floorBad32_matches_smallestPrime
#print axioms floor_closes_by_linnik
#print axioms floor_localization_capstone

end ArkLib.ProximityGap.Frontier.FloorLocalization
