/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

/-!
# D3 — Why the A3 Parseval threshold does NOT extend to s = 128 (#444, route D re-attack)

## Background: the A3 Parseval threshold mechanism that made s = 64 unconditional

The [KKH26] ceiling needs a prime `p ≡ 1 (mod n)` that divides none of the collision
resultants `R_{(d,d')} = Res_ℤ(P_d − P_{d'}, Φ_{2^μ})`.  Two routes discharge this:

* **TZ route (PNT-in-APs)** — exhibit enough primes in `[n^β, 2n^β]` that the `O(log)` bad
  primes per resultant cannot exhaust them.  Needs the analytic Thorner–Zaman input
  (`TZPrimeSupply`, still a named `Prop`).
* **A3 Parseval threshold route** — bound the *size* of each resultant so tightly that
  `|R_{(d,d')}| < p` already, whence NO prime `≥ p` can divide it and EVERY prize-regime
  prime is automatically good — no analytic input at all.  This is the Landau ℓ²-sharpening
  `natAbs_resultant_cyclotomic_sq_le` (`SharpResultantBound.lean`): via the Mahler measure
  and Landau's inequality `M(R) ≤ ‖R‖₂` (a Parseval / second-moment estimate on the
  coefficients),

    `|Res_ℤ(R, Φ_{2^m})|² ≤ 4^{deg R} · (∑_i |R_i|²)^{2^{m−1}} =: landauSqEnvelope(2^{m−1})`,
    `landauSqEnvelope(h) = (4h)^h · 2^{h−1}`     (`h = 2^{m−1}`, coeffs in {−2..2}, deg < h).

  The unconditional discharge is exactly the inequality `landauSqEnvelope(2^{m−1}) < p²`
  (`collisionResultant_not_dvd_of_cyclotomicLandauSqBound`, `KKH26SumsOfRootsOfUnity.lean`).

## The arithmetic — why it stops at s = 64

* **μ = 6, s = 64, h = 32:** `landauSqEnvelope(32) = (128)^32 · 2^31 = 2^{224} · 2^{31} = 2^255`,
  so the discharge needs `p² > 2^255`, i.e. `p > 2^{127.5}`.  The prize-regime s = 64 prime
  is `p ≈ 2^128` (`Mu6ConditionalPin`: `P = 1526377·2^128 + 1`), which clears `2^{127.5}` —
  so **s = 64 is unconditional**, exactly as recorded in the #334 ledger.

* **μ = 7, s = 128, h = 64:** `landauSqEnvelope(64) = (256)^64 · 2^63 = 2^{512} · 2^{63} = 2^575`
  (`landauSq_s128_eq` below, exact `norm_num`).  The discharge needs `p² > 2^575`, i.e.
  `p > 2^{287.5}`.

## The decisive obstruction (this file's content)

The s = 128 prize-regime fields are POLYNOMIAL in the domain `p = Θ(n^β)`, and the budget
inequality (★) of `KKH26S128Ceiling.lean` forces only a MODERATE `β`.  The probe
`scripts/probes` solving (★) at `n = 2^30` gives (also in the `KKH26S128Ceiling` docstring):

    ρ = 1/16 (r = 9):  β ≈ 3.98,  p ≈ n^β ≈ 2^119
    ρ = 1/8  (r = 17): β ≈ 5.53,  p ≈ n^β ≈ 2^166
    ρ = 1/4  (r = 33): β ≈ 7.28,  p ≈ n^β ≈ 2^218

EVERY one of these is far below the `2^{287.5}` the Parseval route demands
(`prize_s128_field_below_parseval_threshold` below).  Hence the A3 mechanism canNOT make any
s = 128 prize row unconditional: the resultant is LARGER than the field, so primes `≥ p` CAN
divide it and one must count/avoid bad primes — exactly the TZ analytic input.

**Is the gap a loose constant or fundamental?**  Fundamental.  Exact-arithmetic
(`scripts/probes`, no floats) measurement of the TRUE collision-resultant magnitude
`log₂|Res(R, X^{64}+1)|` for the constrained coefficient class (`∑|R_i|² ≤ 4h`, support of
size `≈ 2r`) gives, at the prize rows:

    nz ≈ 16 (ρ=1/16): log₂|Res| ≈ 177  >  log₂ p ≈ 119
    nz ≈ 32 (ρ=1/8 ): log₂|Res| ≈ 204  >  log₂ p ≈ 166
    nz ≈ 64 (ρ=1/4 ): log₂|Res| ≈ 231  >  log₂ p ≈ 218

so even the EXACT (Landau-free) resultant exceeds the field in every prize row — the
mechanism `|Res| < p` is information-theoretically unavailable at s = 128, not merely
blocked by a loose Mahler/Landau constant.  The reason is structural: `Res(R, X^h+1)` is a
product of `h` evaluations of an `h`-term `±2` polynomial, hence `≈ 2^{Θ(h log h)}` — which
dwarfs `p = n^β = 2^{O(β log n)}` once `β` is moderate, and (★) keeps `β` moderate.

## What this resolves

The route-D re-attack question — "does the A3 Parseval/second-moment trick extend to
s = 128?" — is answered **NO, fundamentally**.  s = 128 genuinely requires the
Thorner–Zaman PNT-in-APs supply (the named `TZPrimeSupply`/`EffectivePNTinAP` hypothesis of
`KKH26S128Ceiling.lean`); no sharpening of the Parseval coefficient bound can replace it,
because the obstruction is the size of the true resultant, not the looseness of the bound.

This file records the threshold arithmetic and the obstruction unconditionally and
axiom-clean; it does NOT claim any closure of s = 128 (which stays conditional on TZ).
Route D RE-ATTACK ⇒ REDUCES-TO-WALL (the wall = the TZ analytic input, unchanged).
-/

namespace ArkLib.ProximityGap.Frontier.AvD3

/-- The squared Landau/Hadamard resultant envelope `(4h)^h · 2^{h−1}` (mirrors
`KKH26SumsOfRootsOfUnity.landauSqEnvelope`; re-declared here with minimal imports). -/
def landauSqEnvelope (h : ℕ) : ℕ := (4 * h) ^ h * 2 ^ (h - 1)

/-- **s = 64 (μ = 6, h = 32) envelope, exact:** `landauSqEnvelope(32) = 2^255`. -/
theorem landauSq_s64_eq : landauSqEnvelope 32 = 2 ^ 255 := by
  unfold landauSqEnvelope; norm_num

/-- **s = 128 (μ = 7, h = 64) envelope, exact:** `landauSqEnvelope(64) = 2^575`.
The Parseval discharge `landauSqEnvelope(64) < p²` therefore needs `p > 2^{287.5}`,
i.e. `p² > 2^575`. -/
theorem landauSq_s128_eq : landauSqEnvelope 64 = 2 ^ 575 := by
  unfold landauSqEnvelope
  have h1 : (4 * 64 : ℕ) = 2 ^ 8 := by norm_num
  rw [h1, ← pow_mul, show (64 - 1) = 63 from rfl, ← pow_add]

/-- **s = 64 unconditional discharge is available:** the prize-regime s = 64 prime
`p ≈ 2^128` satisfies `landauSqEnvelope(32) < p²` (here exhibited via the lower witness
`p ≥ 2^128 > 2^{127.5}`, so `p² ≥ 2^256 > 2^255`). -/
theorem s64_parseval_discharge {p : ℕ} (hp : 2 ^ 128 ≤ p) :
    landauSqEnvelope 32 < p ^ 2 := by
  rw [landauSq_s64_eq]
  calc (2 : ℕ) ^ 255 < 2 ^ 256 := by norm_num
    _ = (2 ^ 128) ^ 2 := by rw [← pow_mul]
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2

/-- **The Parseval threshold for s = 128 is `p² > 2^575`, i.e. `p > 2^{287.5}`.**  Concretely:
the discharge `landauSqEnvelope(64) < p²` FAILS for every `p ≤ 2^287` (since `(2^287)² =
2^574 < 2^575`).  So no prize-regime field below `2^287` can use the A3 Parseval route. -/
theorem s128_parseval_threshold_fails {p : ℕ} (hp : p ≤ 2 ^ 287) :
    p ^ 2 < landauSqEnvelope 64 := by
  rw [landauSq_s128_eq]
  calc p ^ 2 ≤ (2 ^ 287) ^ 2 := Nat.pow_le_pow_left hp 2
    _ = 2 ^ 574 := by rw [← pow_mul]
    _ < 2 ^ 575 := by gcongr <;> norm_num

/-- **The decisive obstruction (prize ρ = 1/4 row, the LARGEST s = 128 field).**  The
budget inequality (★) of `KKH26S128Ceiling.lean` pins the s = 128 ρ = 1/4 field at
`p ≈ 2^218` (β ≈ 7.28, `n = 2^30`).  Even allowing a generous over-estimate `p ≤ 2^287`,
the Parseval discharge `landauSqEnvelope(64) < p²` does NOT hold — so the A3 mechanism
cannot make this (or any smaller-field) s = 128 prize row unconditional. -/
theorem prize_s128_field_below_parseval_threshold {p : ℕ}
    (hfield : p ≤ 2 ^ 287) :
    ¬ landauSqEnvelope 64 < p ^ 2 := by
  have h := s128_parseval_threshold_fails hfield
  omega

/-- **Quantified gap to the largest prize s = 128 field** (ρ = 1/4, `p ≈ 2^218`): the
Parseval bound `landauSqEnvelope(64) = 2^575` exceeds `p²` by a factor `≥ 2^{139}`
(`2^575 / (2^218)² = 2^{575−436} = 2^139`).  A sharper second-moment estimate would have to
shave 139 binary digits off the squared resultant just to reach the ρ = 1/4 field — and the
exact-arithmetic probe shows the TRUE resultant is itself `≈ 2^231 > 2^218`, so no Parseval
sharpening can close even this best case. -/
theorem s128_gap_at_prize_quarter :
    ((2 : ℕ) ^ 218) ^ 2 * 2 ^ 139 = landauSqEnvelope 64 := by
  rw [landauSq_s128_eq, ← pow_mul, ← pow_add]

end ArkLib.ProximityGap.Frontier.AvD3

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.AvD3.landauSq_s64_eq
#print axioms ArkLib.ProximityGap.Frontier.AvD3.landauSq_s128_eq
#print axioms ArkLib.ProximityGap.Frontier.AvD3.s64_parseval_discharge
#print axioms ArkLib.ProximityGap.Frontier.AvD3.s128_parseval_threshold_fails
#print axioms ArkLib.ProximityGap.Frontier.AvD3.prize_s128_field_below_parseval_threshold
#print axioms ArkLib.ProximityGap.Frontier.AvD3.s128_gap_at_prize_quarter
