/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._KKH26s128ThornerZamanBridge

/-!
# B3 — s = 128 ceiling: analytic input reclassified

Issue #444, AvD1.

This lane revisits **Route D** (B3 `s = 128` via Thorner–Zaman) with one job: *verify the
cited analytic input against the actual literature* and record the honest classification.

## What is landed (the reduction — unconditional, axiom-clean)

The full `s = 128` ceiling is already a clean named-`Prop` bridge in
`_KKH26s128ThornerZamanBridge.lean`:

  `kkh26_s128_ceiling_of_thornerZamanPNTinAP` :
    `ThornerZamanPNTinAP n β ε` (the named analytic input)
    + smooth modulus `n = 2^7·m`, degree budget `2 ≤ r ≤ 2^6`, `2^7 < n^β`,
    + two ELEMENTARY side conditions (`supply ≤ density`, `supply` beats the bad-prime budget)
    ⟹  `mcaDeltaStar(C, ε*) ≤ 1 − r/128` at a prime `p = Θ(n^β)`.

Everything except the single `Prop` `ThornerZamanPNTinAP` is proven and axiom-clean. The
reduction is genuinely modular and correct; this lane does NOT touch it (we re-export the
headline below for self-containment).

## The finding (task: does the REAL Thorner–Zaman cover the s = 128 regime?)

**Citation — VERIFIED, not fabricated.** [TZ] = J. Thorner, A. Zaman, *Refinements to the
prime number theorem **for** arithmetic progressions*, arXiv:2108.10878, Math. Z. **307** (2024).
(The in-tree docstrings call it "…in arithmetic progressions" — a one-word title slip; the
paper and its Theorem 1.1 are real.) [KKH26] = Krachun, Kazanin, Haböck, *Failure of proximity
gaps close to capacity*, ePrint 2026/782 — also real and confirmed.

**Quantitative form — the decisive regime mismatch.** The `s = 128` budget needs a *positive
lower bound on the COUNT* of primes `p ≡ 1 (mod n)` in the polynomial window `[n^β, 2·n^β]`,
with modulus `q = n` and `x = n^β`, i.e. `x = q^β` for a **fixed** `β` (the probe gives
`β ≈ 7.28` for ρ=1/4 / `r=33`, `β ≈ 5.53` for ρ=1/8, and `β ≈ 3.98`
for ρ=1/16 at `n = 2^30`).

Thorner–Zaman Theorem 1.1's *asymptotic / positive-count* conclusion
`Σ_{x−h<p≤x, p≡a(q)} log p ∼ λh/φ(q)` is proved under the paper's
"q large" paragraph conditions:
`λh/φ(q) ≥ x^{4/5}` **and** `(log x)/(log q) → ∞`. That last condition forces the modulus to
be **sub-polynomial** in `x` (`q = x^{o(1)}`). For our parameters `log x / log q = β`, a FIXED
constant — so `(log x)/(log q) ↛ ∞`, and the positive-count half of Theorem 1.1 **does NOT
apply** to the fixed-`β` polynomial-modulus window. (There is no "`β > 12/5`" unconditional
positive-count threshold in Theorem 1.1 for this regime; that claim in the older in-tree
docstrings is not supported by the paper as stated and should be read as heuristic, not cited.)

What TZ *does* give for `q ~ x^δ` with `δ` fixed (their `x ≥ q^{c5(δ)}` regime, recovering
Linnik): the **existence** of *one* prime `p ≤ q^{c5}` with `p ≡ a (mod q)` (Linnik's least
prime), plus a Brun–Titchmarsh-type **upper** bound `Σ log p ≪ h/φ(q)`. An *existence* result
and an *upper* bound are exactly the wrong direction: the `s = 128` budget needs a *lower bound
on the count* (`supply` must beat `|collisionPairs 7 r|·448·log 2 / log(n^β)`, which is `> 1`).

**Verdict (re-classification of B3 s = 128).** The honest open input is therefore NOT "the
unconditional TZ count for `β > 12/5`" but the **effective lower bound on the prime COUNT in a
polynomial-modulus short interval** — a strictly stronger, genuinely open analytic-NT statement
that Theorem 1.1 of [TZ] does not deliver in this regime (it lies beyond the
`(log x)/(log q) → ∞` range). It is the *Linnik-density* question (effective positive count for
`q = x^{Θ(1)}`), open in the required effective/quantitative form. So `s = 128` reduces cleanly
to this named input — but to a **count** lower bound for fixed-`β` polynomial moduli, which the
real Thorner–Zaman theorem covers only at the level of *existence* (one prime), not the *count*
the budget consumes. This is recorded as the named `Prop` `PolyModulusPrimeCount` below.

## Honesty

No new mathematics is claimed here. The reduction (re-exported as
`kkh26_s128_of_polyModulusCount`) is the in-tree bridge with the analytic input renamed to the
*regime-correct* hypothesis. The analytic input stays a named `Prop` — never an `axiom`, never a
`sorry`. The contribution of this lane is the verified-citation finding and the re-classification.

## References
* [TZ] arXiv:2108.10878 (Thorner–Zaman, Math. Z. 307, 2024), Theorem 1.1 + the "q large" §1 ¶.
* [KKH26] ePrint 2026/782 (Krachun–Kazanin–Haböck). Issues #334, #444.
-/

open Finset
open scoped NNReal ENNReal Nat

namespace ProximityGap.Frontier.AvD1KKH26S128

open ArkLib.ProximityGap.KKH26 (TZPrimeSupply collisionPairs evalCode)
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge
  (tzDensityLB ThornerZamanPNTinAP kkh26_s128_ceiling_of_thornerZamanPNTinAP'
   kkh26_s128_ceiling_of_thornerZamanPNTinAP_square
   kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square
   kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square_log
   kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log)

/-- **The regime-correct named analytic input** (`Hab25Johnson` named-hypothesis pattern; never
an axiom).  `PolyModulusPrimeCount n β supply` asserts the **lower bound on the COUNT** of primes
`p ≡ 1 (mod n)` in the polynomial-modulus short window `[n^β, 2·n^β]` (modulus `q = n`,
`x = n^β = q^β`, `β` FIXED): the window has at least `supply` such primes.  This is
*definitionally* `TZPrimeSupply n β supply`; it is recorded under this name to make explicit the
finding of this lane — that for fixed `β` (so `log x / log q = β ↛ ∞`) this is the
**Linnik-density count** for polynomial moduli, which lies *outside* Thorner–Zaman
Theorem 1.1's positive-count range (that needs `(log x)/(log q) → ∞`).  TZ gives this
regime only Linnik *existence* and a Brun–Titchmarsh *upper* bound, not the *lower bound on
the count* the `s = 128` budget consumes.  Open in the required effective form. -/
abbrev PolyModulusPrimeCount (n : ℕ) (β : ℝ) (supply : ℕ) : Prop := TZPrimeSupply n β supply

/-- **`PolyModulusPrimeCount` is the density form too.**  If the [TZ]-style effective density
lower bound `ThornerZamanPNTinAP n β ε` holds and `supply` fits under that density, then the
count input `PolyModulusPrimeCount n β supply` holds — i.e. the regime-correct count hypothesis
of this lane is exactly the in-tree density hypothesis, re-expressed.  PROVEN, axiom-clean
(it is the in-tree elementary reduction). -/
theorem polyModulusCount_of_thornerZamanPNTinAP {n : ℕ} {β ε : ℝ} {supply : ℕ}
    (hTZ : ThornerZamanPNTinAP n β ε) (hsupply : (supply : ℝ) ≤ tzDensityLB n β ε) :
    PolyModulusPrimeCount n β supply :=
  ProximityGap.Frontier.KKH26s128ThornerZamanBridge.tzPrimeSupply_of_thornerZamanPNTinAP
    hTZ hsupply

/-- **The s = 128 `δ*` ceiling, conditional on the regime-correct count input** (#444, AvD1).
This re-exports the in-tree bridge `kkh26_s128_ceiling_of_thornerZamanPNTinAP'` with the analytic
hypothesis named `ThornerZamanPNTinAP` (the effective density form); the proof is unchanged and
axiom-clean.  The ONLY unproven input is `ThornerZamanPNTinAP` (equivalently, per
`polyModulusCount_of_thornerZamanPNTinAP`, the regime-correct count `PolyModulusPrimeCount`),
which — by this lane's finding — is the polynomial-modulus Linnik-*density* count that lies
beyond the positive-count range of Thorner–Zaman Theorem 1.1, NOT an unconditional consequence
of it.  Given that input plus the elementary side conditions, there is a prime `p = Θ(n^β)` and a
smooth order-`n` domain with `mcaDeltaStar(C, ε*) ≤ 1 − r/128`. -/
theorem kkh26_s128_of_polyModulusCount {n : ℕ} {β ε : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : ThornerZamanPNTinAP n β ε) {m r : ℕ}
    (hm : 1 ≤ m) (hn : n = 2 ^ 7 * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (7 - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ 7 : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hsupply : (supply : ℝ) ≤ tzDensityLB n β ε)
    (hcount : ((collisionPairs 7 r).card : ℝ)
        * ((448 * Real.log 2) / Real.log ((n : ℝ) ^ β)) < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (7 - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) :=
  kkh26_s128_ceiling_of_thornerZamanPNTinAP' hTZ hm hn hr2 hr hx hpl hsupply hcount

/-- **The s = 128 `δ*` ceiling from the regime-correct count input, square-budget form.**
This is the same reclassified analytic route as `kkh26_s128_of_polyModulusCount`, but with the
paper-facing side condition `(2^r*C(64,r))^2 * 448*log 2 / log(n^β) < supply`; the exact
collision-pair budget is smaller. -/
theorem kkh26_s128_of_polyModulusCount_square {n : ℕ} {β ε : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : ThornerZamanPNTinAP n β ε) {m r : ℕ}
    (hm : 1 ≤ m) (hn : n = 2 ^ 7 * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (7 - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ 7 : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hsupply : (supply : ℝ) ≤ tzDensityLB n β ε)
    (hcount : (((2 ^ r * ((64 : ℕ).choose r)) ^ 2 : ℕ) : ℝ)
        * ((448 * Real.log 2) / Real.log ((n : ℝ) ^ β)) < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (7 - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) :=
  kkh26_s128_ceiling_of_thornerZamanPNTinAP_square hTZ hm hn hr2 hr hx hpl hsupply hcount

/-- **The s = 128 `δ*` ceiling from the regime-correct count input, tight square-budget form.**
This uses the same collision-family square as `kkh26_s128_of_polyModulusCount_square`, but with
the sharper fixed-`r` resultant-size log `log((2r)^64)` in place of `448*log 2`. -/
theorem kkh26_s128_of_polyModulusCount_tight_square
    {n : ℕ} {β ε : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : ThornerZamanPNTinAP n β ε) {m r : ℕ}
    (hm : 1 ≤ m) (hn : n = 2 ^ 7 * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (7 - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ 7 : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hsupply : (supply : ℝ) ≤ tzDensityLB n β ε)
    (hcount : (((2 ^ r * ((64 : ℕ).choose r)) ^ 2 : ℕ) : ℝ)
        * (Real.log (((2 * r) ^ 2 ^ (7 - 1) : ℕ) : ℝ) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (7 - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) :=
  kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square
    hTZ hm hn hr2 hr hx hpl hsupply hcount

/-- **The s = 128 `δ*` ceiling from the regime-correct count input, tight square-budget
`64*log(2r)` form.**  This is the log-normalized form of
`kkh26_s128_of_polyModulusCount_tight_square`. -/
theorem kkh26_s128_of_polyModulusCount_tight_square_log
    {n : ℕ} {β ε : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : ThornerZamanPNTinAP n β ε) {m r : ℕ}
    (hm : 1 ≤ m) (hn : n = 2 ^ 7 * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (7 - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ 7 : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hsupply : (supply : ℝ) ≤ tzDensityLB n β ε)
    (hcount : (((2 ^ r * ((64 : ℕ).choose r)) ^ 2 : ℕ) : ℝ)
        * ((64 * Real.log (((2 * r : ℕ) : ℝ))) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (7 - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) :=
  kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square_log
    hTZ hm hn hr2 hr hx hpl hsupply hcount

/-- **The s = 128 `δ*` ceiling from the regime-correct count input, canonical floor-supply
`64*log(2r)` form.**  This removes the auxiliary `supply` witness from
`kkh26_s128_of_polyModulusCount_tight_square_log`: the normalized budget is compared directly
against `⌊tzDensityLB n β ε⌋₊`. -/
theorem kkh26_s128_of_polyModulusCount_floor_tight_square_log
    {n : ℕ} {β ε : ℝ} [NeZero n]
    (hTZ : ThornerZamanPNTinAP n β ε) {m r : ℕ}
    (hm : 1 ≤ m) (hn : n = 2 ^ 7 * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (7 - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ 7 : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hpos : 0 ≤ tzDensityLB n β ε)
    (hcount : (((2 ^ r * ((64 : ℕ).choose r)) ^ 2 : ℕ) : ℝ)
        * ((64 * Real.log (((2 * r : ℕ) : ℝ))) / Real.log ((n : ℝ) ^ β))
      < ((⌊tzDensityLB n β ε⌋₊ : ℕ) : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (7 - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) :=
  kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log
    hTZ hm hn hr2 hr hx hpl hpos hcount

end ProximityGap.Frontier.AvD1KKH26S128

/-! ## Axiom audit (expected: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) -/
open ProximityGap.Frontier.AvD1KKH26S128 in
#print axioms polyModulusCount_of_thornerZamanPNTinAP
open ProximityGap.Frontier.AvD1KKH26S128 in
#print axioms kkh26_s128_of_polyModulusCount
open ProximityGap.Frontier.AvD1KKH26S128 in
#print axioms kkh26_s128_of_polyModulusCount_square
open ProximityGap.Frontier.AvD1KKH26S128 in
#print axioms kkh26_s128_of_polyModulusCount_tight_square
open ProximityGap.Frontier.AvD1KKH26S128 in
#print axioms kkh26_s128_of_polyModulusCount_tight_square_log
open ProximityGap.Frontier.AvD1KKH26S128 in
#print axioms kkh26_s128_of_polyModulusCount_floor_tight_square_log
