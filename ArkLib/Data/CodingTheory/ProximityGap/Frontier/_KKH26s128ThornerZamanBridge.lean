/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26S128Ceiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._KKH26ThornerZamanTightBridge
import Mathlib.Data.Nat.Totient

/-!
# B3 — the s = 128 `δ*` ceiling as a named PNT-in-AP bridge (#334, E1)

This file packages the [KKH26] `s = 128` (`μ = 7`, `s = 2^7 = 128`) bad-line / field-size
ceiling as a **single axiom-clean BRIDGE** from the explicit, honestly-stated analytic
number theory input of **[Thorner–Zaman 2024]** to the coding-theory conclusion:

  `ThornerZamanPNTinAP <params>  →  kkh26_s128 δ* ceiling`.

The `s = 64` (`μ = 6`) rows are already unconditional in-tree via the A3 Parseval threshold;
`μ = 7` forces a genuinely-analytic prime supply, so the analytic input stays a named `Prop`
hypothesis — **never** an `axiom`, **never** a hidden `sorry`. The coding-theory consequence
is proven *from* it. This is the canonical "named-Prop BRIDGE" residual shape: honest scope is
"`s = 128` is discharged **conditional on** the named analytic-NT input; this file does **not**
prove the analytic input".

## The analytic input, stated precisely (correct quantifiers, polynomial range)

The honest open input is the **effective prime number theorem in arithmetic progressions** of
[TZ24], specialised to the progression `1 (mod n)` and the *polynomial* short range
`[n^β, 2·n^β]` (so the resulting prime `p = Θ(n^β)` is polynomial in the domain size
`n = 2^μ·m`, as [KKH26] Theorem 1 demands). Applied via partial summation to that interval it
gives the **effective density lower bound**

  `π(2·n^β; n, 1) − π(n^β; n, 1)
     ≥ (1 − ε) · n^β / (φ(n) · log(n^β))`,                         (TZ)

where `π(x; n, 1) = #{p ≤ x : p prime, p ≡ 1 (mod n)}` is the prime-counting function in the
progression and `ε = ε(n, β) = o(1)` is the explicit (effective) TZ error term. On paper this
holds unconditionally for every fixed `β > 12/5` (and for every `β > 1` under Montgomery's
conjecture); the deep proof (log-free zero-density / Linnik–Heath-Brown estimates for Dirichlet
`L`-functions) is far beyond present-day formalization and is **not** attempted here.

We name `(TZ)` as the `Prop`-valued hypothesis `ThornerZamanPNTinAP n β ε`. This is the
*right* sufficient input because:

* it is exactly the **PNT-in-AP density** [TZ24] proves (a counting-function lower bound in
  one residue class), not a bespoke window predicate — the `tzWindow` count is literally the
  short-interval difference `π(⌊2·n^β⌋; n, 1) − π((⌈n^β⌉−1); n, 1)` of the genuine
  `primeCountAPone`;
* its range `[n^β, 2·n^β]` is the *polynomial* window the `s = 128` ceiling consumes
  (`p = Θ(n^β)`), matching [KKH26] Thm 1; and
* the density expression `(1 − ε)·n^β/(φ(n)·log(n^β))` is precisely what the
  `s = 128` budget `|collisionPairs 7 r| · 448·log 2 / log(n^β)` must be
  compared against.  This comparison is the elementary side condition, the
  *only* non-analytic ingredient, and is discharged here.

## Main results

* `primeCountAPone n x = π(x; n, 1)` — the genuine prime-counting function in the progression.
* `tzWindow_card_eq_primeCountAPone_diff` — the window count is the short-interval difference
  of two values of `primeCountAPone`, so the named hypothesis really is the paper's `(TZ)`.
* `ThornerZamanPNTinAP n β ε` — **the named [TZ24] analytic input** `(TZ)`: a `Prop`, never an
  axiom, cited to [TZ24] Cor 3.1.
* `thornerZamanPNTinAP_iff_primeCountAPone` — confirms `ThornerZamanPNTinAP` is exactly the
  displayed counting-function bound `(TZ)`.
* `tzPrimeSupply_of_thornerZamanPNTinAP` — the PROVEN elementary reduction `(TZ) ⇒` the in-tree
  raw supply hypothesis `TZPrimeSupply` (real density bound ⇒ integer cardinality).
* `kkh26_s128_ceiling_of_thornerZamanPNTinAP` — **THE BRIDGE**: from the named analytic input
  `ThornerZamanPNTinAP n β ε`, the smooth-modulus decomposition `n = 2^7·m`, the degree budget
  `2 ≤ r ≤ 2^6`, the field-size lower bound `2^7 < n^β`, and the elementary side conditions
  (the supply count `supply` fits under the TZ density, and beats the `s = 128` bad-prime
  budget), there is a prime `p ≡ 1 (mod n)`, `p ∈ [n^β, 2·n^β]`, so
  `p = Θ(n^β)`, and a smooth evaluation domain `⟨g⟩ ⊆ F_p^×` of order `n`,
  with `mcaDeltaStar(C, ε*) ≤ 1 − r/128`.
* `kkh26_s128_ceiling_of_thornerZamanPNTinAP_square` — the same bridge with the paper-facing
  square budget `(2^r*C(64,r))^2 * 448*log 2 / log(n^β) < supply`.
* `kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square` — the fixed-`r` square-budget
  bridge with the sharper resultant log `log((2r)^64)`.
* `kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square_log` — the same fixed-`r` bridge
  with that logarithm normalized to `64 * log(2r)`.
* `kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log` — the canonical floor-supply
  form comparing the normalized budget directly against `⌊tzDensityLB n β ε⌋₊`.
* `kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log_auto_nonneg` — the same
  floor form with the density nonnegativity side condition derived from the budget comparison.

## Honesty

The ONLY unproven input is `ThornerZamanPNTinAP` (the [TZ24] effective PNT-in-AP density). It
is a named `Prop` hypothesis throughout — no `axiom`, no `sorry`, no `native_decide`. The
reduction, the budget comparison, and the wiring into `kkh26_mcaDeltaStar_le_s128` are all
unconditional and axiom-clean. Scope: this discharges `s = 128` **conditionally** on the named
analytic-NT input; it does **not** prove that input.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782 (Lemma 2, Theorem 1).
* [TZ24] J. Thorner, A. Zaman, *Refinements to the prime number theorem in arithmetic
  progressions*, Corollary 3.1 (the effective log-free density lower bound `(TZ)`).
-/

open Finset
open scoped NNReal ENNReal Nat

namespace ProximityGap.Frontier.KKH26s128ThornerZamanBridge

open ArkLib.ProximityGap.KKH26
  (tzWindow TZPrimeSupply collisionPairs evalCode
   kkh26_mcaDeltaStar_le_s128 kkh26_mcaDeltaStar_le_s128_tight_square_bound
   s128_resultantLog_eq s128_tightResultantLog_eq tightResultantLogRatio_nonneg)
open ProximityGap.Frontier.KKH26ThornerZamanTightBridge
  (real_nonneg_of_nonneg_lt_natFloor real_lt_natFloor_of_add_one_le)

/-! ### The prime-counting function in the arithmetic progression `1 (mod n)` -/

/-- The **prime-counting function in the progression `1 (mod n)`**:
`primeCountAPone n x = π(x; n, 1) = #{p ≤ x : p prime, p ≡ 1 (mod n)}`.  This is the object
[TZ24] bounds; the Thorner–Zaman window count `(tzWindow n β).card` is the short-interval
difference of two of its values (`tzWindow_card_eq_primeCountAPone_diff`). -/
noncomputable def primeCountAPone (n x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD n])).card

/-- **The short-interval identity.**  The Thorner–Zaman window count equals the difference of
two prime-counting-in-AP values, `π(⌊2·n^β⌋; n, 1) − π((⌈n^β⌉−1); n, 1)`.
This is exactly the short-interval quantity that partial summation over `[n^β, 2·n^β]`
produces in [TZ24] Cor 3.1.  Thus `tzWindow` is a difference of the genuine
counting function `primeCountAPone`, not a bespoke set. -/
theorem tzWindow_card_eq_primeCountAPone_diff (n : ℕ) (β : ℝ) :
    (tzWindow n β).card
      = primeCountAPone n ⌊2 * (n : ℝ) ^ β⌋₊
        - primeCountAPone n (⌈(n : ℝ) ^ β⌉₊ - 1) := by
  classical
  set lo : ℕ := ⌈(n : ℝ) ^ β⌉₊ with hlo
  set hi : ℕ := ⌊2 * (n : ℝ) ^ β⌋₊ with hhi
  set P : ℕ → Prop := fun p => p.Prime ∧ p ≡ 1 [MOD n] with hP
  -- The window is `Icc lo hi = Ico lo (hi+1)` filtered by `P`.
  have hIccIco : Finset.Icc lo hi = Finset.Ico lo (hi + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hwin : tzWindow n β = (Finset.Ico lo (hi + 1)).filter P := by
    rw [show tzWindow n β = (Finset.Icc lo hi).filter P from rfl, hIccIco]
  -- `primeCountAPone n x` counts `P` over `range (x+1) = Ico 0 (x+1)`.
  have hcountIco : ∀ x, primeCountAPone n x = ((Finset.Ico 0 (x + 1)).filter P).card := by
    intro x; rw [primeCountAPone, Finset.range_eq_Ico]
  rcases le_or_gt lo (hi + 1) with hle | hgt
  · -- the generic case `lo ≤ hi + 1`
    have hsplit : Finset.Ico 0 (hi + 1)
        = Finset.Ico 0 lo ∪ Finset.Ico lo (hi + 1) :=
      (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hle).symm
    have hdisj : Disjoint (Finset.Ico 0 lo) (Finset.Ico lo (hi + 1)) :=
      Finset.Ico_disjoint_Ico_consecutive 0 lo (hi + 1)
    have hcount :
        primeCountAPone n hi
          = ((Finset.Ico 0 lo).filter P).card + (tzWindow n β).card := by
      rw [hcountIco, hwin]
      conv_lhs => rw [hsplit]
      rw [Finset.filter_union, Finset.card_union_of_disjoint
        (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    have hlow : primeCountAPone n (lo - 1) = ((Finset.Ico 0 lo).filter P).card := by
      rw [hcountIco]
      rcases Nat.eq_zero_or_pos lo with h0 | hpos
      · rw [h0]
        have e1 : Finset.Ico 0 ((0 - 1) + 1) = {0} := by decide
        have e2 : Finset.Ico (0 : ℕ) 0 = ∅ := Finset.Ico_self 0
        rw [e1, e2, Finset.filter_singleton]
        simp only [P, Nat.not_prime_zero, false_and, if_false, Finset.card_empty,
          Finset.filter_empty]
      · rw [Nat.sub_add_cancel hpos]
    omega
  · -- degenerate empty window `lo > hi + 1`
    have hempty : tzWindow n β = ∅ := by
      rw [hwin, Finset.filter_eq_empty_iff]
      intro x hx
      simp only [Finset.mem_Ico] at hx
      omega
    have hle' : primeCountAPone n hi ≤ primeCountAPone n (lo - 1) := by
      rw [hcountIco, hcountIco]
      apply Finset.card_le_card
      apply Finset.filter_subset_filter
      apply Finset.Ico_subset_Ico le_rfl
      omega
    rw [hempty, Finset.card_empty]
    omega

/-! ### The named [TZ24] analytic input (the density form, with `φ(n)`) -/

/-- The **[TZ24] density expression** `(1 − ε) · n^β / (φ(n) · log(n^β))` — the explicit,
effective lower bound that Thorner–Zaman's refined PNT in arithmetic progressions gives for the
count of primes `p ≡ 1 (mod n)` in the polynomial short interval `[n^β, 2·n^β]` (Cor 3.1, via
partial summation).  `ε = ε(n, β) = o(1)` is the explicit TZ error term.  Named once so both the
statement and the reduction speak of the same quantity. -/
noncomputable def tzDensityLB (n : ℕ) (β ε : ℝ) : ℝ :=
  (1 - ε) * (n : ℝ) ^ β / ((Nat.totient n : ℝ) * Real.log ((n : ℝ) ^ β))

/-- **The named [TZ24] effective PNT-in-AP input** `(TZ)` (the `Hab25Johnson` /
`TZPrimeSupply` named-hypothesis pattern; **never an axiom, never a `sorry`**).
`ThornerZamanPNTinAP n β ε` asserts the *effective density lower bound* of Thorner–Zaman's
refined prime number theorem in arithmetic progressions (Cor 3.1 of [TZ24], applied via
partial summation to the polynomial short interval `[n^β, 2·n^β]`): the window of primes
`p ≡ 1 (mod n)` has cardinality at least the density expression
`tzDensityLB n β ε = (1 − ε) · n^β / (φ(n) · log(n^β))`.

On paper this holds unconditionally for every fixed `β > 12/5` with an explicit effective error
`ε = o(1)` (and for every `β > 1` under Montgomery's conjecture).  The deep analytic proof
(log-free zero-density / Linnik–Heath-Brown estimates for Dirichlet `L`-functions) is far beyond
present-day formalization; following the project convention it lives as this `Prop`, consumed
downstream by an explicit hypothesis.  It is **not** an `axiom` and is **not** proven here. -/
def ThornerZamanPNTinAP (n : ℕ) (β ε : ℝ) : Prop :=
  tzDensityLB n β ε ≤ ((tzWindow n β).card : ℝ)

/-- **`ThornerZamanPNTinAP` is exactly the paper's `π(x; n, 1)` statement `(TZ)`.**
Unfolding the window cardinality via the short-interval identity,
`ThornerZamanPNTinAP n β ε` says precisely that the prime-counting difference
`π(⌊2·n^β⌋; n, 1) − π((⌈n^β⌉−1); n, 1)` is at least the [TZ24] density expression.
So the named hypothesis is the literature statement in terms of the genuine counting function
`primeCountAPone`, not a bespoke window predicate. -/
theorem thornerZamanPNTinAP_iff_primeCountAPone (n : ℕ) (β ε : ℝ) :
    ThornerZamanPNTinAP n β ε ↔
      tzDensityLB n β ε
        ≤ ((primeCountAPone n ⌊2 * (n : ℝ) ^ β⌋₊
            - primeCountAPone n (⌈(n : ℝ) ^ β⌉₊ - 1) : ℕ) : ℝ) := by
  rw [ThornerZamanPNTinAP, tzWindow_card_eq_primeCountAPone_diff]

/-! ### The elementary reduction `(TZ) ⇒ TZPrimeSupply` (PROVEN, axiom-clean) -/

/-- **The PROVEN reduction** `[TZ24] density bound ⇒ in-tree supply hypothesis`.  Given the
named literature bound `ThornerZamanPNTinAP n β ε` (the deep analytic input) and the elementary
arithmetic fact that the requested `supply` does not exceed the [TZ24] density expression
`tzDensityLB n β ε`, the in-tree named hypothesis `TZPrimeSupply n β supply` consumed by the
`s = 128` ceiling holds.  Chain `supply ≤ tzDensityLB ≤ #window` over `ℝ`, then descend
to `ℕ`; the deep analytic content stays packaged in `hTZ`. -/
theorem tzPrimeSupply_of_thornerZamanPNTinAP {n : ℕ} {β ε : ℝ} {supply : ℕ}
    (hTZ : ThornerZamanPNTinAP n β ε) (hsupply : (supply : ℝ) ≤ tzDensityLB n β ε) :
    TZPrimeSupply n β supply := by
  refine ⟨?_⟩
  have hreal : (supply : ℝ) ≤ ((tzWindow n β).card : ℝ) := hsupply.trans hTZ
  exact_mod_cast hreal

/-! ### THE BRIDGE: named PNT-in-AP input ⇒ `s = 128` `δ*` ceiling -/

/-- **THE s = 128 BRIDGE** (#334, B3 / E1):
`ThornerZamanPNTinAP ⇒ kkh26 s = 128 δ* ceiling`.

Given the named [TZ24] effective PNT-in-AP density input `ThornerZamanPNTinAP n β ε`, the
smooth-modulus decomposition `n = 2^7·m` (`s = 2^7 = 128`), the degree budget `2 ≤ r ≤ 2^6`,
the field-size lower bound `2^7 < n^β`, and the two **elementary** side conditions

* `hsupply : supply ≤ tzDensityLB n β ε`  — the integer supply count fits under the TZ density
  (the reduction to the raw `TZPrimeSupply`), and
* `hcount`  — that supply count strictly beats the `s = 128` bad-prime budget
  `|collisionPairs 7 r| · log(s^{s/2}) / log(n^β)`  (with `s^{s/2} = (2^7)^{2^6} = 2^448`),

there is a prime `p ≡ 1 (mod n)`, `p ∈ [n^β, 2·n^β]`, so `p = Θ(n^β)`
and is **polynomial** in the domain size `n`; and a smooth evaluation domain
`⟨g⟩ ⊆ F_p^×` of order `n`, such that for every
target error `ε* < 2^r·C(2^6, r)/p` the formal MCA threshold of the explicit evaluation code
satisfies

  `mcaDeltaStar(C, ε*) ≤ 1 − r/128`,

strictly below the code's capacity.  The ONLY unproven input is `ThornerZamanPNTinAP`; the
reduction, budget comparison, and wiring are all unconditional and axiom-clean. -/
theorem kkh26_s128_ceiling_of_thornerZamanPNTinAP {n : ℕ} {β ε : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : ThornerZamanPNTinAP n β ε) {m r : ℕ}
    (hm : 1 ≤ m) (hn : n = 2 ^ 7 * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (7 - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ 7 : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hsupply : (supply : ℝ) ≤ tzDensityLB n β ε)
    (hcount : ((collisionPairs 7 r).card : ℝ)
        * (Real.log ((((((2 : ℕ) ^ 7) ^ 2 ^ (7 - 1) : ℕ)) : ℝ)) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (7 - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) := by
  -- (1) the only analytic step: discharge the raw supply hypothesis from the named density input
  have hSupply : TZPrimeSupply n β supply :=
    tzPrimeSupply_of_thornerZamanPNTinAP hTZ hsupply
  -- (2) feed it (it is definitionally `EffectivePNTinAP`) into the proven s = 128 headline
  exact kkh26_mcaDeltaStar_le_s128 (n := n) (β := β) (supply := supply)
    (hTZ := hSupply) hm hn hr2 hr hx hpl hcount

/-- **The bridge in the convenient `448·log 2` budget form.**  Identical to
`kkh26_s128_ceiling_of_thornerZamanPNTinAP` but with the `s = 128` resultant-size log already
reduced via `s128_resultantLog_eq` (`log(s^{s/2}) = 448·log 2`), so the budget side condition
reads directly as the paper's `|collisionPairs 7 r| · 448·log 2 / log(n^β) < supply`. -/
theorem kkh26_s128_ceiling_of_thornerZamanPNTinAP' {n : ℕ} {β ε : ℝ} {supply : ℕ} [NeZero n]
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
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) := by
  refine kkh26_s128_ceiling_of_thornerZamanPNTinAP hTZ hm hn hr2 hr hx hpl hsupply ?_
  rw [s128_resultantLog_eq]
  exact hcount

/-- **The bridge in the paper-facing square-budget form.**  This variant consumes the common
analytic side condition
`(2^r*C(64,r))^2 * 448*log 2 / log(n^β) < supply`; the exact collision-pair budget is
smaller, so the proven s = 128 ceiling applies. -/
theorem kkh26_s128_ceiling_of_thornerZamanPNTinAP_square
    {n : ℕ} {β ε : ℝ} {supply : ℕ} [NeZero n]
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
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) := by
  have hSupply : TZPrimeSupply n β supply :=
    tzPrimeSupply_of_thornerZamanPNTinAP hTZ hsupply
  exact ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_s128_of_square_bound
    (n := n) (β := β) (supply := supply) (m := m) (r := r)
    hSupply hm hn hr2 hr hx hpl hcount

/-- **The bridge in the sharp fixed-`r` square-budget form.**  This consumes the common
collision-family square `(2^r*C(64,r))^2`, but with the already-proven sharper fixed-`r`
resultant-size log `log((2r)^64)` instead of the coarse `448*log 2`. -/
theorem kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square
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
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) := by
  have hSupply : TZPrimeSupply n β supply :=
    tzPrimeSupply_of_thornerZamanPNTinAP hTZ hsupply
  exact kkh26_mcaDeltaStar_le_s128_tight_square_bound
    (n := n) (β := β) (supply := supply) (m := m) (r := r)
    hSupply hm hn hr2 hr hx hpl hcount

/-- **The sharp fixed-`r` bridge in `64*log(2r)` form.**  This is the same bridge as
`kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square`, with
`log((2r)^64)` rewritten by `s128_tightResultantLog_eq`. -/
theorem kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square_log
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
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) := by
  have hSupply : TZPrimeSupply n β supply :=
    tzPrimeSupply_of_thornerZamanPNTinAP hTZ hsupply
  exact ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_s128_tight_square_bound_log
    (n := n) (β := β) (supply := supply) (m := m) (r := r)
    hSupply hm hn hr2 hr hx hpl hcount

/-- **The sharp fixed-`r` s = 128 bridge in canonical floor-supply form.**  This removes the
auxiliary `supply` witness from `kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square_log`:
the normalized bad-prime budget is compared directly against `⌊tzDensityLB n β ε⌋₊`. -/
theorem kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log
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
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) := by
  refine kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square_log
    (supply := ⌊tzDensityLB n β ε⌋₊) hTZ hm hn hr2 hr hx hpl ?_ hcount
  exact Nat.floor_le hpos

/-- **The sharp fixed-`r` s = 128 bridge in floor-supply form, with automatic density
nonnegativity.**  Since the normalized `64*log(2r)` budget is nonnegative under `r ≥ 2` and
`n^β ≥ 2`, the comparison against `⌊tzDensityLB n β ε⌋₊` already proves
`0 ≤ tzDensityLB n β ε`. -/
theorem kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log_auto_nonneg
    {n : ℕ} {β ε : ℝ} [NeZero n]
    (hTZ : ThornerZamanPNTinAP n β ε) {m r : ℕ}
    (hm : 1 ≤ m) (hn : n = 2 ^ 7 * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (7 - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ 7 : ℕ) : ℝ) < (n : ℝ) ^ β)
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
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) := by
  have hratio_nonneg :
      0 ≤ ((64 * Real.log (((2 * r : ℕ) : ℝ))) / Real.log ((n : ℝ) ^ β)) := by
    simpa [s128_tightResultantLog_eq] using
      (tightResultantLogRatio_nonneg (n := n) (β := β) 7 r (by omega) hx)
  have hbudget_nonneg :
      0 ≤ (((2 ^ r * ((64 : ℕ).choose r)) ^ 2 : ℕ) : ℝ)
        * ((64 * Real.log (((2 * r : ℕ) : ℝ))) / Real.log ((n : ℝ) ^ β)) := by
    exact mul_nonneg (by positivity) hratio_nonneg
  have hpos : 0 ≤ tzDensityLB n β ε :=
    real_nonneg_of_nonneg_lt_natFloor hbudget_nonneg hcount
  exact kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log
    hTZ hm hn hr2 hr hx hpl hpos hcount

/-- **The sharp fixed-`r` s = 128 bridge from a real density margin.**

This is the paper-facing sufficient condition for the canonical floor-supply theorem: the
normalized `64*log(2r)` bad-prime budget plus one is at most the TZ density lower bound. -/
theorem kkh26_s128_ceiling_of_thornerZamanPNTinAP_density_margin_tight_square_log
    {n : ℕ} {β ε : ℝ} [NeZero n]
    (hTZ : ThornerZamanPNTinAP n β ε) {m r : ℕ}
    (hm : 1 ≤ m) (hn : n = 2 ^ 7 * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (7 - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ 7 : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hmargin : (((2 ^ r * ((64 : ℕ).choose r)) ^ 2 : ℕ) : ℝ)
        * ((64 * Real.log (((2 * r : ℕ) : ℝ))) / Real.log ((n : ℝ) ^ β)) + 1
      ≤ tzDensityLB n β ε) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (7 - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) := by
  have hcount : (((2 ^ r * ((64 : ℕ).choose r)) ^ 2 : ℕ) : ℝ)
        * ((64 * Real.log (((2 * r : ℕ) : ℝ))) / Real.log ((n : ℝ) ^ β))
      < ((⌊tzDensityLB n β ε⌋₊ : ℕ) : ℝ) :=
    real_lt_natFloor_of_add_one_le hmargin
  exact kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log_auto_nonneg
    hTZ hm hn hr2 hr hx hpl hcount

end ProximityGap.Frontier.KKH26s128ThornerZamanBridge

/-! ## Axiom audit (expected: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) -/
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms tzWindow_card_eq_primeCountAPone_diff
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms thornerZamanPNTinAP_iff_primeCountAPone
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms tzPrimeSupply_of_thornerZamanPNTinAP
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms kkh26_s128_ceiling_of_thornerZamanPNTinAP
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms kkh26_s128_ceiling_of_thornerZamanPNTinAP'
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms kkh26_s128_ceiling_of_thornerZamanPNTinAP_square
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square_log
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log_auto_nonneg
open ProximityGap.Frontier.KKH26s128ThornerZamanBridge in
#print axioms kkh26_s128_ceiling_of_thornerZamanPNTinAP_density_margin_tight_square_log
