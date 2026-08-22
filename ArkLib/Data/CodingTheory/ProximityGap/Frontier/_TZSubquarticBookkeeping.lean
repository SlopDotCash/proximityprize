/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.Prime

/-!
# [TZ24] Thm 1.1 sub-quartic bookkeeping for dyadic moduli (#466, lane W2)

## What the in-tree Prop asserts vs what the paper delivers (the discharge map)

The in-tree analytic input of the B3 ceiling is `TZPrimeSupply n β supply`
(`KKH26ThornerZaman.lean`): the window `[n^β, 2·n^β]` contains at least `supply` primes
`p ≡ 1 (mod n)` — a **raw window cardinality**.  It is consumed by
`kkh26_mcaDeltaStar_le_of_TZ` (the polynomial-field δ* ceiling) and by the off-BGK floor
arrow (`tzSupplyOne_gives_prime_below_prize`).  `_ThornerZamanPNTStatement.lean` already
grounds it per-instance: `ThornerZamanPNT n β ε` (the density form
`(1−ε)·n^β/(φ(n)·log n^β) ≤ #window`) **provably implies** `TZPrimeSupply n β supply`
for any `supply` below the density.

What Thorner–Zaman (arXiv:2108.10878, *Refinements to the prime number theorem for
arithmetic progressions*) actually proves — confirmed verbatim in
`docs/kb/deltastar-464-thorner-zaman-subquartic-CONFIRMED-2026-06-27.md` — is **Theorem 1.1**:
the PNT-in-AP asymptotic for the short interval `(x−h, x]` holds once (eq. 1.8)
`h ≥ x^{1−δ₁}`, `q ≤ x^{δ₂}`, `δ₁ + (3/2)·δ₂ ≤ 1 − θ − ε`, with `θ = 7/12` **when no Siegel
zero exists** and the coefficient `3/2` replaced by `1` in that case.  For the **dyadic
family `q = 2^a`** the squarefree part is the fixed `d = 2`, so (§3.1, Iwaniec) the Siegel
zero is eliminated for all `a` beyond an absolute `a₀`; then `δ₂ ≤ 5/12`, i.e. the count
holds for all `x ≥ q^{12/5+ε}` — the **sub-quartic exponent `12/5 = 2.4 < 4`**.

**Verdict on the remaining gap.**  It splits cleanly:

1. **NOT formalizable today (stays a named Prop + citation):** Theorem 1.1 itself — log-free
   zero-density estimates for Dirichlet `L`-functions.  Mathlib has Dirichlet's theorem
   (`Nat.forall_exists_prime_gt_and_modEq`, used by `_TZDirichletUnconditional.lean` for the
   size-unbounded existence) but **no effective PNT-in-AP of any strength**.  The honest
   in-tree form of the analytic content is therefore the named hypothesis below.
2. **DERIVABLE (this file, proven, axiom-clean):** the entire *bookkeeping* from a faithful
   quantified form of Theorem 1.1 down to the shapes the tree consumes — the
   "coefficient `3/2 → 1`, `x ≥ q^{12/5}`" arithmetic:
   the window specialization (`x = 2n^β`, `h = x/2 = n^β`), the `TZPrimeSupply` instances
   for dyadic moduli at every `β ≥ β₀` (in particular **β = 3 and β = 4**), and the
   **least-prime bound `p ≤ (2^a)^{β₀+ε}`** (so `(2^a)^{12/5+ε}` at the paper's exponent),
   including its below-prize-scale form `p ≤ (2^a)^4`.

## The named hypothesis (never an axiom)

* `TZDyadicShortIntervalLB c a₀ β₀` — for every `a ≥ a₀` and every real `x ≥ (2^a)^{β₀}` and
  `h ∈ [x/2, x]`, the interval `(x−h, x]` contains at least `c·h/(φ(2^a)·log x)` primes
  `≡ 1 (mod 2^a)`.  [TZ24] Thm 1.1 + §3.1 instantiates this for **every fixed `β₀ > 12/5`**
  with some `c = c(β₀) > 0` and `a₀ = a₀(β₀)` (absolute, since the dyadic squarefree part is
  the fixed `d = 2`).  Our form is *weaker* than the paper's (it restricts `h` to `[x/2, x]`
  instead of `h ≥ x^{1−δ₁}`, keeps only the lower half of the asymptotic, and absorbs the
  `(1+o(1))` into `c`), so instantiating it from [TZ24] is sound.  Note the hypothesis is
  never vacuously exploited: every consumer below carries an explicit arithmetic side
  condition (`hsupply`/`hone`) that is false unless `c` genuinely delivers the density.

## The proven conditional chain (all axiom-clean)

* `apPrimesIoc` / `mem_apPrimesIoc` — the AP prime count over a real interval `(y, x]`.
* `apPrimesIoc_subset_tzWindow` — the window specialization `(n^β, 2n^β] ⊆ tzWindow n β`.
* `tzPrimeSupply_dyadic_of_shortIntervalLB` (+ `_natFloor`) — the headline reduction:
  the named [TZ24] hypothesis yields `TZPrimeSupply (2^a) β supply` for every `β ≥ β₀` and
  every `supply` below the density `c·(2^a)^β / (φ(2^a)·log(2·(2^a)^β))`.
* `tzPrimeSupply_dyadic_beta3/beta4_of_shortIntervalLB` — the β ∈ {3, 4} instances.
* `exists_dyadic_prime_le_two_mul_rpow` → `exists_dyadic_prime_le_rpow_exponent` — the
  least-prime chain: a prime `p ≡ 1 (mod 2^a)` with `p ≤ 2·(2^a)^{β₀} = (2^a)^{β₀+1/a}
  ≤ (2^a)^{β₀+ε}` for any `ε ≥ 1/a` — the paper's `≪ q^{12/5+ε}` least-prime bound.
* `exists_dyadic_prime_below_prize` — with `β₀ ≤ 3`: the prime is `≤ (2^a)^4`, the exact
  premise shape of the off-BGK floor arrow (`_FloorLinnikThornerZamanArrow.lean`).

## Concrete ladder extension (unconditional, `decide`/`norm_num`)

The rungs `n ≤ 256` missing from `ThornerZamanInstance.lean` at the sub-quartic-relevant
exponents: `tzPrimeSupply_128_three`, `tzPrimeSupply_256_three`, `tzPrimeSupply_128_four`,
`tzPrimeSupply_256_four` (witness data generated by
`scripts/probes/probe_466_tz_ladder_rungs.py`).

## Honesty

Nothing here proves `TZDyadicShortIntervalLB` — it is the [TZ24] literature statement,
carried as a named `Prop` (the `Hab25Johnson` pattern), mathematically CONFIRMED from the
paper but beyond present-day Lean analytic NT.  Everything else in this file is proven,
`[propext, Classical.choice, Quot.sound]` only.  This does not touch the BGK/Paley wall;
the prize core stays OPEN.

## References

* [TZ24] J. Thorner, A. Zaman, arXiv:2108.10878, Thm 1.1, eq. (1.8), §3.1, Cor 3.1.
* [KKH26] ePrint 2026/782, Lemma 2 (the consumer).  Issues #334/#466.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping

open ArkLib.ProximityGap.KKH26 (tzWindow mem_tzWindow TZPrimeSupply)

/-! ### The AP prime count over a real interval -/

/-- The primes `p ≡ 1 (mod q)` in the real interval `(y, x]` (as a `Finset` of naturals;
the real-boundary conditions are encoded by `⌊y⌋₊ < p ≤ ⌊x⌋₊`, see `mem_apPrimesIoc`).
This is the `(x−h, x]` object of [TZ24] Theorem 1.1. -/
noncomputable def apPrimesIoc (q : ℕ) (y x : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]

/-- Membership in `apPrimesIoc`, in real-interval form (for nonnegative endpoints). -/
lemma mem_apPrimesIoc {q : ℕ} {y x : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x) {p : ℕ} :
    p ∈ apPrimesIoc q y x ↔ p.Prime ∧ p ≡ 1 [MOD q] ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  simp only [apPrimesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.floor_lt hy,
    Nat.le_floor_iff hx]
  tauto

/-- **The window specialization.**  Taking `x = 2·n^β` and `h = x/2 = n^β` in the [TZ24]
short interval, the primes counted land inside the in-tree Thorner–Zaman window
`tzWindow n β = [n^β, 2·n^β]`. -/
lemma apPrimesIoc_subset_tzWindow {n : ℕ} {β : ℝ} :
    apPrimesIoc n ((n : ℝ) ^ β) (2 * (n : ℝ) ^ β) ⊆ tzWindow n β := by
  intro p hp
  have h0 : (0 : ℝ) ≤ (n : ℝ) ^ β := Real.rpow_nonneg (Nat.cast_nonneg n) β
  have h2 : (0 : ℝ) ≤ 2 * (n : ℝ) ^ β := by linarith
  rw [mem_apPrimesIoc h0 h2] at hp
  rw [mem_tzWindow]
  exact ⟨hp.1, hp.2.1, le_of_lt hp.2.2.1, hp.2.2.2⟩

/-! ### The named [TZ24] Theorem 1.1 hypothesis (dyadic, Siegel-zero-free regime) -/

/-- **The named [TZ24] Theorem 1.1 hypothesis for the dyadic family** (`Hab25Johnson`
pattern; **never an axiom**).  `TZDyadicShortIntervalLB c a₀ β₀` asserts: for every `a ≥ a₀`
and all reals `x ≥ (2^a)^{β₀}`, `x/2 ≤ h ≤ x`, the interval `(x−h, x]` contains at least
`c·h / (φ(2^a)·log x)` primes `p ≡ 1 (mod 2^a)`.

On paper ([TZ24] Thm 1.1 + §3.1; confirmed verbatim in
`docs/kb/deltastar-464-thorner-zaman-subquartic-CONFIRMED-2026-06-27.md`): the dyadic modulus
`q = 2^a` has fixed squarefree part `d = 2`, so the exceptional (Siegel) zero is eliminated
for all `a` beyond an absolute threshold; then `θ = 7/12`, the eq.-(1.8) coefficient `3/2`
becomes `1`, and the asymptotic holds whenever `q ≤ x^{δ₂}` with `δ₂ < 5/12` — i.e. for
every fixed `β₀ > 12/5` there are `c = c(β₀) > 0` and `a₀ = a₀(β₀)` making this `Prop` true.
This form is *weaker* than the paper's (only `h ∈ [x/2, x]`, lower half of the asymptotic,
`(1+o(1))` absorbed into `c`), so the instantiation is sound.  The deep analytic proof
(log-free zero-density estimates) is beyond present-day formalization; per project
convention it lives as this named `Prop`, consumed by explicit hypothesis. -/
def TZDyadicShortIntervalLB (c : ℝ) (a₀ : ℕ) (β₀ : ℝ) : Prop :=
  ∀ a : ℕ, a₀ ≤ a →
    ∀ x h : ℝ, ((2 ^ a : ℕ) : ℝ) ^ β₀ ≤ x → x / 2 ≤ h → h ≤ x →
      c * h / ((Nat.totient (2 ^ a) : ℝ) * Real.log x)
        ≤ ((apPrimesIoc (2 ^ a) (x - h) x).card : ℝ)

/-! ### The proven bookkeeping chain -/

/-- **The headline reduction ([TZ24] Thm 1.1 ⇒ in-tree supply), dyadic.**  Given the named
short-interval bound at threshold exponent `β₀` and any `β ≥ β₀`, every `supply` below the
window density `c·(2^a)^β / (φ(2^a)·log(2·(2^a)^β))` discharges the in-tree hypothesis
`TZPrimeSupply (2^a) β supply` consumed by `kkh26_mcaDeltaStar_le_of_TZ`.  The proof is the
pure bookkeeping: specialize to `x = 2·(2^a)^β`, `h = x/2` (allowed since
`x ≥ (2^a)^β ≥ (2^a)^{β₀}`), and push the interval count into the window. -/
theorem tzPrimeSupply_dyadic_of_shortIntervalLB {c : ℝ} {a₀ : ℕ} {β₀ : ℝ}
    (hTZ : TZDyadicShortIntervalLB c a₀ β₀) {a : ℕ} (ha : a₀ ≤ a)
    {β : ℝ} (hβ : β₀ ≤ β) {supply : ℕ}
    (hsupply : (supply : ℝ) ≤
      c * ((2 ^ a : ℕ) : ℝ) ^ β /
        ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ β))) :
    TZPrimeSupply (2 ^ a) β supply := by
  have hn1 : (1 : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have ht0 : (0 : ℝ) < ((2 ^ a : ℕ) : ℝ) ^ β := Real.rpow_pos_of_pos (by linarith) β
  -- the threshold: x = 2·(2^a)^β ≥ (2^a)^{β₀}
  have hthr : ((2 ^ a : ℕ) : ℝ) ^ β₀ ≤ 2 * ((2 ^ a : ℕ) : ℝ) ^ β := by
    have h1 : ((2 ^ a : ℕ) : ℝ) ^ β₀ ≤ ((2 ^ a : ℕ) : ℝ) ^ β :=
      Real.rpow_le_rpow_of_exponent_le hn1 hβ
    linarith
  -- apply the named hypothesis at x = 2·(2^a)^β, h = (2^a)^β
  have hcard := hTZ a ha (2 * ((2 ^ a : ℕ) : ℝ) ^ β) (((2 ^ a : ℕ) : ℝ) ^ β)
    hthr (le_of_eq (by ring)) (by linarith)
  rw [show 2 * ((2 ^ a : ℕ) : ℝ) ^ β - ((2 ^ a : ℕ) : ℝ) ^ β = ((2 ^ a : ℕ) : ℝ) ^ β
    from by ring] at hcard
  -- the counted primes sit inside the in-tree window
  have hsub :
      apPrimesIoc (2 ^ a) (((2 ^ a : ℕ) : ℝ) ^ β) (2 * ((2 ^ a : ℕ) : ℝ) ^ β)
        ⊆ tzWindow (2 ^ a) β := apPrimesIoc_subset_tzWindow
  refine ⟨?_⟩
  have hfin : (supply : ℝ) ≤ ((tzWindow (2 ^ a) β).card : ℝ) := by
    calc (supply : ℝ)
        ≤ c * ((2 ^ a : ℕ) : ℝ) ^ β /
            ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ β)) := hsupply
      _ ≤ ((apPrimesIoc (2 ^ a) (((2 ^ a : ℕ) : ℝ) ^ β)
              (2 * ((2 ^ a : ℕ) : ℝ) ^ β)).card : ℝ) := hcard
      _ ≤ ((tzWindow (2 ^ a) β).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
  exact_mod_cast hfin

/-- The headline reduction with the side condition in clean natural-number floor form
(mirrors `tzPrimeSupply_of_thornerZamanPNT_natFloor`). -/
theorem tzPrimeSupply_dyadic_of_shortIntervalLB_natFloor {c : ℝ} {a₀ : ℕ} {β₀ : ℝ}
    (hTZ : TZDyadicShortIntervalLB c a₀ β₀) {a : ℕ} (ha : a₀ ≤ a)
    {β : ℝ} (hβ : β₀ ≤ β) {supply : ℕ}
    (hpos : 0 ≤ c * ((2 ^ a : ℕ) : ℝ) ^ β /
        ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ β)))
    (hsupply : supply ≤ ⌊c * ((2 ^ a : ℕ) : ℝ) ^ β /
        ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ β))⌋₊) :
    TZPrimeSupply (2 ^ a) β supply := by
  refine tzPrimeSupply_dyadic_of_shortIntervalLB hTZ ha hβ ?_
  calc (supply : ℝ)
      ≤ (⌊c * ((2 ^ a : ℕ) : ℝ) ^ β /
          ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ β))⌋₊ : ℝ) := by
        exact_mod_cast hsupply
    _ ≤ _ := Nat.floor_le hpos

/-- **The β = 3 instance** (the exponent of the off-BGK floor arrow; `3 ≥ β₀` holds for the
canonical [TZ24] instantiation `β₀ ∈ (12/5, 3]`). -/
theorem tzPrimeSupply_dyadic_beta3_of_shortIntervalLB {c : ℝ} {a₀ : ℕ} {β₀ : ℝ}
    (hTZ : TZDyadicShortIntervalLB c a₀ β₀) {a : ℕ} (ha : a₀ ≤ a) (hβ₀ : β₀ ≤ 3)
    {supply : ℕ}
    (hsupply : (supply : ℝ) ≤
      c * ((2 ^ a : ℕ) : ℝ) ^ (3 : ℝ) /
        ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ (3 : ℝ)))) :
    TZPrimeSupply (2 ^ a) (3 : ℝ) supply :=
  tzPrimeSupply_dyadic_of_shortIntervalLB hTZ ha hβ₀ hsupply

/-- **The β = 4 instance** (the prize-scale exponent). -/
theorem tzPrimeSupply_dyadic_beta4_of_shortIntervalLB {c : ℝ} {a₀ : ℕ} {β₀ : ℝ}
    (hTZ : TZDyadicShortIntervalLB c a₀ β₀) {a : ℕ} (ha : a₀ ≤ a) (hβ₀ : β₀ ≤ 4)
    {supply : ℕ}
    (hsupply : (supply : ℝ) ≤
      c * ((2 ^ a : ℕ) : ℝ) ^ (4 : ℝ) /
        ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ (4 : ℝ)))) :
    TZPrimeSupply (2 ^ a) (4 : ℝ) supply :=
  tzPrimeSupply_dyadic_of_shortIntervalLB hTZ ha hβ₀ hsupply

/-! ### The least-prime chain: `p ≤ 2·(2^a)^{β₀} = (2^a)^{β₀+1/a} ≤ (2^a)^{β₀+ε}` -/

/-- **Least prime, raw form.**  If the density at the threshold exponent `β₀` itself reaches
`1` (an arithmetic side condition on `c` and `a`, true for all large `a` on the [TZ24]
instantiation since the density grows like `(2^a)^{β₀−1}`), the named hypothesis produces a
prime `p ≡ 1 (mod 2^a)` with `p ≤ 2·(2^a)^{β₀}`. -/
theorem exists_dyadic_prime_le_two_mul_rpow {c : ℝ} {a₀ : ℕ} {β₀ : ℝ}
    (hTZ : TZDyadicShortIntervalLB c a₀ β₀) {a : ℕ} (ha : a₀ ≤ a)
    (hone : (1 : ℝ) ≤ c * ((2 ^ a : ℕ) : ℝ) ^ β₀ /
        ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ β₀))) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 2 ^ a] ∧ (p : ℝ) ≤ 2 * ((2 ^ a : ℕ) : ℝ) ^ β₀ := by
  have hsupply : TZPrimeSupply (2 ^ a) β₀ 1 :=
    tzPrimeSupply_dyadic_of_shortIntervalLB hTZ ha le_rfl (by exact_mod_cast hone)
  have hne : (tzWindow (2 ^ a) β₀).Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.lt_of_lt_of_le Nat.one_pos hsupply.le_card
  obtain ⟨p, hp⟩ := hne
  rw [mem_tzWindow] at hp
  exact ⟨p, hp.1, hp.2.1, hp.2.2.2⟩

/-- The clean exponent identity `2·(2^a)^β = (2^a)^{β+1/a}` (the factor `2` is exactly one
more dyadic digit: `2 = (2^a)^{1/a}`). -/
lemma two_mul_two_pow_rpow {a : ℕ} (ha : 1 ≤ a) (β : ℝ) :
    2 * ((2 ^ a : ℕ) : ℝ) ^ β = ((2 ^ a : ℕ) : ℝ) ^ (β + 1 / (a : ℝ)) := by
  have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hb0 : (0 : ℝ) < ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast Nat.two_pow_pos a
  have hroot : ((2 ^ a : ℕ) : ℝ) ^ ((1 : ℝ) / (a : ℝ)) = 2 := by
    have hcast : ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ (a : ℕ) := by push_cast; ring
    rw [hcast, ← Real.rpow_natCast (2 : ℝ) a,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_one_div, div_self ha0,
      Real.rpow_one]
  rw [Real.rpow_add hb0, hroot]
  ring

/-- **The [TZ24] least-prime bound in exponent form: `p ≤ (2^a)^{β₀+ε}`.**  For any
`ε ≥ 1/a`, the named hypothesis (plus the density-≥-1 side condition) produces a prime
`p ≡ 1 (mod 2^a)` below `(2^a)^{β₀+ε}`.  With the canonical [TZ24] instantiation
`β₀ = 12/5 + ε/2` (any `ε > 0`) this is exactly the paper's *least prime `≡ 1 (mod 2^a)`
is `≪_ε (2^a)^{12/5+ε}`* — the sub-quartic Linnik-type exponent for the prize's dyadic
family. -/
theorem exists_dyadic_prime_le_rpow_exponent {c : ℝ} {a₀ : ℕ} {β₀ : ℝ}
    (hTZ : TZDyadicShortIntervalLB c a₀ β₀) {a : ℕ} (ha : a₀ ≤ a) (ha1 : 1 ≤ a)
    (hone : (1 : ℝ) ≤ c * ((2 ^ a : ℕ) : ℝ) ^ β₀ /
        ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ β₀)))
    {ε : ℝ} (hε : 1 / (a : ℝ) ≤ ε) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 2 ^ a] ∧ (p : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) ^ (β₀ + ε) := by
  obtain ⟨p, hp, hmod, hle⟩ := exists_dyadic_prime_le_two_mul_rpow hTZ ha hone
  have hn1 : (1 : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  refine ⟨p, hp, hmod, ?_⟩
  calc (p : ℝ) ≤ 2 * ((2 ^ a : ℕ) : ℝ) ^ β₀ := hle
    _ = ((2 ^ a : ℕ) : ℝ) ^ (β₀ + 1 / (a : ℝ)) := two_mul_two_pow_rpow ha1 β₀
    _ ≤ ((2 ^ a : ℕ) : ℝ) ^ (β₀ + ε) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

/-- **The below-prize-scale form.**  With the canonical sub-quartic threshold `β₀ ≤ 3`
(the [TZ24] instantiation `β₀ ∈ (12/5, 3]`), the produced prime is `≤ (2^a)^4` — the exact
premise shape of the off-BGK floor arrow (`tzSupplyOne_gives_prime_below_prize` in
`_FloorLinnikThornerZamanArrow.lean`), now derived from the faithful [TZ24] Thm 1.1 form
instead of a bare per-instance supply. -/
theorem exists_dyadic_prime_below_prize {c : ℝ} {a₀ : ℕ} {β₀ : ℝ}
    (hTZ : TZDyadicShortIntervalLB c a₀ β₀) {a : ℕ} (ha : a₀ ≤ a) (ha1 : 1 ≤ a)
    (hβ₀ : β₀ ≤ 3)
    (hone : (1 : ℝ) ≤ c * ((2 ^ a : ℕ) : ℝ) ^ β₀ /
        ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ β₀))) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 2 ^ a] ∧ (p : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) ^ 4 := by
  have ha0 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
  obtain ⟨p, hp, hmod, hle⟩ :=
    exists_dyadic_prime_le_rpow_exponent hTZ ha ha1 hone (ε := 1 / (a : ℝ)) le_rfl
  have hn1 : (1 : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have hinv : 1 / (a : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact ha0
  refine ⟨p, hp, hmod, ?_⟩
  calc (p : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) ^ (β₀ + 1 / (a : ℝ)) := hle
    _ ≤ ((2 ^ a : ℕ) : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ = ((2 ^ a : ℕ) : ℝ) ^ (4 : ℕ) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    _ = ((2 ^ a : ℕ) : ℝ) ^ 4 := by norm_num

end ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping

namespace ArkLib.ProximityGap.KKH26

/-! ### Concrete ladder extension: the missing `n ≤ 256` rungs at β ∈ {3, 4}
(unconditional; witness primes from `scripts/probes/probe_466_tz_ladder_rungs.py`) -/

/-- **Concrete discharge for `n = 128, β = 3`.**  The window `[128³, 2·128³] =
`[2097152, 4194304]` contains the twelve primes listed below, all `≡ 1 (mod 128)`. -/
theorem tzPrimeSupply_128_three : TZPrimeSupply 128 (3 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((128 : ℕ) : ℝ) ^ (3 : ℝ) = 2097152 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({2100097, 2100353, 2100737, 2101249, 2102273, 2103041, 2103169, 2103553,
          2104961, 2105729, 2107393, 2108033} : Finset ℕ) ⊆ tzWindow 128 (3 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (12 : ℕ)
      = ({2100097, 2100353, 2100737, 2101249, 2102273, 2103041, 2103169, 2103553,
          2104961, 2105729, 2107393, 2108033} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 128 (3 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 256, β = 3`.**  The window `[256³, 2·256³] =
`[16777216, 33554432]` contains the twelve primes listed below, all `≡ 1 (mod 256)`. -/
theorem tzPrimeSupply_256_three : TZPrimeSupply 256 (3 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((256 : ℕ) : ℝ) ^ (3 : ℝ) = 16777216 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({16777729, 16778497, 16780289, 16780801, 16783873, 16787713, 16789249, 16790017,
          16790273, 16793089, 16795393, 16796161} : Finset ℕ) ⊆ tzWindow 256 (3 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (12 : ℕ)
      = ({16777729, 16778497, 16780289, 16780801, 16783873, 16787713, 16789249, 16790017,
          16790273, 16793089, 16795393, 16796161} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 256 (3 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 128, β = 4`.**  The window `[128⁴, 2·128⁴] =
`[268435456, 536870912]` contains the twelve primes listed below, all `≡ 1 (mod 128)`. -/
theorem tzPrimeSupply_128_four : TZPrimeSupply 128 (4 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((128 : ℕ) : ℝ) ^ (4 : ℝ) = 268435456 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({268437889, 268438657, 268438913, 268439681, 268440449, 268440577, 268440833,
          268440961, 268441601, 268441729, 268445057, 268447873} : Finset ℕ)
        ⊆ tzWindow 128 (4 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (12 : ℕ)
      = ({268437889, 268438657, 268438913, 268439681, 268440449, 268440577, 268440833,
          268440961, 268441601, 268441729, 268445057, 268447873} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 128 (4 : ℝ)).card := Finset.card_le_card hsub

set_option maxHeartbeats 1600000 in
/-- **Concrete discharge for `n = 256, β = 4`.**  The window `[256⁴, 2·256⁴] =
`[4294967296, 8589934592]` contains the eight primes listed below, all `≡ 1 (mod 256)`.
This completes the `n ≤ 256` concrete ladder at every exponent `β ∈ {2, 3, 4}`. -/
theorem tzPrimeSupply_256_four : TZPrimeSupply 256 (4 : ℝ) 8 := by
  refine ⟨?_⟩
  have hpow : ((256 : ℕ) : ℝ) ^ (4 : ℝ) = 4294967296 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({4294968833, 4294973953, 4294977793, 4294979329, 4294983937, 4294986497,
          4294988801, 4294989313} : Finset ℕ) ⊆ tzWindow 256 (4 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (8 : ℕ)
      = ({4294968833, 4294973953, 4294977793, 4294979329, 4294983937, 4294986497,
          4294988801, 4294989313} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 256 (4 : ℝ)).card := Finset.card_le_card hsub

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit (expected: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) -/
open ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping in
#print axioms apPrimesIoc_subset_tzWindow
open ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping in
#print axioms tzPrimeSupply_dyadic_of_shortIntervalLB
open ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping in
#print axioms tzPrimeSupply_dyadic_of_shortIntervalLB_natFloor
open ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping in
#print axioms tzPrimeSupply_dyadic_beta3_of_shortIntervalLB
open ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping in
#print axioms tzPrimeSupply_dyadic_beta4_of_shortIntervalLB
open ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping in
#print axioms exists_dyadic_prime_le_two_mul_rpow
open ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping in
#print axioms two_mul_two_pow_rpow
open ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping in
#print axioms exists_dyadic_prime_le_rpow_exponent
open ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping in
#print axioms exists_dyadic_prime_below_prize
#print axioms ArkLib.ProximityGap.KKH26.tzPrimeSupply_128_three
#print axioms ArkLib.ProximityGap.KKH26.tzPrimeSupply_256_three
#print axioms ArkLib.ProximityGap.KKH26.tzPrimeSupply_128_four
#print axioms ArkLib.ProximityGap.KKH26.tzPrimeSupply_256_four
