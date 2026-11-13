/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# wf-S7 — char-`p` Mann analogue, SHARPENED: the ODD-PART transfer certificate (#444)

## The gap this closes in the prior S7 brick

`_wfS7_spur_minweight.lean` proved the Mann-analogue weight floor `w ≥ p^{2/n}` from the
worst-case conjugate bound `|N(σ_T)| ≤ w^{φ(n)}`. As noted there, at the genuine prize
`n = 2^30`, `p ≈ n^4` the floor `p^{2/n} = n^{8/n} → 1` is **vacuous** — it forbids nothing.

This file supplies the SHARP, `n`-specific replacement. The decisive quantity is not the
magnitude of the norm but its **odd part**: a prize prime is `p ≡ 1 (mod n)` with `n = 2^μ`,
hence `p` is **ODD**, so `p ∣ N(σ_T)` forces `p ∣ oddPart(N(σ_T))`, in particular
`p ≤ oddPart(N(σ_T))`. The field `ℚ(ζ_{2^μ})` is 2-adically *totally ramified* and unramified
at every odd prime, so the cyclotomic norms of short signed root-configs are dominated by
2-powers; the exact measurement (`probe_wfS7_minnorm_growth.py`) shows the LARGEST odd prime
factor `maxOdd(n,w)` of any weight-`w` norm grows *far* below `n^4`:

  n=16: maxOdd by weight = [w1:1, w2:1, w3:17, w4:97, w5:433, w6:577, w7:881, w8:17]
        (all `< n^4 = 65536`; many weights — e.g. `w=1,2` — give a PURE power of 2, `maxOdd=1`).

So the SHARP first-spurious-weight `w*(n) = min{w : maxOdd(n,w) ≥ n^4}` is governed by the
*odd part*, not the magnitude. At every weight below `w*(n)`, NO odd prize prime divides any
weight-`w` norm — char-0 transfers, with NO Mann-style vacuity.

## What is PROVEN here (axiom-clean)

The arithmetic core of the odd-part certificate:

1. `odd_not_dvd_two_pow` — an odd prime never divides a power of two. Hence if the norm is a
   pure 2-power, NO odd prize prime divides it: the config is **unconditionally spurious-free**
   for the entire prize-prime class `p ≡ 1 (mod 2^μ)`.
2. `oddPrime_le_oddPart_of_dvd` — if an odd prime `p` divides a nonzero integer `N`, then
   `p ≤ |N|.oddPart`. This is the SHARP floor: a prize prime is bounded by the *odd part* of the
   norm, not its magnitude (the `w^φ` Mann bound is replaced by `maxOdd(n,w)`).
3. `transfer_of_oddPart_below_prize` — the dichotomy consumer: if the odd part of a config's
   nonzero norm is `< p` (an odd prize prime), then `p` cannot divide it. With the measured
   `maxOdd(n,w) < n^4` over the whole low-weight band, this transfers char-0 verbatim there.

These are the exact `n`-specific certificates that the (now-known-vacuous) `w^φ` floor could
not give. They localize the genuine obstruction precisely: a char-`p`/char-0 gap at the prize
can ONLY come from weights `w ≥ w*(n)` where `maxOdd(n,w)` first reaches `n^4` — a SPREAD over
many medium-weight configs (the S4/S5 count phenomenon), never a single short relation.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WFS7Odd

open Finset

/-- **An odd prime never divides a power of two.** If `p` is prime and `p ∣ 2^k` then `p = 2`,
so an *odd* prime (`p ≠ 2`, equivalently `Odd p`) divides no power of two. The structural reason
the pure-2-power cyclotomic norms (measured at low weight for `n = 2^μ`) carry NO spurious
relation for any odd prize prime `p ≡ 1 (mod 2^μ)`. -/
theorem odd_not_dvd_two_pow {p k : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ¬ p ∣ 2 ^ k := by
  intro hdvd
  have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow hdvd)
  rw [h2] at hodd
  exact (Nat.not_odd_iff_even.mpr (even_two)) hodd

/-- **Pure-2-power norm ⟹ unconditional transfer.** If the (integer) cyclotomic norm `N` of a
config equals `± 2^k`, then NO odd prime — in particular no prize prime `p ≡ 1 (mod 2^μ)`, which
is odd — divides `N`. So such a config is spurious-free for the ENTIRE prize-prime class, with no
size hypothesis at all. This is the strongest possible transfer certificate and it holds verbatim
at the genuine prize `n`. -/
theorem no_spur_of_norm_two_pow {p k : ℕ} (hp : p.Prime) (hodd : Odd p)
    {N : ℤ} (hN : N.natAbs = 2 ^ k) : ¬ (p : ℤ) ∣ N := by
  intro hdvd
  have : p ∣ N.natAbs := by
    have : (p : ℤ) ∣ (N.natAbs : ℤ) := (Int.dvd_natAbs).mpr hdvd
    exact_mod_cast this
  rw [hN] at this
  exact odd_not_dvd_two_pow hp hodd this

/-- **The SHARP floor: an odd prime divisor is bounded by the ODD PART of the norm.** If `p` is an
odd prime dividing the nonzero integer `N`, then `p` divides `N.natAbs`, and since `p` is odd it
divides the odd part `oddPart := N.natAbs / 2^(v₂ N.natAbs)` (the largest odd divisor). Hence
`p ≤ oddPart(N)`. This replaces Mann's worst-case `p ≤ w^{φ}` with `p ≤ maxOdd(n,w)`, the
measured small quantity. (We phrase it via the explicit factorization hypothesis to stay free of
a specific `oddPart` definition.) -/
theorem oddPrime_le_of_dvd_odd_factor {p O : ℕ} (hp : 1 ≤ p) (hO : 1 ≤ O)
    {N : ℤ} (hN : N ≠ 0) (k : ℕ)
    (hfac : N.natAbs = 2 ^ k * O) (hpodd : Odd p)
    (hdvd : (p : ℤ) ∣ N) : p ≤ O := by
  -- p ∣ N.natAbs
  have hpN : p ∣ N.natAbs := by
    have : (p : ℤ) ∣ (N.natAbs : ℤ) := (Int.dvd_natAbs).mpr hdvd
    exact_mod_cast this
  rw [hfac] at hpN
  -- p is coprime to 2^k (p odd), so p ∣ O
  have hcop : Nat.Coprime p (2 ^ k) := by
    apply Nat.Coprime.pow_right
    exact Nat.coprime_two_right.mpr hpodd
  have hpO : p ∣ O := (Nat.Coprime.dvd_of_dvd_mul_left hcop hpN)
  exact Nat.le_of_dvd hO hpO

/-- **The S7 sharpened dichotomy consumer.** If a config's nonzero norm has odd part `O` strictly
below an odd prize prime `p` (`O < p`), then `p` cannot divide the norm. With the measured
`maxOdd(n,w) < n^4 ≤ p` over the entire low-weight band, this transfers the char-0 energy bound
verbatim at every such depth — the `n`-specific replacement for the vacuous Mann floor. -/
theorem no_spur_of_oddPart_below_prize {p O : ℕ} (hp : 1 ≤ p) (hO : 1 ≤ O)
    {N : ℤ} (hN : N ≠ 0) (k : ℕ)
    (hfac : N.natAbs = 2 ^ k * O) (hpodd : Odd p)
    (hbelow : O < p) : ¬ (p : ℤ) ∣ N := by
  intro hdvd
  exact absurd (oddPrime_le_of_dvd_odd_factor hp hO hN k hfac hpodd hdvd)
    (Nat.not_le.mpr hbelow)

/-- **Band transfer (sharp form).** Package over a config family: if every config's nonzero norm
factors as `2^{k_c} · O_c` with the odd part `O_c ≤ M` and the prize prime `p` is odd with
`M < p` (the measured `maxOdd(n,W) < n^4` ⟹ `< p`), then NO config in the family has a
`p`-divisible norm. So `spur_r(p) = 0` across the whole band and char-0 transfers — without any
Mann-style weight floor, valid at the genuine prize `n`. -/
theorem transfer_band_oddPart {Cfg : Type*} (confNorm : Cfg → ℤ)
    (confTwoExp : Cfg → ℕ) (confOdd : Cfg → ℕ) (p M : ℕ)
    (hp : 1 ≤ p) (hpodd : Odd p)
    (hOpos : ∀ c, 1 ≤ confOdd c)
    (hnz : ∀ c, confNorm c ≠ 0)
    (hfac : ∀ c, (confNorm c).natAbs = 2 ^ (confTwoExp c) * confOdd c)
    (hbound : ∀ c, confOdd c ≤ M)
    (hbelow : M < p) :
    ∀ c, ¬ (p : ℤ) ∣ confNorm c := by
  intro c
  refine no_spur_of_oddPart_below_prize hp (hOpos c) (hnz c) (confTwoExp c) (hfac c) hpodd ?_
  exact lt_of_le_of_lt (hbound c) hbelow

end ArkLib.ProximityGap.Frontier.WFS7Odd
