/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# The orbit count is doubling-INVARIANT, so the plateau is invisible to the orbit skeleton

## Target (refines lalalune's master-open-thread item #3, #444)

`_Close26_PrimitiveCleanRecursion` proves the clean dyadic recursion `D*_{2n}(m) = D*_n(m-1)`
(no plateau) at PRIMITIVE far directions (`gcd(b-a, n) = 1`), and explicitly defers the
IMPRIMITIVE analogue (the plateau-doubling rung, `B27`) as the open "landable brick." The
empirical measurement (lalalune: `w(16)=1, w(32)=2`) shows the plateau IS active at imprimitive
binding directions.

This file pins a clean STRUCTURAL CONSTRAINT on any route to that imprimitive recursion through
the in-tree **orbit-count crossing law** (`OrbitCountCrossingLaw`): the governing orbit count
`N = d = gcd(b-a, n)` is **doubling-invariant at a fixed direction**, at PRIMITIVE *and*
IMPRIMITIVE directions alike. Hence the plateau-doubling is **invisible** to the orbit-count
skeleton: it cannot be the source of the extra rung, and lives strictly in the gap between the
orbit count `N` and the distinct-gamma count `D*` (the BGK/incidence content).

## The arithmetic core (axiom-clean, no `sorry`)

In the prize tower `n = 2^a`, the far direction is the fixed shift `s = b-a` (mod `n`); the
orbit count is `d = gcd(s, n)` and the orbit size `S = n / d` (supply `S * d = n`,
`OrbitCountCrossingLaw`). Doubling the level `n -> 2n` keeps the SAME direction `s`. The claim:

  for `n = 2^a` and any in-range shift `1 <= s <= n`,  `gcd(s, 2n) = gcd(s, n)`.

Proof skeleton: write the 2-adic valuation `t = v_2(s)`. For a power of two,
`gcd(s, 2^a) = 2^min(t, a)`. Since `1 <= s <= 2^a` forces `t <= a` (else `2^(a+1) | s` gives
`s >= 2^(a+1) > 2^a >= s`), we get `min(t, a) = min(t, a+1) = t`, so the two gcds coincide.

## What is proven here

* `gcd_two_pow_eq_two_pow_min_v2`: `gcd(s, 2^a) = 2^min(v2 s, a)` for `s > 0` (the pin).
* `v2_le_of_le_two_pow`: `1 <= s <= 2^a => v_2(s) <= a` (the in-range valuation bound).
* `gcd_doubling_invariant` (headline): `1 <= s <= 2^a => gcd(s, 2*2^a) = gcd(s, 2^a)`.
* `orbitCount_doubling_invariant`: packaged on the supply identity: the orbit count `d`
  (`= N` at a fixed direction `s`) is unchanged under `n -> 2n` at primitive AND imprimitive
  directions, so the orbit-count crossing-law budget threshold `N <= d` is doubling-stable.

## Honest scope

This is a CONSTRAINT lemma (rule 4), NOT a CORE closure. It does NOT prove or disprove the prize.
It refines item #3 by showing the orbit-count skeleton route to the imprimitive recursion is
**plateau-blind**: `N(2n) = N(n)` everywhere, so the measured plateau (`w(32)=2`) cannot come from
the orbit count and must live in the distinct-gamma `D*` beyond `N` (the open BGK content). Pure
2-adic arithmetic; field-universal in the formula; thinness enters only via the tower `n = 2^a`.
Makes NO capacity/beyond-Johnson/sub-linear claim; ASYMPTOTIC GUARD cliff-at-n/2 untouched. CORE
`M(mu_n) <= C sqrt(n log(p/n))` stays OPEN.
-/

open Finset

namespace ArkLib.ProximityGap.OrbitCountDoublingInvariant

/-- For `s > 0`, the gcd of `s` with a power of two is the matching power of two cut off at the
2-adic valuation of `s`: `gcd(s, 2^a) = 2^min(v2 s, a)`, where `v2 s = s.factorization 2`. -/
theorem gcd_two_pow_eq_two_pow_min_v2 (s a : ℕ) (hs : 0 < s) :
    Nat.gcd s (2 ^ a) = 2 ^ min (s.factorization 2) a := by
  have hp : Nat.Prime 2 := Nat.prime_two
  -- factorization of the gcd is the pointwise min of factorizations
  have hsne : s ≠ 0 := hs.ne'
  have h2ane : (2 ^ a) ≠ 0 := (pow_pos (by norm_num : 0 < 2) a).ne'
  -- gcd is a power of two: its only possible prime factor is 2 (it divides 2^a)
  have hdvd : Nat.gcd s (2 ^ a) ∣ 2 ^ a := Nat.gcd_dvd_right _ _
  obtain ⟨k, hk, hgeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  -- (2^a).factorization 2 = a
  have hpa : (2 ^ a).factorization 2 = a := by
    rw [Nat.Prime.factorization_pow hp]; simp
  -- v2 of gcd = min of the v2's
  have hfac : (Nat.gcd s (2 ^ a)).factorization 2
      = min (s.factorization 2) ((2 ^ a).factorization 2) := by
    rw [Nat.factorization_gcd hsne h2ane]; rfl
  rw [hpa] at hfac
  -- gcd = 2^k, so its v2 = k
  have hvk : (Nat.gcd s (2 ^ a)).factorization 2 = k := by
    rw [hgeq, Nat.Prime.factorization_pow hp]; simp
  rw [hvk] at hfac
  rw [hgeq, hfac]

/-- An in-range shift has small valuation: `1 <= s <= 2^a => v2(s) <= a`. If `v2(s) > a` then
`2^(a+1) | s`, forcing `s >= 2^(a+1) > 2^a >= s`, a contradiction. -/
theorem v2_le_of_le_two_pow (s a : ℕ) (hs : 0 < s) (hle : s ≤ 2 ^ a) :
    s.factorization 2 ≤ a := by
  by_contra hgt
  have hgt' : a + 1 ≤ s.factorization 2 := by omega
  -- 2^(v2 s) divides s
  have hdvd : 2 ^ (s.factorization 2) ∣ s := Nat.ordProj_dvd s 2
  have hge : 2 ^ (s.factorization 2) ≤ s := Nat.le_of_dvd hs hdvd
  have hstep : 2 ^ (a + 1) ≤ 2 ^ (s.factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hgt'
  have hbig : 2 ^ a < 2 ^ (a + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self a)
  omega

/-- **Headline: the orbit count is doubling-invariant.**  For the prize tower `n = 2^a` and any
in-range far direction `1 <= s <= n`, doubling the level keeps the gcd fixed:
`gcd(s, 2n) = gcd(s, n)`. Equivalently, the orbit count `N = gcd(s, n)` (the
`OrbitCountCrossingLaw` budget threshold) is unchanged under `n -> 2n`: at PRIMITIVE
(`gcd = 1`) and IMPRIMITIVE (`gcd` even) directions alike. -/
theorem gcd_doubling_invariant (s a : ℕ) (hs : 0 < s) (hle : s ≤ 2 ^ a) :
    Nat.gcd s (2 * 2 ^ a) = Nat.gcd s (2 ^ a) := by
  have hpow : 2 * 2 ^ a = 2 ^ (a + 1) := by ring
  rw [hpow, gcd_two_pow_eq_two_pow_min_v2 s (a + 1) hs,
      gcd_two_pow_eq_two_pow_min_v2 s a hs]
  have hv : s.factorization 2 ≤ a := v2_le_of_le_two_pow s a hs hle
  have h1 : min (s.factorization 2) (a + 1) = s.factorization 2 := by omega
  have h2 : min (s.factorization 2) a = s.factorization 2 := by omega
  rw [h1, h2]

/-- **Packaged on the supply identity.**  Let `s = b - a` be the fixed far direction, `n = 2^a`,
and write the orbit count at level `n` as `d = gcd(s, n)` with supply `S * d = n`.  Then the
orbit count at level `2n` for the SAME direction is the SAME `d`.  Concretely: the crossing-law
budget threshold `d` is doubling-stable, so the orbit-count test `N <= d` carries through the
tower unchanged: the plateau-doubling (`w(32) = 2`) is NOT visible at the orbit-count level and
must live in the distinct-gamma count `D*` beyond `N`. -/
theorem orbitCount_doubling_invariant (s a d : ℕ) (hs : 0 < s) (hle : s ≤ 2 ^ a)
    (hd : d = Nat.gcd s (2 ^ a)) :
    Nat.gcd s (2 * 2 ^ a) = d := by
  rw [hd, gcd_doubling_invariant s a hs hle]

end ArkLib.ProximityGap.OrbitCountDoublingInvariant
