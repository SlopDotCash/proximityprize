/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic

/-!
# The char-`0` Mann rigidity for three roots of unity (#389)

The cubic orchard identity (`cubic_list_eq_zeroSum`, in-tree) reduces the deepest
pre-capacity supply of the cubic word `x³` on a domain to its **zero-sum-triple count**
`#{(a,b,c) ∈ dom³ : a+b+c = 0}`.  On a multiplicative NTT domain `μ_n` this is an
additive-combinatorics quantity, and `CubicSupplyZeroNTT.lean` exhibits it as *exactly
zero* at `μ_16 ⊂ F₂₅₇` via `decide` — the char-`0` rigidity *surviving* to that prime.

This file proves the **general char-`0` statement** the witnesses instantiate: over `ℂ`,
**no three `n`-th roots of unity sum to zero whenever `3 ∤ n`** (every NTT domain
`μ_{2^k}` qualifies, as do all `n` coprime to 3).

> **`no_three_roots_sum_zero`** — for `n` with `3 ∤ n` and `a,b,c ∈ μ_n(ℂ)`,
> `a + b + c ≠ 0`.
> **`no_three_two_pow_roots_sum_zero`** — the `n = 2^k` corollary (the NTT case).

**Mechanism.** Normalising by `a`, two unit numbers `u, w` with `1 + u + w = 0` have
`u + w = -1`; combined with `|u| = |w| = 1` (conjugate algebra) this forces
`u² + u + 1 = 0`, i.e. `u³ = 1`.  An order of exactly `3` is coprime to `n` (since
`3 ∤ n`), so `orderOf u ∣ gcd(3,n) = 1`, giving `u = 1` and the false `1 + 1 + 1 = 0`.

**Scope (honesty).** This is the char-`0` truth only.  Over `F_q` it can *fail* for
small primes (extra coincidences below the rigidity height — see the
`probe_smooth_zero_sum_triples.py` census, where some `μ_{2^k} ⊂ F_p` reach `~n^{5/3}`
zero-sum triples).  Lifting this rigidity to `F_q` for the production domain is a
separate height/Weil obstruction, part of the open sub-Johnson supply wall; this lemma
discharges only its characteristic-zero half.  Issue #389.
-/

open Complex

namespace ProximityGap.ThreeRoots

/-- A unit complex number times its conjugate is `1`. -/
theorem mul_conj_eq_one {u : ℂ} (hu : ‖u‖ = 1) : u * (starRingEnd ℂ) u = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq u, hu]
  norm_num

/-- Two unit complex numbers summing to `-1` each satisfy `u² + u + 1 = 0`
(they are the two primitive cube roots of unity). -/
theorem sq_add_self_add_one_of_unit_sum {u v : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hsum : u + v = -1) :
    u ^ 2 + u + 1 = 0 := by
  have hvu : v = -1 - u := by linear_combination hsum
  have hnu : u * (starRingEnd ℂ) u = 1 := mul_conj_eq_one hu
  have hnv : v * (starRingEnd ℂ) v = 1 := mul_conj_eq_one hv
  have hcv : (starRingEnd ℂ) v = -1 - (starRingEnd ℂ) u := by
    rw [hvu]; simp [map_sub, map_one, map_neg]
  have hsumc : u + (starRingEnd ℂ) u = -1 := by
    have hprod : (-1 - u) * (-1 - (starRingEnd ℂ) u) = 1 := by
      rw [← hvu, ← hcv]; exact hnv
    have hexp : (-1 - u) * (-1 - (starRingEnd ℂ) u)
        = 1 + (u + (starRingEnd ℂ) u) + u * (starRingEnd ℂ) u := by ring
    rw [hexp, hnu] at hprod
    linear_combination hprod
  have hconju : (starRingEnd ℂ) u = -1 - u := by linear_combination hsumc
  have hmul := hnu
  rw [hconju] at hmul
  linear_combination -hmul

/-- **The char-`0` Mann rigidity, general**: for `n` with `3 ∤ n`, no three `n`-th roots
of unity in `ℂ` sum to zero. -/
theorem no_three_roots_sum_zero {n : ℕ} (hn : n ≠ 0) (h3 : ¬ (3 ∣ n))
    {a b c : ℂ} (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1)
    (hsum : a + b + c = 0) : False := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h, zero_pow hn] at ha; exact zero_ne_one ha
  set u := b / a with hudef
  set w := c / a with hwdef
  have hu1 : u ^ n = 1 := by rw [hudef, div_pow, hb, ha, div_one]
  have hw1 : w ^ n = 1 := by rw [hwdef, div_pow, hc, ha, div_one]
  have husum : (1 : ℂ) + u + w = 0 := by
    rw [hudef, hwdef]; field_simp; linear_combination hsum
  have hnu : ‖u‖ = 1 := norm_eq_one_of_pow_eq_one hu1 hn
  have hnw : ‖w‖ = 1 := norm_eq_one_of_pow_eq_one hw1 hn
  have huw : u + w = -1 := by linear_combination husum
  have hquad : u ^ 2 + u + 1 = 0 := sq_add_self_add_one_of_unit_sum hnu hnw huw
  have hu3 : u ^ 3 = 1 := by linear_combination (u - 1) * hquad
  have hdvd3 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have hdvdn : orderOf u ∣ n := orderOf_dvd_of_pow_eq_one hu1
  have hcop : Nat.gcd 3 n = 1 :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr h3
  have hdvd1 : orderOf u ∣ 1 := hcop ▸ Nat.dvd_gcd hdvd3 hdvdn
  have hu1' : u = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  rw [hu1'] at hquad
  norm_num at hquad

/-- **The NTT corollary**: no three `2^k`-th roots of unity in `ℂ` sum to zero. -/
theorem no_three_two_pow_roots_sum_zero (k : ℕ)
    {a b c : ℂ} (ha : a ^ (2 ^ k) = 1) (hb : b ^ (2 ^ k) = 1) (hc : c ^ (2 ^ k) = 1)
    (hsum : a + b + c = 0) : False :=
  no_three_roots_sum_zero (pow_ne_zero _ (by norm_num))
    (by
      intro h
      have := Nat.Prime.dvd_of_dvd_pow (p := 3) (by norm_num) h
      norm_num at this)
    ha hb hc hsum

end ProximityGap.ThreeRoots

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.ThreeRoots.no_three_roots_sum_zero
#print axioms ProximityGap.ThreeRoots.no_three_two_pow_roots_sum_zero
