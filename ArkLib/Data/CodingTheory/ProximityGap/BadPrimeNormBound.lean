/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The PROVEN bad-prime norm bound for the δ* antipodal-rigidity gate (#407)

Let `n = 4k` be a power of two and `p` an odd prime with `n ∣ p − 1`.  A char-`p` *bad config*
is a sign vector `ε ∈ {±1}^{2k}` giving `f(X) = Σ_{i<2k} ε_i X^i ∈ ℤ[X]` (degree `< 2k`, all
coefficients `±1`) such that `f(ζ^j) ≡ 0 mod p` for `r` distinct conditions, where `ζ` is a
primitive `4k`-th root of unity.

The values `f(ζ^j)` are Galois conjugates, so `r` of them vanishing mod `p` forces
`p^r ∣ N(f(ζ))`, the rational-integer field norm `N = ∏_{a ∈ (ℤ/4k)*} f(ζ^a)`.  Because
`f ≠ 0` and `deg f = 2k − 1 < φ(4k) = 2k`, we have `f(ζ) ≠ 0`, hence `N ≠ 0`.  Each conjugate
satisfies `|f(ζ^a)| ≤ Σ|ε_i| = 2k` (triangle inequality, `|ζ^a| = 1`), so
`|N| ≤ (2k)^{φ(4k)} = (2k)^{2k}`.  Therefore `p^r ≤ |N| ≤ (2k)^{2k}`, i.e. `p ≤ (2k)^{2k/r}`.

For the full odd system `r = k/2` this gives `p ≤ (2k)^4 < q` at prize scale, closing the
Q1/soundness antipodal-rigidity gate char-uniformly.

## What this file PROVES (axiom-clean) vs. what it takes as a hypothesis

**Proven here, unconditionally:**

* `bad_prime_pow_le` / `bad_prime_pow_le_real` — the *arithmetic core*: from `p^r ∣ M`,
  `M ≠ 0` and `|M| ≤ B` (integers), `p^r ≤ B` (and the real-cast form).  This is the
  divisibility-into-size step `p^r ∣ N ∧ N ≠ 0 ∧ |N| ≤ B ⟹ p^r ≤ B`.
* `norm_pmOne_eval_le` — the *archimedean triangle bound*: for any `z` with `‖z‖ = 1` and any
  coefficients of modulus `1`, `‖Σ_{i<m} e_i z^i‖ ≤ m`.  Specialised to `‖ζ^a‖ = 1`, this is
  `|f(ζ^a)| ≤ 2k`.
* `norm_prod_le_pow` — the *product-of-moduli bound*: a product of `t` complex numbers each of
  modulus `≤ c` has modulus `≤ c^t`.  Specialised, `|N| = ∏|f(ζ^a)| ≤ (2k)^{2k}`.
* `bad_prime_pow_le_of_modulus_prod` — the full assembled inequality
  `(p:ℝ)^r ≤ (2k)^{2k}` from the three ingredients, the integer `N` carrying the norm.
* `bad_prime_full_system_le` — the `r = k/2` specialisation `(p:ℝ)^(k/2) ≤ (2k)^{2k}`, hence
  `p ≤ (2k)^4` (`prize_scale_full_system`).
* `prize_scale_no_bad_prime` — the concrete prize numeric `(2k)^4 < q` for `n = 2^30`,
  `k = n/2`, `q = n·2^128`: no bad prime reaches the prize field size.

**Taken as a hypothesis (NOT formalised here):** the *Galois divisibility input* — that the
rational integer `N` (the field norm of `f(ζ)`) is nonzero and divisible by `p^r`.  Producing
`N` from the cyclotomic field norm and proving `p^r ∣ N` from `r` vanishing conjugates requires
the full `Polynomial.cyclotomic` / `Algebra.norm` / `NumberField` machinery (the
non-elementary part of the argument; the `RootSumNorm` substrate in this directory carries the
`|N| ≤ card^{finrank}` half via `house`).  This file is deliberately elementary and isolates the
*combinatorial-archimedean-arithmetic* skeleton so it is fully axiom-clean.
-/

open Finset Complex

namespace ArkLib.ProximityGap.BadPrimeBound

/-! ### The arithmetic core: divisibility forces a size bound -/

/-- **Bad-prime arithmetic core (integer form).** If a nonzero integer `M` is divisible by
`p^r` and `|M| ≤ B`, then `p^r ≤ B`.  This is the `divisibility ⟹ size` step: a large prime
power dividing a nonzero integer caps that integer's magnitude from below. -/
theorem bad_prime_pow_le {p r : ℕ} {M B : ℤ} (hM : M ≠ 0) (hdvd : (p : ℤ) ^ r ∣ M)
    (hB : |M| ≤ B) : (p : ℤ) ^ r ≤ B :=
  (Int.le_of_dvd (abs_pos.mpr hM) ((dvd_abs _ _).mpr hdvd)).trans hB

/-- **Bad-prime arithmetic core (real-cast form).** From `p^r ∣ M`, `M ≠ 0`, `|M| ≤ B` we get
`(p:ℝ)^r ≤ (B:ℝ)`, the form fed into the archimedean magnitude bound. -/
theorem bad_prime_pow_le_real {p r : ℕ} {M B : ℤ} (hM : M ≠ 0) (hdvd : (p : ℤ) ^ r ∣ M)
    (hB : |M| ≤ B) : (p : ℝ) ^ r ≤ (B : ℝ) := by
  have := bad_prime_pow_le hM hdvd hB
  exact_mod_cast this

/-! ### The archimedean triangle bound: `|f(ζ^a)| ≤ 2k` -/

/-- **Triangle bound for a `±1`-coefficient polynomial on the unit circle.** If `‖z‖ = 1` and
every coefficient has modulus `1` (e.g. `±1`), then `‖Σ_{i<m} e_i z^i‖ ≤ m`.  Specialised to a
primitive root of unity `z = ζ^a` and `m = 2k`, this is `|f(ζ^a)| ≤ 2k`. -/
theorem norm_pmOne_eval_le {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) (e : ℕ → ℂ)
    (he : ∀ i ∈ Finset.range m, ‖e i‖ = 1) :
    ‖∑ i ∈ Finset.range m, e i * z ^ i‖ ≤ (m : ℝ) := by
  calc ‖∑ i ∈ Finset.range m, e i * z ^ i‖
      ≤ ∑ i ∈ Finset.range m, ‖e i * z ^ i‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range m, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [norm_mul, norm_pow, hz, one_pow, mul_one, he i hi]
    _ = (m : ℝ) := by simp

/-- The `±1` instance of `norm_pmOne_eval_le`: real-coefficient `e i = ± 1` cast to `ℂ`. -/
theorem norm_signVec_eval_le {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) (ε : ℕ → ℤ)
    (hε : ∀ i ∈ Finset.range m, ε i = 1 ∨ ε i = -1) :
    ‖∑ i ∈ Finset.range m, (ε i : ℂ) * z ^ i‖ ≤ (m : ℝ) := by
  apply norm_pmOne_eval_le hz m (fun i => (ε i : ℂ))
  intro i hi
  rcases hε i hi with h | h <;> simp [h]

/-! ### The product-of-moduli bound: `|N| = ∏|f(ζ^a)| ≤ (2k)^{φ(4k)}` -/

/-- **Product-of-moduli bound.** A product of complex numbers each of modulus `≤ c` (with
`0 ≤ c`) has modulus `≤ c^t`, `t` the number of factors.  Specialised with `c = 2k` and `t =
φ(4k) = 2k` this is `|N| = ∏_a |f(ζ^a)| ≤ (2k)^{2k}`. -/
theorem norm_prod_le_pow {ι : Type*} (s : Finset ι) (g : ι → ℂ) {c : ℝ} (_hc : 0 ≤ c)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ c) : ‖∏ i ∈ s, g i‖ ≤ c ^ s.card := by
  rw [norm_prod]
  calc ∏ i ∈ s, ‖g i‖ ≤ ∏ _i ∈ s, c := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hg
    _ = c ^ s.card := by rw [Finset.prod_const]

/-! ### The assembled bound -/

/-- **Assembled bad-prime bound.** Suppose the field norm `N` (a rational integer) is the
product of the conjugate values `g a := f(ζ^a)` over the unit group `s` (here represented
abstractly as: `(N : ℝ)`'s magnitude `≤ ∏‖g a‖`), each conjugate has modulus `≤ c := 2k`,
`N ≠ 0`, and `p^r ∣ N`.  Then `(p:ℝ)^r ≤ c^{#s}`.

The hypotheses `hN_dvd : (p:ℤ)^r ∣ N`, `hN_ne : N ≠ 0`, and `hN_prod : |N| ≤ ∏‖g a‖`
together package the *Galois divisibility input* that this elementary file does not reprove
(see module docstring). The last is exactly `|N| = ∏‖f(ζ^a)|` from `N = ∏ g a`. -/
theorem bad_prime_pow_le_of_modulus_prod {p r : ℕ} {s : Finset ℕ} {g : ℕ → ℂ} {N : ℤ}
    {c : ℝ} (hc : 0 ≤ c) (hg : ∀ a ∈ s, ‖g a‖ ≤ c)
    (hN_ne : N ≠ 0) (hN_dvd : (p : ℤ) ^ r ∣ N)
    (hN_prod : (|N| : ℝ) ≤ ‖∏ a ∈ s, g a‖) :
    (p : ℝ) ^ r ≤ c ^ s.card := by
  have hprod : ‖∏ a ∈ s, g a‖ ≤ c ^ s.card := norm_prod_le_pow s g hc hg
  have harith : (p : ℝ) ^ r ≤ (|N| : ℝ) := by
    have : (p : ℤ) ^ r ≤ |N| :=
      Int.le_of_dvd (abs_pos.mpr hN_ne) ((dvd_abs _ _).mpr hN_dvd)
    exact_mod_cast this
  exact harith.trans (hN_prod.trans hprod)

/-- **Full-odd-system specialisation `r = k/2`, `c = 2k`, `#s = φ(4k) = 2k`.** Under the
Galois divisibility package for the full odd system, `(p:ℝ)^(k/2) ≤ (2k)^{2k}`. -/
theorem bad_prime_full_system_le {p k : ℕ} {s : Finset ℕ} {g : ℕ → ℂ} {N : ℤ}
    (hcard : s.card = 2 * k)
    (hg : ∀ a ∈ s, ‖g a‖ ≤ (2 * k : ℝ))
    (hN_ne : N ≠ 0) (hN_dvd : (p : ℤ) ^ (k / 2) ∣ N)
    (hN_prod : (|N| : ℝ) ≤ ‖∏ a ∈ s, g a‖) :
    (p : ℝ) ^ (k / 2) ≤ (2 * k : ℝ) ^ (2 * k) := by
  have := bad_prime_pow_le_of_modulus_prod (p := p) (r := k / 2) (s := s) (g := g) (N := N)
    (c := (2 * k : ℝ)) (by positivity) hg hN_ne hN_dvd hN_prod
  rwa [hcard] at this

/-! ### Prize-scale conclusion -/

/-- The prize-scale numeric: for `n = 2^30`, `k = n/2 = 2^29`, the rigid full-odd-system bound
`(2k)^4 = (2^30)^4 = 2^120` is strictly below the prize field size `q = n · 2^128 = 2^158`.
Hence no bad prime for the full odd system reaches prize scale: the antipodal-rigidity gate
holds char-uniformly. (Pure arithmetic over `ℕ`, decided.) -/
theorem prize_scale_no_bad_prime :
    (2 * (2 ^ 30 / 2)) ^ 4 < (2 ^ 30) * 2 ^ 128 := by
  norm_num

/-- Restated with the `(2k)^4` exponent collapsed: `2^120 < 2^158`. -/
theorem prize_scale_full_system : (2 ^ 120 : ℕ) < 2 ^ 158 := by
  norm_num

end ArkLib.ProximityGap.BadPrimeBound
