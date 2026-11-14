/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The `t = 3` ceiling-column zero law

For the monomial pencil `(X^a, X^(n-1))` evaluated on the `n`-th roots of unity, the scalar
`0` is *bad* at `t = 3` exactly when `X^a` is affine on three distinct `n`-th roots of unity
(`ZeroBad`). This file proves the gcd law

  `ZeroBad ↔ 3 ≤ gcd a n ∨ 3 ≤ gcd (a - 1) n`

in the following form:

* `zeroBad_of_law`: over any field containing a primitive `n`-th root of unity, the gcd law
  forces `ZeroBad` (the points `1, ω, ω²` for a primitive `gcd`-th root `ω`);
* `zeroBad_complex_iff`: over `ℂ` the gcd law is exact. The converse direction uses
  `conj w = w⁻¹` on the unit circle: conjugating the collinearity relation either kills its
  common value (then all three `a`-th powers agree) or forces `y^(a-1) = z^(a-1)`.

## Scope

This is one column (`b = n - 1`) of the `t = 3` monomial-pencil census. Nothing is claimed
about other columns, `t ≥ 4`, census maxima, `δ*`, or the prize. Over finite fields only the
forward implication `zeroBad_of_law` is proved here; the converse fails at small primes.
-/

namespace ProximityPrize.T3CeilingColumnZeroLaw

/-- `(x, x^a)`, `(y, y^a)`, `(z, z^a)` are collinear: the second divided difference of
`X^a` at `x, y, z` vanishes (cross-multiplied, so no division). -/
def Collinear3 {K : Type*} [Field K] (a : ℕ) (x y z : K) : Prop :=
  (y - x) * (z ^ a - x ^ a) = (z - x) * (y ^ a - x ^ a)

/-- `0` is a bad scalar of the pencil `(X^a, X^(n-1))` on `μ_n`: three distinct `n`-th roots
of unity at which `X^a` is affine. -/
def ZeroBad (K : Type*) [Field K] (n a : ℕ) : Prop :=
  ∃ x y z : K, x ^ n = 1 ∧ y ^ n = 1 ∧ z ^ n = 1 ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ Collinear3 a x y z

/-- The gcd law. (`a - 1` is truncated subtraction; at `a = 0` the first disjunct already
holds because `Nat.gcd 0 n = n`.) -/
def Law (n a : ℕ) : Prop := 3 ≤ Nat.gcd a n ∨ 3 ≤ Nat.gcd (a - 1) n

/-- A primitive `n`-th root yields, for each divisor `3 ≤ d ∣ n`, a `d`-th root of unity `ω`
with `1, ω, ω²` pairwise distinct `n`-th roots of unity. -/
private lemma exists_three_roots {K : Type*} [Field K] {n d : ℕ} {ζ : K}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (hd : 3 ≤ d) (hdn : d ∣ n) :
    ∃ ω : K, ω ^ n = 1 ∧ ω ^ d = 1 ∧ (1 : K) ≠ ω ∧ (1 : K) ≠ ω ^ 2 ∧ ω ≠ ω ^ 2 := by
  obtain ⟨m, rfl⟩ := hdn
  have hω : IsPrimitiveRoot (ζ ^ m) d := hζ.pow hn (mul_comm d m)
  have hinj : ∀ i j : ℕ, i < d → j < d → (ζ ^ m) ^ i = (ζ ^ m) ^ j → i = j :=
    fun i j hi hj h => hω.pow_inj hi hj h
  refine ⟨ζ ^ m, ?_, hω.pow_eq_one, ?_, ?_, ?_⟩
  · rw [pow_mul, hω.pow_eq_one, one_pow]
  · intro h
    have := hinj 0 1 (by omega) (by omega) (by simpa using h)
    omega
  · intro h
    have := hinj 0 2 (by omega) (by omega) (by simpa using h)
    omega
  · intro h
    have := hinj 1 2 (by omega) (by omega) (by simpa using h)
    omega

/-- T1. Over any field containing a primitive `n`-th root of unity, the law forces a zero. -/
theorem zeroBad_of_law {K : Type*} [Field K] {n a : ℕ} {ζ : K}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (h : Law n a) : ZeroBad K n a := by
  rcases h with h | h
  · obtain ⟨ω, hωn, hωd, h1, h2, h3⟩ :=
      exists_three_roots hn hζ h (Nat.gcd_dvd_right a n)
    have hωa : ω ^ a = 1 := by
      obtain ⟨c, hc⟩ := Nat.gcd_dvd_left a n
      rw [hc, pow_mul, hωd, one_pow]
    refine ⟨1, ω, ω ^ 2, one_pow n, hωn, by rw [← pow_mul, mul_comm, pow_mul, hωn, one_pow],
      h1, h2, h3, ?_⟩
    unfold Collinear3
    rw [← pow_mul, mul_comm 2 a, pow_mul, hωa]
    ring
  · obtain ⟨ω, hωn, hωd, h1, h2, h3⟩ :=
      exists_three_roots hn hζ h (Nat.gcd_dvd_right (a - 1) n)
    have hωb : ω ^ (a - 1) = 1 := by
      obtain ⟨c, hc⟩ := Nat.gcd_dvd_left (a - 1) n
      rw [hc, pow_mul, hωd, one_pow]
    refine ⟨1, ω, ω ^ 2, one_pow n, hωn, by rw [← pow_mul, mul_comm, pow_mul, hωn, one_pow],
      h1, h2, h3, ?_⟩
    unfold Collinear3
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      ring
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hωb
      have hωa : ω ^ (b + 1) = ω := by rw [pow_succ, hωb, one_mul]
      have hω2a : (ω ^ 2) ^ (b + 1) = ω ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul, hωa]
      rw [hωa, hω2a]
      ring

/-- In a field, if two nonzero `n`-th roots of unity `p ≠ q` have equal `c`-th powers and
`gcd c n < 3`, then `p = -q`. -/
private lemma eq_neg_of_pow_eq {K : Type*} [Field K] {n c : ℕ} (hn : 0 < n) {p q : K}
    (hp : p ^ n = 1) (hq : q ^ n = 1) (hpq : p ≠ q) (hc : p ^ c = q ^ c)
    (hg : Nat.gcd c n < 3) : p = -q := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp [zero_pow hn.ne'] at hq
  set w := p / q with hw
  have hwc : w ^ c = 1 := by rw [hw, div_pow, hc, div_self (pow_ne_zero _ hq0)]
  have hwn : w ^ n = 1 := by rw [hw, div_pow, hp, hq, div_one]
  have hwg : w ^ Nat.gcd c n = 1 := (pow_gcd_eq_one).mpr ⟨hwc, hwn⟩
  have hw1 : w ≠ 1 := by
    intro h
    exact hpq (by rw [hw, div_eq_one_iff_eq hq0] at h; exact h)
  have hgpos : 0 < Nat.gcd c n := Nat.gcd_pos_of_pos_right c hn
  have hsq : w ^ 2 = 1 := by
    interval_cases h : Nat.gcd c n
    · rw [pow_one] at hwg; exact absurd hwg hw1
    · exact hwg
  have : (w - 1) * (w + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hw1
  · have hwm : w = -1 := eq_neg_of_add_eq_zero_left h
    rw [hw, div_eq_iff hq0] at hwm
    rw [hwm]; ring

/-- On the unit circle of `ℂ`, conjugation is inversion. -/
private lemma conj_eq_inv_of_pow_eq_one {n : ℕ} (hn : 0 < n) {x : ℂ} (hx : x ^ n = 1) :
    (starRingEnd ℂ) x = x⁻¹ := by
  have hnorm : ‖x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hx hn.ne'
  have hmul : x * (starRingEnd ℂ) x = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    simp
  exact (eq_inv_of_mul_eq_one_right hmul)

/-- The converse direction over `ℂ`. -/
private lemma law_of_zeroBad_complex {n a : ℕ} (hn : 0 < n) (h : ZeroBad ℂ n a) : Law n a := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, hcol⟩ := h
  unfold Collinear3 at hcol
  have ne0 : ∀ {w : ℂ}, w ^ n = 1 → w ≠ 0 := by
    rintro w hw rfl
    simp [zero_pow hn.ne'] at hw
  have hx0 := ne0 hx
  have hy0 := ne0 hy
  have hz0 := ne0 hz
  -- Conjugate the collinearity relation; on the unit circle `conj = inv`.
  have hconj := congrArg (starRingEnd ℂ) hcol
  simp only [map_mul, map_sub, map_pow, conj_eq_inv_of_pow_eq_one hn hx,
    conj_eq_inv_of_pow_eq_one hn hy, conj_eq_inv_of_pow_eq_one hn hz] at hconj
  -- Clearing denominators: `E * (z * y^a - y * z^a) = 0`.
  have key : (y - x) * (z ^ a - x ^ a) * (z * y ^ a - y * z ^ a) = 0 := by
    simp only [inv_pow] at hconj
    have hX : x ^ a ≠ 0 := pow_ne_zero _ hx0
    have hY : y ^ a ≠ 0 := pow_ne_zero _ hy0
    have hZ : z ^ a ≠ 0 := pow_ne_zero _ hz0
    generalize x ^ a = X at *
    generalize y ^ a = Y at *
    generalize z ^ a = Z at *
    field_simp at hconj
    linear_combination hconj - y * Z * hcol
  rcases mul_eq_zero.mp key with hE | hE
  · -- The common value vanishes: `x^a = y^a = z^a`.
    have hzx : z ^ a = x ^ a := by
      rcases mul_eq_zero.mp hE with h | h
      · exact absurd (sub_eq_zero.mp h).symm hxy
      · exact sub_eq_zero.mp h
    have hyx : y ^ a = x ^ a := by
      rw [hE] at hcol
      rcases mul_eq_zero.mp hcol.symm with h | h
      · exact absurd (sub_eq_zero.mp h).symm hxz
      · exact sub_eq_zero.mp h
    left
    by_contra hlt
    rw [not_le] at hlt
    have h1 := eq_neg_of_pow_eq hn hy hx hxy.symm hyx hlt
    have h2 := eq_neg_of_pow_eq hn hz hx hxz.symm hzx hlt
    exact hyz (h1.trans h2.symm)
  · -- Otherwise `z * y^a = y * z^a`, so `y^(a-1) = z^(a-1)`.
    have cancel : ∀ {p q : ℂ} {b : ℕ}, p ≠ 0 → q ≠ 0 →
        q * p ^ (b + 1) = p * q ^ (b + 1) → p ^ b = q ^ b := by
      intro p q b hp hq h
      have : p * q * (p ^ b - q ^ b) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' (mul_ne_zero hp hq)
      · exact sub_eq_zero.mp h'
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      exact absurd (by simpa using sub_eq_zero.mp hE) hyz.symm
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hb : y ^ b = z ^ b := cancel hy0 hz0 (sub_eq_zero.mp hE)
    right
    rw [Nat.add_sub_cancel]
    by_contra hlt
    rw [not_le] at hlt
    have hyz' : y = -z := eq_neg_of_pow_eq hn hy hz hyz hb hlt
    have hya : y ^ (b + 1) = -z ^ (b + 1) := by
      rw [pow_succ, hb, hyz']; ring
    rw [hya, hyz'] at hcol
    have hxz' : z * x ^ (b + 1) = x * z ^ (b + 1) := by linear_combination hcol / 2
    have hxb : x ^ b = z ^ b := cancel hx0 hz0 hxz'
    have hx' : x = -z := eq_neg_of_pow_eq hn hx hz hxz hxb hlt
    exact hxy (hx'.trans hyz'.symm)

/-- T2. Over `ℂ` the law is exact. -/
theorem zeroBad_complex_iff {n a : ℕ} (hn : 0 < n) : ZeroBad ℂ n a ↔ Law n a :=
  ⟨law_of_zeroBad_complex hn,
    zeroBad_of_law hn (Complex.isPrimitiveRoot_exp n hn.ne')⟩

#print axioms zeroBad_of_law
#print axioms zeroBad_complex_iff

end ProximityPrize.T3CeilingColumnZeroLaw
