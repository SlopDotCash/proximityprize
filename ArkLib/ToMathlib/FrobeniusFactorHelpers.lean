/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Frobenius / `p`-power factor helpers (BCIKS20 Appendix A/C)

This file collects clean, kernel-checked helper lemmas about the characteristic-`p`
factor structure that appears in the Guruswami–Sudan / proximity-gap analysis of
BCIKS20 ("Proximity Gaps for Reed–Solomon Codes", Appendix A/C). There, a list-decoding
factor of the form
$$ R(X, Y^{p^f}, Z) = (Y - P(X, Z))^{p^f} $$
shows up, and one needs to extract the "honest" factor `Y - P` out of a known
`p^f`-power. Over a field `K` of characteristic `p` the relevant algebra is the
interplay between:

* the *Frobenius freshman's dream* `(a - b)^(p^f) = a^(p^f) - b^(p^f)`
  (`sub_pow_expChar_pow` / `sub_pow_char_pow`), and
* `Polynomial.expand K (p^f)`, the `p^f`-fold expansion `X ↦ X^(p^f)`, which is the
  inverse-image of the Frobenius on polynomials
  (`Polynomial.map_iterateFrobenius_expand`).

We package these into one-dimensional statements over `K[Y]` (the "`Y`" variable),
keeping `P` a *constant* in `Y` (a coefficient drawn from `K`), which is exactly the
shape that occurs after specializing `X, Z` in the BCIKS factor.

All lemmas are genuine, true combinations; `#print axioms` at the end pins the axiom
footprint to `[propext, Classical.choice, Quot.sound]`.

## Main statements

* `ArkLib.sub_C_pow_expChar_pow` : `(X - C a)^(p^f) = X^(p^f) - C (a^(p^f))` in `K[X]`.
* `ArkLib.expand_X_sub_C` : `expand K (p^f) (X - C a) = X^(p^f) - C a`.
* `ArkLib.X_sub_C_pow_expChar_pow_eq_map_expand` :
  `(X - C a)^(p^f) = (expand K (p^f) (X - C a)).map (iterateFrobenius K p f)`.
* `ArkLib.roots_X_sub_C_pow` : the multiset of roots of `(X - C a)^n` is `n • {a}`.
* `ArkLib.X_sub_C_pow_factor_roots` : a `p^f`-power factor `(X - C a)^(p^f)` has its
  unique root at `a` with multiplicity `p^f`.
* `ArkLib.separable_X_sub_C_pow_iff` / `ArkLib.not_separable_X_sub_C_pow` :
  `(X - C a)^n` is separable iff `n = 1`; in particular never separable for `n ≥ 2`.
* `ArkLib.eq_of_X_sub_C_pow_eq` : injectivity of the honest factor — if
  `(X - C a)^(p^f) = (X - C b)^(p^f)` (with `p^f ≠ 0`), then `a = b`.
-/

namespace ArkLib

open Polynomial

/-! ### Frobenius freshman's dream on the linear factor `X - C a`. -/

section ExpChar

variable {K : Type*} [CommRing K] (p f : ℕ) [ExpChar K p]

/-- Freshman's dream for the linear factor: in characteristic `p`,
`(X - C a)^(p^f) = X^(p^f) - C (a^(p^f))`. This is the polynomial form of the
identity that turns the BCIKS factor `(Y - P)^(p^f)` into a `p^f`-expanded shape. -/
theorem sub_C_pow_expChar_pow (a : K) :
    (X - C a) ^ p ^ f = X ^ p ^ f - C (a ^ p ^ f) := by
  rw [sub_pow_expChar_pow, ← C_pow]

omit [ExpChar K p] in
/-- `expand` of a linear factor: `expand K (p^f) (X - C a) = X^(p^f) - C a`.
Note this holds over any commutative semiring (no characteristic hypothesis needed);
it is the "untwisted" companion of `sub_C_pow_expChar_pow`. -/
theorem expand_X_sub_C (a : K) :
    expand K (p ^ f) (X - C a) = X ^ p ^ f - C a := by
  rw [map_sub, expand_X, expand_C]

/-- The Frobenius/`expand` bridge specialised to the linear factor: applying the
iterated Frobenius coefficient-wise to the `p^f`-expansion of `X - C a` recovers the
`p^f`-power `(X - C a)^(p^f)`. This is `Polynomial.map_iterateFrobenius_expand`
phrased for the honest factor and is the precise statement that "the `p^f`-power
factor is the Frobenius image of an expanded factor". -/
theorem X_sub_C_pow_expChar_pow_eq_map_expand (a : K) :
    (X - C a) ^ p ^ f
      = (expand K (p ^ f) (X - C a)).map (iterateFrobenius K p f) := by
  rw [map_iterateFrobenius_expand]

end ExpChar

/-! ### Root structure of a `p^f`-power factor. -/

section Roots

variable {K : Type*} [CommRing K] [IsDomain K]

/-- The roots (with multiplicity) of `(X - C a)^n` form the multiset `n • {a}`. -/
@[simp]
theorem roots_X_sub_C_pow (a : K) (n : ℕ) :
    ((X - C a) ^ n).roots = n • ({a} : Multiset K) := by
  rw [roots_pow, roots_X_sub_C]

/-- A `p^f`-power factor `(X - C a)^(p^f)` has its unique root at `a`, with
multiplicity exactly `p^f`. Over a domain this is the precise sense in which the
honest value `a` (`= P` in the BCIKS factor `(Y - P)^(p^f)`) is read off from the
factor. -/
theorem X_sub_C_pow_factor_roots {p f : ℕ} [ExpChar K p] (a : K) :
    ((X - C a) ^ p ^ f).roots = (p ^ f) • ({a} : Multiset K) :=
  roots_X_sub_C_pow a (p ^ f)

/-- The root multiplicity of `a` in the `p^f`-power factor is exactly `p^f`. -/
theorem rootMultiplicity_X_sub_C_pow [DecidableEq K] (a : K) (n : ℕ) :
    rootMultiplicity a ((X - C a) ^ n) = n := by
  classical
  rw [← count_roots, roots_X_sub_C_pow, Multiset.count_nsmul, Multiset.count_singleton_self,
    mul_one]

end Roots

/-! ### Separability: extracting `f = 0` (i.e. multiplicity one). -/

section Separable

variable {K : Type*} [CommRing K]

/-- `(X - C a)^n` is separable iff `n = 1`. (`n = 0` gives `1`, which *is* separable,
but the `↔` is for `n` ranging over the "factor" exponents that occur; we phrase the
clean directional facts separately below.) -/
theorem separable_X_sub_C_pow_iff [Nontrivial K] {a : K} {n : ℕ} (hn : n ≠ 0) :
    ((X - C a) ^ n).Separable ↔ n = 1 := by
  constructor
  · intro h
    exact (h.of_pow (not_isUnit_X_sub_C a) hn).2
  · rintro rfl
    simpa using (separable_X_sub_C : (X - C a).Separable)

/-- For `n ≥ 2` (the genuinely-repeated case, e.g. `n = p^f` with `f > 0`),
`(X - C a)^n` is *not* separable. This is the obstruction that distinguishes a true
`p^f`-power factor from the honest linear factor. -/
theorem not_separable_X_sub_C_pow [Nontrivial K] {a : K} {n : ℕ} (hn : 2 ≤ n) :
    ¬ ((X - C a) ^ n).Separable := by
  intro h
  have hn0 : n ≠ 0 := by omega
  have : n = 1 := (separable_X_sub_C_pow_iff hn0).1 h
  omega

end Separable

/-! ### Char-`p` specialization: a genuine `p^f`-power factor is non-separable.

The exponential characteristic `p` of a field can be `1` (when the field has
characteristic zero), in which case `p^f = 1` for all `f` and the factor is always the
honest separable `X - C a`. So the genuinely interesting statements require *prime*
exponential characteristic, i.e. true positive characteristic. We state both: a
characteristic-free `iff` in terms of `p^f` directly (always true), and the
specialization to prime `p` where `p^f = 1 ↔ f = 0`. -/

section CharP

variable {K : Type*} [Field K]

/-- The `p^f`-expanded power `(X - C a)^(p^f)` is separable iff its exponent is `1`.
This is the characteristic-free, always-true core. -/
theorem separable_X_sub_C_expChar_pow_iff (p f : ℕ) [ExpChar K p] (a : K) :
    ((X - C a) ^ p ^ f).Separable ↔ p ^ f = 1 :=
  separable_X_sub_C_pow_iff (pow_ne_zero f (expChar_pos K p).ne')

/-- In genuine prime (exponential) characteristic `p`, the `p^f`-power factor
`(X - C a)^(p^f)` is separable iff `f = 0`. Equivalently (via `sub_C_pow_expChar_pow`)
`X^(p^f) - C (a^(p^f))` is separable iff `f = 0`: an *inseparable* factor signals a
non-trivial Frobenius twist `f > 0`. -/
theorem separable_X_sub_C_prime_pow_iff (p f : ℕ) [ExpChar K p] (hp : p.Prime) (a : K) :
    ((X - C a) ^ p ^ f).Separable ↔ f = 0 := by
  rw [separable_X_sub_C_expChar_pow_iff p f a, Nat.pow_eq_one]
  -- `p^f = 1 ↔ p = 1 ∨ f = 0`; for a prime `p`, only `f = 0`.
  simp [hp.ne_one]

/-- For a genuine Frobenius twist `f > 0` in prime characteristic, the `p^f`-power
factor is *not* separable: this is the obstruction distinguishing a true `p^f`-power
factor from the honest linear factor `X - C a`. -/
theorem not_separable_X_sub_C_prime_pow (p f : ℕ) [ExpChar K p] (hp : p.Prime)
    (hf : f ≠ 0) (a : K) : ¬ ((X - C a) ^ p ^ f).Separable := by
  rw [separable_X_sub_C_prime_pow_iff p f hp a]; exact hf

end CharP

/-! ### Injectivity of the honest factor. -/

section Inj

variable {K : Type*} [CommRing K] [IsDomain K]

/-- If two `p^f`-power factors agree, `(X - C a)^(p^f) = (X - C b)^(p^f)` with the
exponent `p^f` nonzero, then their honest values agree: `a = b`. This says the map
`a ↦ (X - C a)^(p^f)` is injective, so the value `P` in the BCIKS factor `(Y - P)^(p^f)`
is uniquely determined by the factor. -/
theorem eq_of_X_sub_C_pow_eq {p f : ℕ} [ExpChar K p]
    {a b : K} (h : (X - C a) ^ p ^ f = (X - C b) ^ p ^ f) : a = b := by
  classical
  have hroots : ((X - C a) ^ p ^ f).roots = ((X - C b) ^ p ^ f).roots := by rw [h]
  rw [roots_X_sub_C_pow, roots_X_sub_C_pow] at hroots
  have hne : (p ^ f : ℕ) ≠ 0 := pow_ne_zero f (expChar_pos K p).ne'
  -- Compare the (nonempty) supports of `p^f • {a}` and `p^f • {b}`.
  have ha : a ∈ (p ^ f) • ({a} : Multiset K) :=
    (Multiset.mem_nsmul (a := a)).2 ⟨hne, Multiset.mem_singleton_self a⟩
  rw [hroots] at ha
  rw [Multiset.mem_nsmul, Multiset.mem_singleton] at ha
  exact ha.2

end Inj

end ArkLib

#print axioms ArkLib.sub_C_pow_expChar_pow
#print axioms ArkLib.expand_X_sub_C
#print axioms ArkLib.X_sub_C_pow_expChar_pow_eq_map_expand
#print axioms ArkLib.roots_X_sub_C_pow
#print axioms ArkLib.X_sub_C_pow_factor_roots
#print axioms ArkLib.rootMultiplicity_X_sub_C_pow
#print axioms ArkLib.separable_X_sub_C_pow_iff
#print axioms ArkLib.not_separable_X_sub_C_pow
#print axioms ArkLib.separable_X_sub_C_expChar_pow_iff
#print axioms ArkLib.separable_X_sub_C_prime_pow_iff
#print axioms ArkLib.not_separable_X_sub_C_prime_pow
#print axioms ArkLib.eq_of_X_sub_C_pow_eq
