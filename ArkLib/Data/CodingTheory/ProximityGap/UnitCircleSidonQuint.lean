/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UnitCircleSidonQuadWrapper

/-!
# `μ_n` is `B_5`-Sidon under the symmetric-function lift (#444, §0) — the 5-element rung

The `B_h`-Sidon depth ladder for `μ_n` has been built up to the 4-element rung:
`unitCircle_sidon` (2), `unitCircle_sidon_triple` (3), `unitCircle_sidon_quad` (4).  This file
lands the **5-element rung**, the analogue of `unitCircle_sidon_quad`, and it is *cleaner* than the
4-element case: the wrapper hypothesizes only **`e₁, e₂, e₅`** (sum, `e₂`, product), because for
roots of unity BOTH missing middle symmetric functions come free from conjugation —
`e₃ = e₅·conj(e₂)` and `e₄ = e₅·conj(e₁)`.

**The probe-established picture** (`scripts/probes/probe_b5_quint_wrapper.py`,
`scripts/probes/probe_b5_e125_check.py`, exact ℂ roots of unity, `n = 5,6,8,10,12,16`):

* `μ_n` is **NOT** `B_5`-additive-Sidon from the sum alone: equal `e₁` does not force the quintuple
  (collisions `161/252` at `n=6`, `336/792` at `n=8`, …).  This brick does *not* assert it.
* Fixing **`(e₁, e₂, e₅)`** forces the unordered quintuple — **zero** collisions across
  `n = 8,12,16` — because both of the remaining symmetric functions are conjugation-recoverable:

  > `conj(e₁) = e₄/e₅`  (so `e₄ = e₅·conj(e₁)`, error `< 2e-15`) and
  > `conj(e₂) = e₃/e₅`  (so `e₃ = e₅·conj(e₂)`, error `< 5e-15`).

  Fixing only `(e₁, e₅)` (bare sum + product) is **not** enough (collisions `48/468/448` at
  `n = 8,12,16`): the `e₂` hypothesis is genuinely needed.  This matches the reciprocal pattern
  `conj(eₖ) = e_{5-k}/e₅`: `e₁ ↔ e₄` and `e₂ ↔ e₃` are conjugate-paired, leaving the lone
  self-unpaired datum `e₂` (equivalently `e₃`) to be supplied, plus the anchors `e₁, e₅`.

**The theorems (all axiom-clean).**

* `quint_root_mem_of_esymm_eq` — the **char-free root-membership core** (integral domain): equal
  `e₁,…,e₅` force `a ∈ {a',b',c',d',e'}`.  `a` is a root of the common monic quintic, so
  `(a-a')(a-b')(a-c')(a-d')(a-e') = 0` (one `linear_combination`).
* `quintuple_eq_of_esymm_eq` — the **full multiset core**: equal `e₁,…,e₅` force equal unordered
  quintuples.  Pins `a` via root-membership, then discharges the leftover unordered quadruple
  `{b,c,d,e}` against the remaining primed quadruple via `quadruple_eq_of_esymm_eq` (the leftover
  `e₁,…,e₄` recovered by `linear_combination`, with the `a = 0` branch handled by the leftover `e₄`
  identity, exactly as the 3/4-element cores handled their `a = 0` branches).
* `esymm4_eq_conj_esymm1_mul_esymm5`, `esymm3_eq_conj_esymm2_mul_esymm5` — the two reciprocal
  identities for roots of unity (`conj = inverse`).
* `unitCircle_sidon_quint` (headline) — the **roots-of-unity wrapper**: equal `e₁`, `e₂`, `e₅`
  force the unordered quintuple.  Both `e₃` and `e₄` come free from the conjugation identities.

**Honest scope.**  NOT a CORE closure, NOT a refutation.  A structural Sidon-depth brick — the
5-element rung of the `B_h` ladder for `μ_n` — extending the proven 4-element
`unitCircle_sidon_quad`/`quadruple_eq_of_esymm_eq`.  It is **thinness/roots-of-unity-essential**
(the `e₃,e₄`-from-`e₁,e₂` steps use `conj = inverse`, i.e. `|x| = 1`; false for generic field
elements).  No capacity / beyond-Johnson / growth-law claim (ASYMPTOTIC GUARD untouched); the open
core is still bootstrapping the depth-`ℓ` Sidon structure to the full sup-norm bound — this advances
the depth `ℓ` to 5.  NON-MOMENT (pure symmetric-function / integral-domain algebra + conjugation).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Complex

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- `UnorderedQuadEq (a,b,c,d) (a',b',c',d')` : the unordered quadruples coincide.  This is exactly
the conclusion of `quadruple_eq_of_esymm_eq` (root `a` matches one of the primed roots, and the
leftover triple matches), packaged so the 5-element multiset core can state its leftover-quadruple
conclusion compactly. -/
def UnorderedQuadEq {R : Type*} (t t' : R × R × R × R) : Prop :=
  (t.1 = t'.1 ∧ UnorderedTripleEq (t.2.1, t.2.2.1, t.2.2.2) (t'.2.1, t'.2.2.1, t'.2.2.2)) ∨
  (t.1 = t'.2.1 ∧ UnorderedTripleEq (t.2.1, t.2.2.1, t.2.2.2) (t'.1, t'.2.2.1, t'.2.2.2)) ∨
  (t.1 = t'.2.2.1 ∧ UnorderedTripleEq (t.2.1, t.2.2.1, t.2.2.2) (t'.1, t'.2.1, t'.2.2.2)) ∨
  (t.1 = t'.2.2.2 ∧ UnorderedTripleEq (t.2.1, t.2.2.1, t.2.2.2) (t'.1, t'.2.1, t'.2.2.1))

/-- `quadruple_eq_of_esymm_eq` repackaged into `UnorderedQuadEq`. -/
theorem unorderedQuadEq_of_esymm_eq {R : Type*} [CommRing R] [IsDomain R]
    {a b c d a' b' c' d' : R}
    (h1 : a + b + c + d = a' + b' + c' + d')
    (h2 : a * b + a * c + a * d + b * c + b * d + c * d
        = a' * b' + a' * c' + a' * d' + b' * c' + b' * d' + c' * d')
    (h3 : a * b * c + a * b * d + a * c * d + b * c * d
        = a' * b' * c' + a' * b' * d' + a' * c' * d' + b' * c' * d')
    (h4 : a * b * c * d = a' * b' * c' * d') :
    UnorderedQuadEq (a, b, c, d) (a', b', c', d') :=
  quadruple_eq_of_esymm_eq h1 h2 h3 h4

/-- **The algebraic `5`-element Sidon core (root membership).**  In an integral domain, if two
quintuples have equal elementary symmetric functions `e₁,…,e₅`, then `a` is one of
`a', b', c', d', e'`.  Mechanism: `a` is a root of the common monic quintic, so
`(a-a')(a-b')(a-c')(a-d')(a-e') = 0`. -/
theorem quint_root_mem_of_esymm_eq {R : Type*} [CommRing R] [IsDomain R]
    {a b c d e a' b' c' d' e' : R}
    (h1 : a + b + c + d + e = a' + b' + c' + d' + e')
    (h2 : a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e
        = a'*b' + a'*c' + a'*d' + a'*e' + b'*c' + b'*d' + b'*e' + c'*d' + c'*e' + d'*e')
    (h3 : a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e + b*c*d + b*c*e + b*d*e + c*d*e
        = a'*b'*c' + a'*b'*d' + a'*b'*e' + a'*c'*d' + a'*c'*e' + a'*d'*e'
          + b'*c'*d' + b'*c'*e' + b'*d'*e' + c'*d'*e')
    (h4 : a*b*c*d + a*b*c*e + a*b*d*e + a*c*d*e + b*c*d*e
        = a'*b'*c'*d' + a'*b'*c'*e' + a'*b'*d'*e' + a'*c'*d'*e' + b'*c'*d'*e')
    (h5 : a*b*c*d*e = a'*b'*c'*d'*e') :
    a = a' ∨ a = b' ∨ a = c' ∨ a = d' ∨ a = e' := by
  -- `a` is a root of `∏ (X - x') = ∏ (X - x)` (equal coeffs), so the product below vanishes.
  have key : (a - a') * (a - b') * (a - c') * (a - d') * (a - e') = 0 := by
    linear_combination (a*a*a*a) * h1 - (a*a*a) * h2 + (a*a) * h3 - a * h4 + h5
  rcases mul_eq_zero.mp key with h | he'
  · rcases mul_eq_zero.mp h with h' | hd'
    · rcases mul_eq_zero.mp h' with h'' | hc'
      · rcases mul_eq_zero.mp h'' with ha' | hb'
        · exact Or.inl (by linear_combination ha')
        · exact Or.inr (Or.inl (by linear_combination hb'))
      · exact Or.inr (Or.inr (Or.inl (by linear_combination hc')))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination hd'))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by linear_combination he'))))

/-- **The symmetric leftover-quadruple lemma.**  If the five quintuple elementary symmetric
functions of `(a,b,c,d,e)` equal those of `(w,p,q,r,s)` (in this fixed order — the caller reorders
the primed tuple to put the matched root `w` first) and `a = w`, then the leftover unordered
quadruple `{b,c,d,e}` equals `{p,q,r,s}`.  Handles the `w = 0` branch (where the product identity
alone cannot cancel `a`) via the leftover `e₄` identity, exactly as the 3/4-element cores handled
their `a = 0` branches. -/
private theorem leftover_quad {R : Type*} [CommRing R] [IsDomain R]
    {a b c d e w p q r s : R}
    (h1 : a + b + c + d + e = w + p + q + r + s)
    (h2 : a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e
        = w*p + w*q + w*r + w*s + p*q + p*r + p*s + q*r + q*s + r*s)
    (h3 : a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e + b*c*d + b*c*e + b*d*e + c*d*e
        = w*p*q + w*p*r + w*p*s + w*q*r + w*q*s + w*r*s + p*q*r + p*q*s + p*r*s + q*r*s)
    (h4 : a*b*c*d + a*b*c*e + a*b*d*e + a*c*d*e + b*c*d*e
        = w*p*q*r + w*p*q*s + w*p*r*s + w*q*r*s + p*q*r*s)
    (h5 : a*b*c*d*e = w*p*q*r*s)
    (ha : a = w) :
    UnorderedQuadEq (b, c, d, e) (p, q, r, s) := by
  subst ha
  -- leftover e₁ (of {b,c,d,e}) from the quintuple e₁ by cancelling a.
  have hs : b + c + d + e = p + q + r + s := by linear_combination h1
  -- leftover e₂ from quintuple e₂ by subtracting a·(leftover e₁).
  have he2 : b*c + b*d + b*e + c*d + c*e + d*e = p*q + p*r + p*s + q*r + q*s + r*s := by
    linear_combination h2 - a * hs
  -- leftover e₃ from quintuple e₃ by subtracting a·(leftover e₂).
  have he3 : b*c*d + b*c*e + b*d*e + c*d*e = p*q*r + p*q*s + p*r*s + q*r*s := by
    linear_combination h3 - a * he2
  -- leftover e₄ (= product of {b,c,d,e}) from quintuple e₅ by cancelling a (a ≠ 0 branch),
  -- or directly from quintuple e₄ when a = 0.
  have he4 : b*c*d*e = p*q*r*s := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · have e4 := h4
      rw [ha0] at e4
      linear_combination e4
    · have hprodA : a * (b*c*d*e) = a * (p*q*r*s) := by linear_combination h5
      exact mul_left_cancel₀ ha0 hprodA
  exact unorderedQuadEq_of_esymm_eq hs he2 he3 he4

/-- **The full char-free `5`-element Sidon core.**  In an integral domain, two unordered quintuples
with equal `e₁,…,e₅` coincide as unordered quintuples: `a` equals one of `a',b',c',d',e'`, and after
removing that match the leftover unordered quadruple `{b,c,d,e}` equals the remaining primed
quadruple.  Composes `quint_root_mem_of_esymm_eq` (root membership) with the leftover-quadruple
reduction. -/
theorem quintuple_eq_of_esymm_eq {R : Type*} [CommRing R] [IsDomain R]
    {a b c d e a' b' c' d' e' : R}
    (h1 : a + b + c + d + e = a' + b' + c' + d' + e')
    (h2 : a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e
        = a'*b' + a'*c' + a'*d' + a'*e' + b'*c' + b'*d' + b'*e' + c'*d' + c'*e' + d'*e')
    (h3 : a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e + b*c*d + b*c*e + b*d*e + c*d*e
        = a'*b'*c' + a'*b'*d' + a'*b'*e' + a'*c'*d' + a'*c'*e' + a'*d'*e'
          + b'*c'*d' + b'*c'*e' + b'*d'*e' + c'*d'*e')
    (h4 : a*b*c*d + a*b*c*e + a*b*d*e + a*c*d*e + b*c*d*e
        = a'*b'*c'*d' + a'*b'*c'*e' + a'*b'*d'*e' + a'*c'*d'*e' + b'*c'*d'*e')
    (h5 : a*b*c*d*e = a'*b'*c'*d'*e') :
    (a = a' ∧ UnorderedQuadEq (b, c, d, e) (b', c', d', e')) ∨
    (a = b' ∧ UnorderedQuadEq (b, c, d, e) (a', c', d', e')) ∨
    (a = c' ∧ UnorderedQuadEq (b, c, d, e) (a', b', d', e')) ∨
    (a = d' ∧ UnorderedQuadEq (b, c, d, e) (a', b', c', e')) ∨
    (a = e' ∧ UnorderedQuadEq (b, c, d, e) (a', b', c', d')) := by
  rcases quint_root_mem_of_esymm_eq h1 h2 h3 h4 h5 with ha | ha | ha | ha | ha
  · exact Or.inl ⟨ha, leftover_quad
      (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4) (by linear_combination h5) ha⟩
  · exact Or.inr (Or.inl ⟨ha, leftover_quad
      (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4) (by linear_combination h5) ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ha, leftover_quad
      (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4) (by linear_combination h5) ha⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, leftover_quad
      (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4) (by linear_combination h5) ha⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, leftover_quad
      (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4) (by linear_combination h5) ha⟩)))

/-- **Reciprocal identity `e₄ = e₅·conj(e₁)` for root-of-unity quintuples.**  For `n`-th roots of
unity, `conj(e₁)·e₅ = e₄` (`conj x = x⁻¹` on `|x| = 1`, so `conj(e₁) = e₄/e₅`). -/
theorem esymm4_eq_conj_esymm1_mul_esymm5 {n : ℕ} (hn : n ≠ 0) {a b c d e : ℂ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1) (hd : d ^ n = 1) (he : e ^ n = 1) :
    (starRingEnd ℂ) (a + b + c + d + e) * (a * b * c * d * e)
      = a*b*c*d + a*b*c*e + a*b*d*e + a*c*d*e + b*c*d*e := by
  have ha0 : a ≠ 0 := fun h => by rw [h, zero_pow hn] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := fun h => by rw [h, zero_pow hn] at hb; exact zero_ne_one hb
  have hc0 : c ≠ 0 := fun h => by rw [h, zero_pow hn] at hc; exact zero_ne_one hc
  have hd0 : d ≠ 0 := fun h => by rw [h, zero_pow hn] at hd; exact zero_ne_one hd
  have he0 : e ≠ 0 := fun h => by rw [h, zero_pow hn] at he; exact zero_ne_one he
  have hai : a * (starRingEnd ℂ) a = 1 := mul_conj_eq_one_of_pow_eq_one hn ha
  have hbi : b * (starRingEnd ℂ) b = 1 := mul_conj_eq_one_of_pow_eq_one hn hb
  have hci : c * (starRingEnd ℂ) c = 1 := mul_conj_eq_one_of_pow_eq_one hn hc
  have hdi : d * (starRingEnd ℂ) d = 1 := mul_conj_eq_one_of_pow_eq_one hn hd
  have hei : e * (starRingEnd ℂ) e = 1 := mul_conj_eq_one_of_pow_eq_one hn he
  have hcA : (starRingEnd ℂ) a = a⁻¹ := by field_simp; linear_combination hai
  have hcB : (starRingEnd ℂ) b = b⁻¹ := by field_simp; linear_combination hbi
  have hcC : (starRingEnd ℂ) c = c⁻¹ := by field_simp; linear_combination hci
  have hcD : (starRingEnd ℂ) d = d⁻¹ := by field_simp; linear_combination hdi
  have hcE : (starRingEnd ℂ) e = e⁻¹ := by field_simp; linear_combination hei
  rw [map_add, map_add, map_add, map_add, hcA, hcB, hcC, hcD, hcE]
  field_simp
  ring

/-- **Reciprocal identity `e₃ = e₅·conj(e₂)` for root-of-unity quintuples.**  For `n`-th roots of
unity, `conj(e₂)·e₅ = e₃` (`conj(e₂) = e₃/e₅` on `|x| = 1`). -/
theorem esymm3_eq_conj_esymm2_mul_esymm5 {n : ℕ} (hn : n ≠ 0) {a b c d e : ℂ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1) (hd : d ^ n = 1) (he : e ^ n = 1) :
    (starRingEnd ℂ) (a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e)
        * (a * b * c * d * e)
      = a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e + b*c*d + b*c*e + b*d*e + c*d*e := by
  have ha0 : a ≠ 0 := fun h => by rw [h, zero_pow hn] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := fun h => by rw [h, zero_pow hn] at hb; exact zero_ne_one hb
  have hc0 : c ≠ 0 := fun h => by rw [h, zero_pow hn] at hc; exact zero_ne_one hc
  have hd0 : d ≠ 0 := fun h => by rw [h, zero_pow hn] at hd; exact zero_ne_one hd
  have he0 : e ≠ 0 := fun h => by rw [h, zero_pow hn] at he; exact zero_ne_one he
  have hai : a * (starRingEnd ℂ) a = 1 := mul_conj_eq_one_of_pow_eq_one hn ha
  have hbi : b * (starRingEnd ℂ) b = 1 := mul_conj_eq_one_of_pow_eq_one hn hb
  have hci : c * (starRingEnd ℂ) c = 1 := mul_conj_eq_one_of_pow_eq_one hn hc
  have hdi : d * (starRingEnd ℂ) d = 1 := mul_conj_eq_one_of_pow_eq_one hn hd
  have hei : e * (starRingEnd ℂ) e = 1 := mul_conj_eq_one_of_pow_eq_one hn he
  have hcA : (starRingEnd ℂ) a = a⁻¹ := by field_simp; linear_combination hai
  have hcB : (starRingEnd ℂ) b = b⁻¹ := by field_simp; linear_combination hbi
  have hcC : (starRingEnd ℂ) c = c⁻¹ := by field_simp; linear_combination hci
  have hcD : (starRingEnd ℂ) d = d⁻¹ := by field_simp; linear_combination hdi
  have hcE : (starRingEnd ℂ) e = e⁻¹ := by field_simp; linear_combination hei
  rw [map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add,
    map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
    hcA, hcB, hcC, hcD, hcE]
  field_simp
  ring

/-- **`μ_n` IS `B_5`-SIDON UNDER THE SYMMETRIC-FUNCTION LIFT.**  For `n`-th roots of unity
`a,b,c,d,e,a',b',c',d',e'` with equal sum `e₁`, equal `e₂`, and equal product `e₅`, the unordered
quintuples coincide.  Both missing symmetric functions are recovered for free from conjugation:
`e₄ = e₅·conj(e₁)` and `e₃ = e₅·conj(e₂)`.  This is the full 5-element rung, the analogue of
`unitCircle_sidon_quad` — and cleaner, requiring only three of the five symmetric functions. -/
theorem unitCircle_sidon_quint {n : ℕ} (hn : n ≠ 0) {a b c d e a' b' c' d' e' : ℂ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1) (hd : d ^ n = 1) (he : e ^ n = 1)
    (ha' : a' ^ n = 1) (hb' : b' ^ n = 1) (hc' : c' ^ n = 1) (hd' : d' ^ n = 1) (he' : e' ^ n = 1)
    (hsum : a + b + c + d + e = a' + b' + c' + d' + e')
    (he2 : a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e
         = a'*b' + a'*c' + a'*d' + a'*e' + b'*c' + b'*d' + b'*e' + c'*d' + c'*e' + d'*e')
    (hprod : a * b * c * d * e = a' * b' * c' * d' * e') :
    (a = a' ∧ UnorderedQuadEq (b, c, d, e) (b', c', d', e')) ∨
    (a = b' ∧ UnorderedQuadEq (b, c, d, e) (a', c', d', e')) ∨
    (a = c' ∧ UnorderedQuadEq (b, c, d, e) (a', b', d', e')) ∨
    (a = d' ∧ UnorderedQuadEq (b, c, d, e) (a', b', c', e')) ∨
    (a = e' ∧ UnorderedQuadEq (b, c, d, e) (a', b', c', d')) := by
  -- `e₄` from `e₁, e₅` and `e₃` from `e₂, e₅`, on both sides, via conjugation.
  have h4L : (starRingEnd ℂ) (a + b + c + d + e) * (a * b * c * d * e)
      = a*b*c*d + a*b*c*e + a*b*d*e + a*c*d*e + b*c*d*e :=
    esymm4_eq_conj_esymm1_mul_esymm5 hn ha hb hc hd he
  have h4R : (starRingEnd ℂ) (a' + b' + c' + d' + e') * (a' * b' * c' * d' * e')
      = a'*b'*c'*d' + a'*b'*c'*e' + a'*b'*d'*e' + a'*c'*d'*e' + b'*c'*d'*e' :=
    esymm4_eq_conj_esymm1_mul_esymm5 hn ha' hb' hc' hd' he'
  have h4 : a*b*c*d + a*b*c*e + a*b*d*e + a*c*d*e + b*c*d*e
      = a'*b'*c'*d' + a'*b'*c'*e' + a'*b'*d'*e' + a'*c'*d'*e' + b'*c'*d'*e' := by
    rw [← h4L, ← h4R, hsum, hprod]
  have h3L : (starRingEnd ℂ) (a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e)
        * (a * b * c * d * e)
      = a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e + b*c*d + b*c*e + b*d*e + c*d*e :=
    esymm3_eq_conj_esymm2_mul_esymm5 hn ha hb hc hd he
  have h3R : (starRingEnd ℂ)
        (a'*b' + a'*c' + a'*d' + a'*e' + b'*c' + b'*d' + b'*e' + c'*d' + c'*e' + d'*e')
        * (a' * b' * c' * d' * e')
      = a'*b'*c' + a'*b'*d' + a'*b'*e' + a'*c'*d' + a'*c'*e' + a'*d'*e'
        + b'*c'*d' + b'*c'*e' + b'*d'*e' + c'*d'*e' :=
    esymm3_eq_conj_esymm2_mul_esymm5 hn ha' hb' hc' hd' he'
  have h3 : a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e + b*c*d + b*c*e + b*d*e + c*d*e
      = a'*b'*c' + a'*b'*d' + a'*b'*e' + a'*c'*d' + a'*c'*e' + a'*d'*e'
        + b'*c'*d' + b'*c'*e' + b'*d'*e' + c'*d'*e' := by
    rw [← h3L, ← h3R, he2, hprod]
  exact quintuple_eq_of_esymm_eq hsum he2 h3 h4 hprod

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.quint_root_mem_of_esymm_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.quintuple_eq_of_esymm_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.esymm4_eq_conj_esymm1_mul_esymm5
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.esymm3_eq_conj_esymm2_mul_esymm5
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.unitCircle_sidon_quint
