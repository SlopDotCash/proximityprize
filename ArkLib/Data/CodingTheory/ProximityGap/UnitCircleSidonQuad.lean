/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UnitCircleSidonTriple

/-!
# `μ_n` `B_4`-Sidon scaffolding (#444, §0) — the char-free 4-element core + reciprocal identities

`UnitCircleSidonTriple.lean` landed the **3-element** rung of the `B_h`-Sidon depth ladder for
`μ_n`: for `n`-th roots of unity, equal `e₁` (sum) + `e₃` (product) force equal unordered triples,
with `e₂` supplied *for free* by conjugation (`e₂ = conj(e₁)·e₃`).  This file builds the
**4-element scaffolding**.

**The probe-mapped picture** (`scripts/probes/probe_b4_sidon_mun.py`, `probe_b4_e2_mechanism.py`,
`probe_b4_reconcile.py`, `probe_b4_e2_closedform.py`, exact ℂ, `n = 4,8,16`):

* Fixing the sum `e₁` alone does **NOT** force a 4-tuple (collisions `8 / 192 / 3584`).
* Fixing `(e₁, e₄)` (sum + product) forces the 4-tuple **iff `e₁ ≠ 0`**: the only collisions occur
  in the **zero-sum** classes (`1 / 8 / 64`, all with `e₁ = 0`).  Restricted to `e₁ ≠ 0`,
  `(e₁, e₄)` determines `e₂` uniquely (`0` multi-`e₂` classes, `n = 8, 16`) and hence the multiset.
* The conjugation **reciprocal** identities hold exactly (error `< 2e-15`): for roots of unity
  `conj(eₖ) = e_{4-k} / e₄`, i.e. `e₃ = e₄·conj(e₁)`, `e₁ = e₄·conj(e₃)`, and `e₂ = e₄·conj(e₂)`.

So the 4-element rung is genuinely different from the 3-element one: it **requires** `e₁ ≠ 0`
(it fails for zero-sum quadruples, unlike the triple case), and while `e₃` comes free from `e₁`
exactly as before, the determination of `e₂` from `(e₁, e₄)` is **not** a one-line conjugation
substitution (the self-reciprocal `e₂ = e₄·conj(e₂)` is a single underdetermined constraint; `e₂`
is pinned only via the global root structure).  That `e₂`-determination is the **open residual** of
the 4-element wrapper and is left honestly unformalized (no `sorry`, simply not claimed).

**What this file lands (all axiom-clean, real proofs):**

* `quad_root_mem_of_esymm_eq` — the **char-free integral-domain core (root membership)**: equal
  `e₁, e₂, e₃, e₄` force `a ∈ {a', b', c', d'}`.  The 4-element analogue of the first split in
  `triple_eq_of_esymm_eq`: `a` is a root of the common quartic, so `(a-a')(a-b')(a-c')(a-d') = 0`;
  combined with `triple_eq_of_esymm_eq` on the leftover triple this gives full multiset equality.
* `esymm3_eq_conj_esymm1_mul_esymm4` — the clean reciprocal identity `e₃ = e₄·conj(e₁)` for roots
  of unity (`conj = inverse`), the 4-element analogue of `esymm2_eq_conj_esymm1_mul_esymm3`.
* `esymm1_eq_conj_esymm3_mul_esymm4` — the dual reciprocal `e₁ = e₄·conj(e₃)`.

**Honest scope.**  NOT a CORE closure, NOT a refutation, NOT (yet) the full `B_4` wrapper (the
`e₂`-determination is the noted open residual).  Structural Sidon-depth scaffolding for the
4-element rung: the char-free core (field-universal) + the two proven reciprocal identities
(roots-of-unity-essential, `conj = inverse` needs `|x| = 1`).  No capacity / beyond-Johnson /
cliff-at-`n/2` claim (ASYMPTOTIC GUARD untouched).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Complex

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The algebraic `4`-element Sidon core (root membership).**  In an integral domain, if two
quadruples have equal elementary symmetric functions `e₁, e₂, e₃, e₄`, then `a` (any member of the
first) is one of `a', b', c', d'` (a member of the second).  Mechanism: `a` is a root of the common
monic quartic, so `(a-a')(a-b')(a-c')(a-d') = 0`.  Combined with `triple_eq_of_esymm_eq` on the
leftover triple (after removing the matched pair of equal roots), this gives full multiset equality;
stated here as the clean root-membership brick (the 4-element analogue of the first split in
`triple_eq_of_esymm_eq`). -/
theorem quad_root_mem_of_esymm_eq {R : Type*} [CommRing R] [IsDomain R] {a b c d a' b' c' d' : R}
    (h1 : a + b + c + d = a' + b' + c' + d')
    (h2 : a*b + a*c + a*d + b*c + b*d + c*d = a'*b' + a'*c' + a'*d' + b'*c' + b'*d' + c'*d')
    (h3 : a*b*c + a*b*d + a*c*d + b*c*d = a'*b'*c' + a'*b'*d' + a'*c'*d' + b'*c'*d')
    (h4 : a*b*c*d = a'*b'*c'*d') :
    a = a' ∨ a = b' ∨ a = c' ∨ a = d' := by
  -- `a` is a root of `(X-a')(X-b')(X-c')(X-d') = (X-a)(X-b)(X-c)(X-d)` (equal coeffs),
  -- so `(a-a')(a-b')(a-c')(a-d') = 0`.
  have key : (a - a') * (a - b') * (a - c') * (a - d') = 0 := by
    linear_combination (a*a*a) * h1 - (a*a) * h2 + a * h3 - h4
  rcases mul_eq_zero.mp key with h | hd'
  · rcases mul_eq_zero.mp h with h' | hc'
    · rcases mul_eq_zero.mp h' with ha' | hb'
      · exact Or.inl (by linear_combination ha')
      · exact Or.inr (Or.inl (by linear_combination hb'))
    · exact Or.inr (Or.inr (Or.inl (by linear_combination hc')))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination hd')))

/-- **Reciprocal identity `e₃ = e₄·conj(e₁)` for root-of-unity quadruples.**  For `n`-th roots of
unity `a, b, c, d`, `conj(a+b+c+d)·(abcd) = abc + abd + acd + bcd` (`conj x = x⁻¹` on `|x| = 1`, so
`conj(e₁) = e₃/e₄`).  The 4-element analogue of `esymm2_eq_conj_esymm1_mul_esymm3`. -/
theorem esymm3_eq_conj_esymm1_mul_esymm4 {n : ℕ} (hn : n ≠ 0) {a b c d : ℂ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1) (hd : d ^ n = 1) :
    (starRingEnd ℂ) (a + b + c + d) * (a * b * c * d)
      = a*b*c + a*b*d + a*c*d + b*c*d := by
  have ha0 : a ≠ 0 := fun h => by rw [h, zero_pow hn] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := fun h => by rw [h, zero_pow hn] at hb; exact zero_ne_one hb
  have hc0 : c ≠ 0 := fun h => by rw [h, zero_pow hn] at hc; exact zero_ne_one hc
  have hd0 : d ≠ 0 := fun h => by rw [h, zero_pow hn] at hd; exact zero_ne_one hd
  have hai : a * (starRingEnd ℂ) a = 1 := mul_conj_eq_one_of_pow_eq_one hn ha
  have hbi : b * (starRingEnd ℂ) b = 1 := mul_conj_eq_one_of_pow_eq_one hn hb
  have hci : c * (starRingEnd ℂ) c = 1 := mul_conj_eq_one_of_pow_eq_one hn hc
  have hdi : d * (starRingEnd ℂ) d = 1 := mul_conj_eq_one_of_pow_eq_one hn hd
  have hcA : (starRingEnd ℂ) a = a⁻¹ := by field_simp; linear_combination hai
  have hcB : (starRingEnd ℂ) b = b⁻¹ := by field_simp; linear_combination hbi
  have hcC : (starRingEnd ℂ) c = c⁻¹ := by field_simp; linear_combination hci
  have hcD : (starRingEnd ℂ) d = d⁻¹ := by field_simp; linear_combination hdi
  rw [map_add, map_add, map_add, hcA, hcB, hcC, hcD]
  field_simp
  ring

/-- **Dual reciprocal identity `e₁ = e₄·conj(e₃)` for root-of-unity quadruples.**  For `n`-th roots
of unity, `conj(abc + abd + acd + bcd)·(abcd) = a + b + c + d`. -/
theorem esymm1_eq_conj_esymm3_mul_esymm4 {n : ℕ} (hn : n ≠ 0) {a b c d : ℂ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1) (hd : d ^ n = 1) :
    (starRingEnd ℂ) (a*b*c + a*b*d + a*c*d + b*c*d) * (a * b * c * d)
      = a + b + c + d := by
  have ha0 : a ≠ 0 := fun h => by rw [h, zero_pow hn] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := fun h => by rw [h, zero_pow hn] at hb; exact zero_ne_one hb
  have hc0 : c ≠ 0 := fun h => by rw [h, zero_pow hn] at hc; exact zero_ne_one hc
  have hd0 : d ≠ 0 := fun h => by rw [h, zero_pow hn] at hd; exact zero_ne_one hd
  have hai : a * (starRingEnd ℂ) a = 1 := mul_conj_eq_one_of_pow_eq_one hn ha
  have hbi : b * (starRingEnd ℂ) b = 1 := mul_conj_eq_one_of_pow_eq_one hn hb
  have hci : c * (starRingEnd ℂ) c = 1 := mul_conj_eq_one_of_pow_eq_one hn hc
  have hdi : d * (starRingEnd ℂ) d = 1 := mul_conj_eq_one_of_pow_eq_one hn hd
  have hcA : (starRingEnd ℂ) a = a⁻¹ := by field_simp; linear_combination hai
  have hcB : (starRingEnd ℂ) b = b⁻¹ := by field_simp; linear_combination hbi
  have hcC : (starRingEnd ℂ) c = c⁻¹ := by field_simp; linear_combination hci
  have hcD : (starRingEnd ℂ) d = d⁻¹ := by field_simp; linear_combination hdi
  rw [map_add, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
    map_mul, map_mul, hcA, hcB, hcC, hcD]
  field_simp
  ring

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.quad_root_mem_of_esymm_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.esymm3_eq_conj_esymm1_mul_esymm4
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.esymm1_eq_conj_esymm3_mul_esymm4
