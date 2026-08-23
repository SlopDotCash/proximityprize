/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UnitCircleSidon

/-!
# `μ_n` is `B_3`-Sidon under the symmetric-function lift (#444, §0) — the 3-element brick

`unitCircle_sidon` (in `UnitCircleSidon.lean`) is the `2`-element Sidon core: for `n`-th roots of
unity, **equal sum `a+b=c+d` (with the conjugation-derived equal product) forces equal unordered
pairs**.  The §0 "B_∞ ← B_{log n} Sidon bootstrap" lane of the prize asks to push the Sidon depth
of `μ_n` past the `2`-element rung.  This file lands the **`3`-element rung**.

**The probe-established facts** (`scripts/probes/probe_b3_sidon_mun.py`,
`scripts/probes/probe_b3_conj_mechanism.py`).

* `μ_n` is **NOT** `B_3`-additive-Sidon from the sum alone: equal triple-sums
  `a+b+c = a'+b'+c'` do **not** force equal multisets (collisions appear already at `n=4`:
  `4/4`, then `48/48` at `n=8`, `448/448` at `n=16`).  So a naive "equal sum ⟹ equal triple"
  claim is **FALSE** — this brick does *not* assert it.
* But **equal `e₁` (sum) AND `e₃` (product)** force equal multiset, with **zero** collisions
  (`n=4..32`), because for roots of unity (`conj x = x⁻¹`) the conjugate of `e₁` is exactly
  `e₂/e₃`, i.e.

  > **`conj(a+b+c)·(abc) = ab+bc+ca`**     (`esymm2_eq_conj_esymm1_mul_esymm3`, error `< 1e-15`),

  so fixing `e₁` and `e₃` *determines* `e₂`, hence all three elementary symmetric functions, hence
  the monic cubic, hence the unordered triple.

**The two theorems.**

* `triple_eq_of_esymm_eq` — the **char-free algebraic core** (integral domain): equal `e₁, e₂, e₃`
  force equal unordered triples.  Mechanism: `a` is a root of `(X-a')(X-b')(X-c') = (X-a)(X-b)(X-c)`
  (equal coefficients), so `(a-a')(a-b')(a-c') = 0`; a case split places `a ∈ {a',b',c'}` and the
  remaining two reduce to `pair_eq_of_sum_prod_eq`.  This is the 3-element analogue of
  `pair_eq_of_sum_prod_eq`.
* `unitCircle_sidon_triple` — the **roots-of-unity wrapper**: for `n`-th roots of unity with
  `a+b+c = a'+b'+c'` and `abc = a'b'c'`, the unordered triples coincide.  The missing `e₂`
  equality comes *free* from conjugation (`esymm2_eq_conj_esymm1_mul_esymm3`), exactly as the
  `e₂ = ab = cd` step came free in `unitCircle_sidon`.  (Unlike the 2-element case, **no**
  `e₁ ≠ 0` hypothesis is needed: the product `e₃` is given directly, so there is no `a+b ≠ 0`
  cancellation step — the result holds for zero-sum triples too.)

**Honest scope.**  NOT a CORE closure and NOT a refutation.  This is a structural Sidon-depth
brick — the `3`-element rung of the `B_h` ladder for `μ_n` — extending the proven `2`-element
`unitCircle_sidon`.  It is **thinness/roots-of-unity-essential** (the `e₂`-from-`e₁,e₃` step uses
`conj = inverse`, which needs `|x| = 1`; it is false for generic field elements).  It makes no
capacity / beyond-Johnson / growth-law claim (ASYMPTOTIC GUARD untouched); the open core is still
bootstrapping the depth-`ℓ` Sidon structure to the full sup-norm bound.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Complex

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The algebraic `3`-element Sidon core.**  In an integral domain, two unordered triples with
equal elementary symmetric functions `e₁` (sum), `e₂`, and `e₃` (product) coincide as unordered
triples.  This is the 3-element analogue of `pair_eq_of_sum_prod_eq`. -/
theorem triple_eq_of_esymm_eq {R : Type*} [CommRing R] [IsDomain R] {a b c a' b' c' : R}
    (h1 : a + b + c = a' + b' + c')
    (h2 : a * b + b * c + c * a = a' * b' + b' * c' + c' * a')
    (h3 : a * b * c = a' * b' * c') :
    (a = a' ∧ b = b' ∧ c = c') ∨ (a = a' ∧ b = c' ∧ c = b') ∨
    (a = b' ∧ b = a' ∧ c = c') ∨ (a = b' ∧ b = c' ∧ c = a') ∨
    (a = c' ∧ b = a' ∧ c = b') ∨ (a = c' ∧ b = b' ∧ c = a') := by
  -- `a` is a root of `(X - a')(X - b')(X - c')`, evaluated at `X = a`, because the cubic
  -- `(X - a)(X - b)(X - c)` and `(X - a')(X - b')(X - c')` have the same coefficients.
  have key : (a - a') * (a - b') * (a - c') = 0 := by
    linear_combination (a * a) * h1 - a * h2 + h3
  -- a sub-helper: with `a` pinned to one of `{a', b', c'}`, the remaining pair is Sidon via
  -- `pair_eq_of_sum_prod_eq` (equal sum + equal product of the leftover two).
  rcases mul_eq_zero.mp key with h | hc'
  · rcases mul_eq_zero.mp h with ha' | hb'
    · -- a = a'
      have ha : a = a' := by linear_combination ha'
      -- leftover: b + c = b' + c' and b*c = b'*c'
      have hsum : b + c = b' + c' := by linear_combination h1 - ha'
      have hprod : b * c = b' * c' := by
        -- from e₂ and e₃ with a = a'
        have hprodA : a * (b * c) = a' * (b' * c') := by
          have : a * (b * c) = a * b * c := by ring
          rw [this, h3]; ring
        rw [ha] at hprodA
        rcases eq_or_ne a' 0 with ha0 | ha0
        · -- a' = 0 ⟹ a = 0; then e₂ gives b*c = b'*c' directly
          have haa : a = 0 := by rw [ha, ha0]
          have e2 := h2
          rw [haa, ha0] at e2
          linear_combination e2
        · exact mul_left_cancel₀ ha0 hprodA
      rcases pair_eq_of_sum_prod_eq hsum hprod with ⟨hb, hcc⟩ | ⟨hb, hcc⟩
      · exact Or.inl ⟨ha, hb, hcc⟩
      · exact Or.inr (Or.inl ⟨ha, hb, hcc⟩)
    · -- a = b'
      have ha : a = b' := by linear_combination hb'
      have hsum : b + c = a' + c' := by linear_combination h1 - hb'
      have hprod : b * c = a' * c' := by
        have hprodA : a * (b * c) = b' * (a' * c') := by
          have : a * (b * c) = a * b * c := by ring
          rw [this, h3]; ring
        rw [ha] at hprodA
        rcases eq_or_ne b' 0 with hb0 | hb0
        · have haa : a = 0 := by rw [ha, hb0]
          have e2 := h2
          rw [haa, hb0] at e2
          linear_combination e2
        · exact mul_left_cancel₀ hb0 hprodA
      rcases pair_eq_of_sum_prod_eq hsum hprod with ⟨hb, hcc⟩ | ⟨hb, hcc⟩
      · exact Or.inr (Or.inr (Or.inl ⟨ha, hb, hcc⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hb, hcc⟩)))
  · -- a = c'
    have ha : a = c' := by linear_combination hc'
    have hsum : b + c = a' + b' := by linear_combination h1 - hc'
    have hprod : b * c = a' * b' := by
      have hprodA : a * (b * c) = c' * (a' * b') := by
        have : a * (b * c) = a * b * c := by ring
        rw [this, h3]; ring
      rw [ha] at hprodA
      rcases eq_or_ne c' 0 with hc0 | hc0
      · have haa : a = 0 := by rw [ha, hc0]
        have e2 := h2
        rw [haa, hc0] at e2
        linear_combination e2
      · exact mul_left_cancel₀ hc0 hprodA
    rcases pair_eq_of_sum_prod_eq hsum hprod with ⟨hb, hcc⟩ | ⟨hb, hcc⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hb, hcc⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hb, hcc⟩))))

/-- **The conjugation identity for root-of-unity triples.**  For `n`-th roots of unity `a, b, c`,
`conj(a+b+c)·(abc) = ab + bc + ca`.  (On the unit circle `conj x = x⁻¹`, so the conjugate of the
sum `e₁` is `(1/a + 1/b + 1/c) = e₂/e₃`.)  This is the mechanism that supplies the missing `e₂`
equality for free in `unitCircle_sidon_triple`. -/
theorem esymm2_eq_conj_esymm1_mul_esymm3 {n : ℕ} (hn : n ≠ 0) {a b c : ℂ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1) :
    (starRingEnd ℂ) (a + b + c) * (a * b * c) = a * b + b * c + c * a := by
  have ha0 : a ≠ 0 := fun h => by rw [h, zero_pow hn] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := fun h => by rw [h, zero_pow hn] at hb; exact zero_ne_one hb
  have hc0 : c ≠ 0 := fun h => by rw [h, zero_pow hn] at hc; exact zero_ne_one hc
  have hai : a * (starRingEnd ℂ) a = 1 := mul_conj_eq_one_of_pow_eq_one hn ha
  have hbi : b * (starRingEnd ℂ) b = 1 := mul_conj_eq_one_of_pow_eq_one hn hb
  have hci : c * (starRingEnd ℂ) c = 1 := mul_conj_eq_one_of_pow_eq_one hn hc
  have hcA : (starRingEnd ℂ) a = a⁻¹ := by field_simp; linear_combination hai
  have hcB : (starRingEnd ℂ) b = b⁻¹ := by field_simp; linear_combination hbi
  have hcC : (starRingEnd ℂ) c = c⁻¹ := by field_simp; linear_combination hci
  rw [map_add, map_add, hcA, hcB, hcC]
  field_simp
  ring

/-- **`μ_n` IS `B_3`-SIDON UNDER THE SYMMETRIC-FUNCTION LIFT.**  For `n`-th roots of unity
`a, b, c, a', b', c'` with equal sum `a+b+c = a'+b'+c' ≠ 0` and equal product `abc = a'b'c'`, the
unordered triples coincide.  The missing `e₂` equality is recovered for free from conjugation
(`esymm2_eq_conj_esymm1_mul_esymm3`), exactly as the product equality was recovered in
`unitCircle_sidon`.  No `e₁ ≠ 0` hypothesis is required (the product `e₃` is supplied directly). -/
theorem unitCircle_sidon_triple {n : ℕ} (hn : n ≠ 0) {a b c a' b' c' : ℂ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1)
    (ha' : a' ^ n = 1) (hb' : b' ^ n = 1) (hc' : c' ^ n = 1)
    (hsum : a + b + c = a' + b' + c') (hprod : a * b * c = a' * b' * c') :
    (a = a' ∧ b = b' ∧ c = c') ∨ (a = a' ∧ b = c' ∧ c = b') ∨
    (a = b' ∧ b = a' ∧ c = c') ∨ (a = b' ∧ b = c' ∧ c = a') ∨
    (a = c' ∧ b = a' ∧ c = b') ∨ (a = c' ∧ b = b' ∧ c = a') := by
  -- `e₂` from `e₁, e₃` via conjugation, on both sides; equal `e₁` + equal `e₃` ⟹ equal `e₂`.
  have h2L : (starRingEnd ℂ) (a + b + c) * (a * b * c) = a * b + b * c + c * a :=
    esymm2_eq_conj_esymm1_mul_esymm3 hn ha hb hc
  have h2R : (starRingEnd ℂ) (a' + b' + c') * (a' * b' * c') = a' * b' + b' * c' + c' * a' :=
    esymm2_eq_conj_esymm1_mul_esymm3 hn ha' hb' hc'
  have h2 : a * b + b * c + c * a = a' * b' + b' * c' + c' * a' := by
    rw [← h2L, ← h2R, hsum, hprod]
  exact triple_eq_of_esymm_eq hsum h2 hprod

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.triple_eq_of_esymm_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.esymm2_eq_conj_esymm1_mul_esymm3
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.unitCircle_sidon_triple
