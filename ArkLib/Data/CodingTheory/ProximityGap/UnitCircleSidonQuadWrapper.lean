/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UnitCircleSidonQuad

/-!
# `μ_n` is `B_4`-Sidon under the symmetric-function lift — the FULL wrapper (#444, §0)

`UnitCircleSidonQuad.lean` landed the 4-element **scaffolding**: the char-free root-membership
brick `quad_root_mem_of_esymm_eq` (equal `e₁,e₂,e₃,e₄` ⟹ `a ∈ {a',b',c',d'}`) and the reciprocal
identities `esymm3_eq_conj_esymm1_mul_esymm4` (`e₃ = e₄·conj(e₁)`).  Its docstring explicitly left
two things open: **(i)** composing root-membership with the leftover triple to get *full multiset
equality*, and **(ii)** the full `B_4` wrapper for roots of unity.  This file lands both — the
4-element analogue of `unitCircle_sidon_triple`, completing the rung.

**The two theorems.**

* `quadruple_eq_of_esymm_eq` — the **full char-free multiset core** (integral domain): equal
  `e₁, e₂, e₃, e₄` force equal unordered quadruples.  It runs `quad_root_mem_of_esymm_eq` to pin
  `a` to one of `a', b', c', d'`, then discharges the leftover triple `{b,c,d}` against the three
  remaining primed roots via `triple_eq_of_esymm_eq` (the leftover `e₁, e₂, e₃` are recovered from
  the quadruple symmetric functions by `linear_combination`, with the `a = 0` branch handled by the
  leftover `e₃` identity exactly as in the 3-element core).
* `unitCircle_sidon_quad` (headline) — the **roots-of-unity wrapper**: for `n`-th roots of unity
  with equal `e₁` (sum), equal `e₂`, and equal `e₄` (product), the unordered quadruples coincide.
  The missing `e₃` equality is recovered *free* from conjugation
  (`esymm3_eq_conj_esymm1_mul_esymm4`), exactly as the `e₂` equality was recovered in
  `unitCircle_sidon_triple`.

**The probe-established picture** (`scripts/probes/probe_b4_sidon_mun.py`, exact roots of unity).
`μ_n` is NOT `B_4`-additive-Sidon from the sum alone (`138/330` collisions at `n=8`).  Fixing
`(e₁, e₄)` leaves collisions, but — per the scaffolding's reconciliation probe — **only zero-sum
ones** (`e₁ = 0`); for `e₁ ≠ 0`, `(e₁, e₄)` already determines `e₂`.  This wrapper takes `e₂` as a
hypothesis (the uniform statement that also covers the zero-sum branch), giving the clean
`(e₁, e₂, e₄) ⟹ quadruple` rung; the missing `e₃` then comes free from conjugation.

**Honest scope.**  NOT a CORE closure and NOT a refutation.  A structural Sidon-depth brick
completing the `4`-element rung of the `B_h` ladder for `μ_n`, extending the proven scaffolding
(`quad_root_mem_of_esymm_eq` + the reciprocal identities) and the 3-element
`unitCircle_sidon_triple`.  It is **thinness/roots-of-unity-essential** (the `e₃`-from-`e₁`
conjugation step needs `conj = inverse`, i.e. `|x| = 1`; false for generic field elements).  No
capacity / beyond-Johnson / growth-law claim (ASYMPTOTIC GUARD untouched); the open core is still
bootstrapping depth-`ℓ` Sidon structure to the full sup-norm bound.  NON-MOMENT (pure
symmetric-function / integral-domain algebra + conjugation).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Complex

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- `UnorderedTripleEq (a,b,c) (a',b',c')` : the unordered triples `{a,b,c}` and `{a',b',c'}`
coincide (one of the 6 permutations matches) — exactly the conclusion of `triple_eq_of_esymm_eq`,
packaged so the 4-element multiset core can state its leftover-triple conclusion compactly. -/
def UnorderedTripleEq {R : Type*} (t t' : R × R × R) : Prop :=
  (t.1 = t'.1 ∧ t.2.1 = t'.2.1 ∧ t.2.2 = t'.2.2) ∨
  (t.1 = t'.1 ∧ t.2.1 = t'.2.2 ∧ t.2.2 = t'.2.1) ∨
  (t.1 = t'.2.1 ∧ t.2.1 = t'.1 ∧ t.2.2 = t'.2.2) ∨
  (t.1 = t'.2.1 ∧ t.2.1 = t'.2.2 ∧ t.2.2 = t'.1) ∨
  (t.1 = t'.2.2 ∧ t.2.1 = t'.1 ∧ t.2.2 = t'.2.1) ∨
  (t.1 = t'.2.2 ∧ t.2.1 = t'.2.1 ∧ t.2.2 = t'.1)

/-- `triple_eq_of_esymm_eq` repackaged into `UnorderedTripleEq`. -/
theorem unorderedTripleEq_of_esymm_eq {R : Type*} [CommRing R] [IsDomain R] {a b c a' b' c' : R}
    (h1 : a + b + c = a' + b' + c')
    (h2 : a * b + b * c + c * a = a' * b' + b' * c' + c' * a')
    (h3 : a * b * c = a' * b' * c') :
    UnorderedTripleEq (a, b, c) (a', b', c') :=
  triple_eq_of_esymm_eq h1 h2 h3

/-- **The symmetric leftover-triple lemma.**  If the four quadruple elementary symmetric functions
of `(a,b,c,d)` equal those of `(w,p,q,r)` (written in this fixed order — the quadruple identities
are symmetric, so the caller reorders the primed tuple to put the matched root `w` first) and
`a = w`, then the leftover unordered triple `{b,c,d}` equals `{p,q,r}`.  Handles the `w = 0` branch
(where the product identity alone cannot cancel `a`) via the leftover `e₃` identity, exactly as the
3-element core handled its `a = 0` branch. -/
private theorem leftover_triple {R : Type*} [CommRing R] [IsDomain R]
    {a b c d w p q r : R}
    (h1 : a + b + c + d = w + p + q + r)
    (h2 : a * b + a * c + a * d + b * c + b * d + c * d
        = w * p + w * q + w * r + p * q + p * r + q * r)
    (h3 : a * b * c + a * b * d + a * c * d + b * c * d
        = w * p * q + w * p * r + w * q * r + p * q * r)
    (h4 : a * b * c * d = w * p * q * r)
    (ha : a = w) :
    UnorderedTripleEq (b, c, d) (p, q, r) := by
  subst ha
  have hs : b + c + d = p + q + r := by linear_combination h1
  have he2 : b * c + c * d + d * b = p * q + q * r + r * p := by
    linear_combination h2 - a * hs
  have hpr : b * c * d = p * q * r := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · have e3 := h3
      rw [ha0] at e3
      linear_combination e3
    · have hprodA : a * (b * c * d) = a * (p * q * r) := by linear_combination h4
      exact mul_left_cancel₀ ha0 hprodA
  refine unorderedTripleEq_of_esymm_eq hs ?_ hpr
  linear_combination he2

/-- **The full char-free `4`-element Sidon core.**  In an integral domain, two unordered
quadruples with equal `e₁, e₂, e₃, e₄` coincide as unordered quadruples: `a` equals one of
`a', b', c', d'`, and after removing that match the leftover unordered triple `{b, c, d}` equals
the remaining primed triple.  Composes `quad_root_mem_of_esymm_eq` (root membership) with the
leftover-triple reduction — the full multiset equality the scaffolding left open. -/
theorem quadruple_eq_of_esymm_eq {R : Type*} [CommRing R] [IsDomain R]
    {a b c d a' b' c' d' : R}
    (h1 : a + b + c + d = a' + b' + c' + d')
    (h2 : a * b + a * c + a * d + b * c + b * d + c * d
        = a' * b' + a' * c' + a' * d' + b' * c' + b' * d' + c' * d')
    (h3 : a * b * c + a * b * d + a * c * d + b * c * d
        = a' * b' * c' + a' * b' * d' + a' * c' * d' + b' * c' * d')
    (h4 : a * b * c * d = a' * b' * c' * d') :
    (a = a' ∧ UnorderedTripleEq (b, c, d) (b', c', d')) ∨
    (a = b' ∧ UnorderedTripleEq (b, c, d) (a', c', d')) ∨
    (a = c' ∧ UnorderedTripleEq (b, c, d) (a', b', d')) ∨
    (a = d' ∧ UnorderedTripleEq (b, c, d) (a', b', c')) := by
  rcases quad_root_mem_of_esymm_eq h1 h2 h3 h4 with ha | ha | ha | ha
  · exact Or.inl ⟨ha, leftover_triple
      (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4) ha⟩
  · exact Or.inr (Or.inl ⟨ha, leftover_triple
      (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4) ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ha, leftover_triple
      (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4) ha⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ha, leftover_triple
      (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3) (by linear_combination h4) ha⟩))

/-- **`μ_n` IS `B_4`-SIDON UNDER THE SYMMETRIC-FUNCTION LIFT.**  For `n`-th roots of unity
`a, b, c, d, a', b', c', d'` with equal sum `e₁`, equal `e₂`, and equal product `e₄`, the unordered
quadruples coincide.  The missing `e₃` equality is recovered for free from conjugation
(`esymm3_eq_conj_esymm1_mul_esymm4`), exactly as the `e₂` equality was recovered in
`unitCircle_sidon_triple`.  This is the full `4`-element rung, the analogue of
`unitCircle_sidon_triple`. -/
theorem unitCircle_sidon_quad {n : ℕ} (hn : n ≠ 0) {a b c d a' b' c' d' : ℂ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1) (hd : d ^ n = 1)
    (ha' : a' ^ n = 1) (hb' : b' ^ n = 1) (hc' : c' ^ n = 1) (hd' : d' ^ n = 1)
    (hsum : a + b + c + d = a' + b' + c' + d')
    (he2 : a * b + a * c + a * d + b * c + b * d + c * d
         = a' * b' + a' * c' + a' * d' + b' * c' + b' * d' + c' * d')
    (hprod : a * b * c * d = a' * b' * c' * d') :
    (a = a' ∧ UnorderedTripleEq (b, c, d) (b', c', d')) ∨
    (a = b' ∧ UnorderedTripleEq (b, c, d) (a', c', d')) ∨
    (a = c' ∧ UnorderedTripleEq (b, c, d) (a', b', d')) ∨
    (a = d' ∧ UnorderedTripleEq (b, c, d) (a', b', c')) := by
  -- `e₃` from `e₁, e₄` via conjugation on both sides; equal `e₁` + equal `e₄` ⟹ equal `e₃`.
  have h3L : (starRingEnd ℂ) (a + b + c + d) * (a * b * c * d)
      = a * b * c + a * b * d + a * c * d + b * c * d :=
    esymm3_eq_conj_esymm1_mul_esymm4 hn ha hb hc hd
  have h3R : (starRingEnd ℂ) (a' + b' + c' + d') * (a' * b' * c' * d')
      = a' * b' * c' + a' * b' * d' + a' * c' * d' + b' * c' * d' :=
    esymm3_eq_conj_esymm1_mul_esymm4 hn ha' hb' hc' hd'
  have h3 : a * b * c + a * b * d + a * c * d + b * c * d
      = a' * b' * c' + a' * b' * d' + a' * c' * d' + b' * c' * d' := by
    rw [← h3L, ← h3R, hsum, hprod]
  exact quadruple_eq_of_esymm_eq hsum he2 h3 hprod

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.quadruple_eq_of_esymm_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.unitCircle_sidon_quad
