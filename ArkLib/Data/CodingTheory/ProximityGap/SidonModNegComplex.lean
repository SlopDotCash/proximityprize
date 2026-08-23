/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg
import Mathlib.Analysis.Complex.Basic

/-!
# The char-0 discharge of `SidonModNeg` for unit complex numbers (#389)

The additive-energy program reduces the Johnson-side rep bound to `SidonModNeg G` — the
property that the only additive coincidences `a+b=c+d` in `G` are the trivial
(ordered-pair-equal) ones and the zero-sum ones — under which the fleet's
`additiveEnergy_eq_of_sidonModNeg` pins `E(G) = 3n²−3n`.  Until now `SidonModNeg` was only
discharged by `decide` at single finite instances (`sidonModNeg_H4`).

This file discharges it **in general in characteristic zero**: any finite set of unit
complex numbers — in particular any set of roots of unity, hence every `μ_n ⊂ ℂ` — is
`SidonModNeg`, with **no height threshold**.

> **`unit_sidonModNeg`** — for `a,b,c,d` on the unit circle with `a+b=c+d`:
> `(a=c ∧ b=d) ∨ (a=d ∧ b=c) ∨ a+b=0`.
> **`sidonModNeg_of_unitNorm`** — `(∀ x ∈ G, ‖x‖ = 1) ⟹ SidonModNeg G` for `G : Finset ℂ`.

Mechanism (the same `|a| = 1 ⟹ ā = 1/a` conjugate algebra as `ThreeRootsSumZeroCharZero`):
for unit `a, b` with nonzero sum `s = a+b`, `ā + b̄ = s̄` gives `s/(ab) = s̄`, so `ab = s/s̄`
is **determined by `s`** — hence `a,b` and any other unit pair `c,d` with the same sum have
the same product, and Vieta forces the pairs to coincide.

**Scope (honesty).** This is the *characteristic-zero* discharge: it pins `E(μ_n) = 3n²−3n`
over `ℂ` exactly, and the energy chain it feeds is **Johnson-strength** — it sharpens the
δ\* lower bound to the Johnson edge `1−√ρ` with the optimal constant, but does **not** cross
into the past-Johnson window where δ\* lives.  The lift of this discharge to `F_p` (valid
for `p` above an explicit height threshold, by Mann/Conway–Jones) is the remaining
finite-characteristic input on this Johnson-side face.  Issue #389.
-/

open Complex

namespace ProximityGap.SidonModNegComplex

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg
open ArkLib.ProximityGap.AdditiveEnergyRepBound (additiveEnergy)

/-- **Vieta pairing**: equal sum and equal product force the unordered pair to match. -/
theorem same_sum_prod {F : Type*} [Field F] {a b c d : F}
    (hs : a + b = c + d) (hp : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hroot : (a - c) * (a - d) = 0 := by linear_combination a * hs - hp
  rcases mul_eq_zero.mp hroot with h | h
  · exact Or.inl ⟨by linear_combination h, by linear_combination hs - h⟩
  · exact Or.inr ⟨by linear_combination h, by linear_combination hs - h⟩

/-- A unit complex number times its conjugate is `1`. -/
theorem mul_conj_eq_one {u : ℂ} (hu : ‖u‖ = 1) : u * (starRingEnd ℂ) u = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq u, hu]; norm_num

/-- For unit `a, b` with nonzero sum `s = a+b`, the product is `a·b = s / conj s`. -/
theorem unit_prod_eq {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hs : a + b ≠ 0) :
    a * b = (a + b) / (starRingEnd ℂ) (a + b) := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hca : (starRingEnd ℂ) a = 1 / a := by
    field_simp; rw [mul_comm]; exact mul_conj_eq_one ha
  have hcb : (starRingEnd ℂ) b = 1 / b := by
    field_simp; rw [mul_comm]; exact mul_conj_eq_one hb
  have hcs : (starRingEnd ℂ) (a + b) = (a + b) / (a * b) := by
    rw [map_add, hca, hcb]; field_simp; ring
  rw [hcs]
  have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
  field_simp

/-- **The char-0 Sidon-modulo-negation property** for unit complex numbers. -/
theorem unit_sidonModNeg {a b c d : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hsum : a + b = c + d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ a + b = 0 := by
  by_cases hs : a + b = 0
  · exact Or.inr (Or.inr hs)
  · have hprodab : a * b = (a + b) / (starRingEnd ℂ) (a + b) := unit_prod_eq ha hb hs
    have hscd : c + d ≠ 0 := hsum ▸ hs
    have hprodcd : c * d = (c + d) / (starRingEnd ℂ) (c + d) := unit_prod_eq hc hd hscd
    have hp : a * b = c * d := by rw [hprodab, hprodcd, hsum]
    rcases same_sum_prod hsum hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **The general discharge**: any finite set of unit complex numbers is `SidonModNeg` —
no height threshold.  In particular every `μ_n ⊂ ℂ` (roots of unity have norm `1`) satisfies
`SidonModNeg`, so `additiveEnergy_eq_of_sidonModNeg` pins `E(μ_n) = 3n²−3n` over `ℂ`. -/
theorem sidonModNeg_of_unitNorm {G : Finset ℂ} (hG : ∀ x ∈ G, ‖x‖ = 1) :
    SidonModNeg G :=
  fun a ha b hb c hc d hd hsum =>
    unit_sidonModNeg (hG a ha) (hG b hb) (hG c hc) (hG d hd) hsum

/-- **The char-0 minimal additive energy, explicit**: a negation-closed finite set of unit
complex numbers (e.g. `μ_n ⊂ ℂ` for even `n`) has additive energy exactly `3n²−3n` — the
minimal (Sidon-like) value, with no height threshold. -/
theorem additiveEnergy_unitNorm {G : Finset ℂ}
    (hG : ∀ x ∈ G, ‖x‖ = 1) (hneg : ∀ x ∈ G, -x ∈ G) :
    additiveEnergy G = 3 * G.card ^ 2 - 3 * G.card := by
  refine additiveEnergy_eq_of_sidonModNeg (two_ne_zero) ?_ hneg
    (sidonModNeg_of_unitNorm hG)
  intro h0
  have := hG 0 h0
  simp at this

end ProximityGap.SidonModNegComplex

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SidonModNegComplex.unit_sidonModNeg
#print axioms ProximityGap.SidonModNegComplex.sidonModNeg_of_unitNorm
#print axioms ProximityGap.SidonModNegComplex.additiveEnergy_unitNorm
