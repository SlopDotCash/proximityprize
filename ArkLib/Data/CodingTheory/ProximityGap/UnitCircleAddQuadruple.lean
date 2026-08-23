/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Rigidity of additive quadruples on the unit circle (#389)

> **`unit_add_quadruple`** — for `a,b,c,d ∈ ℂ` all of modulus `1`, if `a + b = c + d` then either
> `{a,b} = {c,d}` (trivially) or `a + b = 0` (a zero-sum pair).

So the *only* additive coincidences among unit-modulus complex numbers are the trivial ones and the
antipodal zero-sum pairs. Applied to `μ_n ⊆` unit circle (`n` even, so closed under negation), this
forces the additive energy to be *exactly* `E_ℂ(μ_n) = 3n(n−1)`: the `2n²−n` trivial quadruples plus
the `n²` zero-sum quadruples, overlap `2n`. This is the rigidity behind the good-side quadratic
floor (`SubgroupEnergyQuadraticFloor.addEnergy_ge_three_mul`) being *tight* over `ℂ` — and shows the
positive additive-energy *excess* over `F_p` (`E(μ_{2^k}) = 3n(n−1) + excess`) is a purely
characteristic-`p` phenomenon (bad-prime cyclotomic coincidences), the open δ\* interior residual.

The proof is elementary (no cyclotomic fields): `|a+b|² = |c+d|²` forces `Re(a·conj b) = Re(c·conj d)`,
unit modulus gives `a·conj b = c·conj d` or `= conj(c·conj d)`, each collapsing via a quadratic
factorization. Axiom-clean. Issue #389.
-/

open Complex

namespace ArkLib.ProximityGap.UnitCircle

/-- For unit-modulus `z, w` with equal real parts, `z = w` or `z = conj w`. -/
theorem unit_re_eq {z w : ℂ} (hz : normSq z = 1) (hw : normSq w = 1) (hre : z.re = w.re) :
    z = w ∨ z = (starRingEnd ℂ) w := by
  rw [Complex.normSq_apply] at hz hw
  have hrr : z.re * z.re = w.re * w.re := by rw [hre]
  have him : (z.im - w.im) * (z.im + w.im) = 0 := by nlinarith [hz, hw, hrr]
  rcases mul_eq_zero.mp him with h | h
  · left; exact Complex.ext hre (sub_eq_zero.mp h)
  · right
    refine Complex.ext ?_ ?_
    · rw [Complex.conj_re]; exact hre
    · rw [Complex.conj_im]; linarith

/-- **Unit-circle additive rigidity.** `a + b = c + d` with `|a|=|b|=|c|=|d|=1` forces
`{a,b} = {c,d}` or `a + b = 0`. -/
theorem unit_add_quadruple {a b c d : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) (h : a + b = c + d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ a + b = 0 := by
  -- modulus-1 facts as normSq
  have nb : normSq b = 1 := by rw [Complex.normSq_eq_norm_sq, hb]; norm_num
  have nc : normSq c = 1 := by rw [Complex.normSq_eq_norm_sq, hc]; norm_num
  have nd : normSq d = 1 := by rw [Complex.normSq_eq_norm_sq, hd]; norm_num
  have hbb : b * (starRingEnd ℂ) b = 1 := by rw [Complex.mul_conj, nb]; norm_num
  have hcc : c * (starRingEnd ℂ) c = 1 := by rw [Complex.mul_conj, nc]; norm_num
  have hdd : d * (starRingEnd ℂ) d = 1 := by rw [Complex.mul_conj, nd]; norm_num
  -- real parts of a·conj b and c·conj d coincide
  have hre : (a * (starRingEnd ℂ) b).re = (c * (starRingEnd ℂ) d).re := by
    have h1 : normSq (a + b) = normSq (c + d) := by rw [h]
    rw [Complex.normSq_add, Complex.normSq_add] at h1
    rw [Complex.normSq_eq_norm_sq a, Complex.normSq_eq_norm_sq b, Complex.normSq_eq_norm_sq c,
      Complex.normSq_eq_norm_sq d, ha, hb, hc, hd] at h1
    nlinarith [h1]
  -- both have modulus 1
  have nz : normSq (a * (starRingEnd ℂ) b) = 1 := by
    rw [Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_eq_norm_sq a,
      Complex.normSq_eq_norm_sq b, ha, hb]; norm_num
  have nw : normSq (c * (starRingEnd ℂ) d) = 1 := by
    rw [Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_eq_norm_sq c,
      Complex.normSq_eq_norm_sq d, hc, hd]; norm_num
  rcases unit_re_eq nz nw hre with hzw | hzw
  · -- a·conj b = c·conj d  ⟹  a·d = b·c
    have hbc : a * d = b * c := by
      have step : a * (starRingEnd ℂ) b * (b * d) = c * (starRingEnd ℂ) d * (b * d) := by rw [hzw]
      rw [show a * (starRingEnd ℂ) b * (b * d) = a * d * (b * (starRingEnd ℂ) b) by ring, hbb,
        mul_one] at step
      rw [show c * (starRingEnd ℂ) d * (b * d) = b * c * (d * (starRingEnd ℂ) d) by ring, hdd,
        mul_one] at step
      exact step
    have hfac : (a - c) * (a + b) = 0 := by linear_combination a * h + hbc
    rcases mul_eq_zero.mp hfac with h0 | h0
    · left; have hac : a = c := sub_eq_zero.mp h0
      exact ⟨hac, by rw [hac] at h; exact add_left_cancel h⟩
    · right; right; exact h0
  · -- a·conj b = conj(c·conj d) = conj c · d  ⟹  a·c = b·d
    rw [map_mul, Complex.conj_conj] at hzw
    have hac : a * c = b * d := by
      have step : a * (starRingEnd ℂ) b * (b * c) = (starRingEnd ℂ) c * d * (b * c) := by rw [hzw]
      rw [show a * (starRingEnd ℂ) b * (b * c) = a * c * (b * (starRingEnd ℂ) b) by ring, hbb,
        mul_one] at step
      rw [show (starRingEnd ℂ) c * d * (b * c) = b * d * (c * (starRingEnd ℂ) c) by ring, hcc,
        mul_one] at step
      exact step
    have hfac : (a - d) * (a + b) = 0 := by linear_combination a * h + hac
    rcases mul_eq_zero.mp hfac with h0 | h0
    · right; left; have had : a = d := sub_eq_zero.mp h0
      refine ⟨had, ?_⟩
      rw [had, add_comm c d] at h; exact add_left_cancel h
    · right; right; exact h0

end ArkLib.ProximityGap.UnitCircle

#print axioms ArkLib.ProximityGap.UnitCircle.unit_add_quadruple
