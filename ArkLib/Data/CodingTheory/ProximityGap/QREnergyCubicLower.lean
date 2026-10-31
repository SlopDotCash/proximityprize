/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRAdditiveEnergyClosedForm

/-!
# The quadratic residues have cubic additive energy (#389)

A corollary of the closed form `qr_additive_energy`:

> **`qr_energy_cubic_lower`** — `(p−1)⁴ ≤ 16·p·E(QR)`, i.e. `E(QR) ≥ (p−1)⁴/(16p) ~ p³/16`.

Since `|QR| = (p−1)/2`, this is `E(QR) ≳ |QR|³/2` — the additive energy is of *cubic* (i.e.
maximal, up to a constant) order, the largest possible for a set of size `|QR|`. So the quadratic
residues (`n = (p−1)/2 > √p`, the large/QR end of the smooth-domain spectrum) are maximally
additively structured: the exact opposite of a Sidon-like set.

**Units.** `addEnergy` is the *unnormalized* quadruple count `#{(a,b,c,d) ∈ G⁴ : a+b = c+d}`.
Every `n`-element set has energy `≥ 2n² − n` (the trivial quadruples,
`E2CharFreeLowerBound.E2_ge_two_card_sq_sub_card`), so the scale floor is `n²`; a Sidon set
attains `2n² − n`, and a negation-closed Sidon-mod-negation set attains `3n² − 3n`
(`AdditiveEnergySidonModNeg.additiveEnergy_eq_of_sidonModNeg`). On this scale "Sidon-like"
means `E = Θ(n²)`, not `~2n` (that is the normalized energy `E/n`).

This pins the *bad-side extreme* of the δ\* dichotomy. The δ\*-good regime asks the smooth
multiplicative subgroup to have *near-minimal* unnormalized energy `E = n^{2+o(1)}`, e.g.
`E = O(n²·polylog q)` (equivalently normalized `E/n = O(n·polylog q)`); compare the conditional
bound `E ≤ n² + 2e·n²·r` of `PrizeEnergyHeadline.prize_addEnergy_of_dcEnergyBound`, which is
`O(n² log q)` at `r = ⌈ln q⌉` and whose `DCEnergyBound` input is still open. This theorem proves
that the large subgroup `QR` misses that target by the maximal margin — unnormalized energy
`Θ(n³)` — consistent with the expectation that only *small* smooth subgroups (`n ≤ √p`, the 2-power
NTT domains) can land in the prize window. It does not supply the open production upper bound.
Axiom-clean. Issue #389.
-/

open Finset AddChar MulChar Complex
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.QRExpSum

namespace ArkLib.ProximityGap.QREnergyCubic

variable {p : ℕ} [Fact p.Prime]

/-- **Cubic additive energy of the quadratic residues.** `(p−1)⁴ ≤ 16·p·E(QR)`. -/
theorem qr_energy_cubic_lower {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (hp2 : p ≠ 2) :
    ((p : ℝ) - 1) ^ 4 ≤ 16 * (p : ℝ) * addEnergy (QR p) := by
  have hE := qr_additive_energy hψ hp2
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out (p := p.Prime)).one_lt.le
  have hca : chiC (p := p) (-1) = 1 ∨ chiC (p := p) (-1) = -1 := by
    rcases quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero : (-1 : ZMod p) ≠ 0) with h | h <;>
      [left; right] <;> simp [chiC_apply, h]
  have hc : (-1 : ℝ) ≤ (chiC (p := p) (-1)).re := by
    rcases hca with h | h <;> rw [h] <;> norm_num [Complex.one_re, Complex.neg_re]
  have key : 16 * (p : ℝ) * addEnergy (QR p)
      = ((p : ℝ) - 1) ^ 4
        + ((p : ℝ) - 1) * (((p : ℝ) + 1) ^ 2 + 2 * (p : ℝ) * (1 + (chiC (p := p) (-1)).re)) := by
    linear_combination 16 * hE
  have h2 : (0 : ℝ) ≤ ((p : ℝ) + 1) ^ 2 + 2 * (p : ℝ) * (1 + (chiC (p := p) (-1)).re) := by
    have hnn : (0 : ℝ) ≤ 2 * (p : ℝ) * (1 + (chiC (p := p) (-1)).re) :=
      mul_nonneg (by linarith) (by linarith [hc])
    nlinarith [sq_nonneg ((p : ℝ) + 1)]
  have h3 : (0 : ℝ) ≤ ((p : ℝ) - 1)
      * (((p : ℝ) + 1) ^ 2 + 2 * (p : ℝ) * (1 + (chiC (p := p) (-1)).re)) :=
    mul_nonneg (by linarith) h2
  linarith [key, h3]

end ArkLib.ProximityGap.QREnergyCubic

#print axioms ArkLib.ProximityGap.QREnergyCubic.qr_energy_cubic_lower
