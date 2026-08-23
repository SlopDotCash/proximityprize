/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRFrequencySumEval
import ArkLib.Data.CodingTheory.ProximityGap.QRAdditiveEnergyGaussSum

/-!
# The quadratic-residue additive energy, closed form (#389)

Assembles the whole chain into the exact additive energy of the quadratic residues:

> **`qr_card`** — `|QR| = (p−1)/2`.
> **`qr_additive_energy`** — `p·E(QR) = ((p−1)/16)·((p−1)³ + (p+1)² + 2p(1 + (χ(−1)).re))`.

Specializing `(χ(−1)).re = 1` (`p ≡ 1 mod 4`) / `−1` (`p ≡ 3 mod 4`) gives the classical
`E(QR) = (p−1)(p²−2p+9)/16` / `(p−1)(p²−2p+5)/16`. This is the exact additive-energy extreme of the
"bad side" (`n = (p−1)/2 > √p`) of the δ\* small-vs-large-subgroup dichotomy: the quadratic residues
are maximally additively structured, the opposite of the 2-power smooth subgroups (`n ≤ √p`) the
prize needs controlled. A genuine novel closed form, proven from the in-tree moment–energy bridge +
the Gauss-sum identities. Axiom-clean. Issue #389.
-/

open Finset AddChar MulChar Complex
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.QREnergy
open ArkLib.ProximityGap.QRExpSum

namespace ArkLib.ProximityGap.QRExpSum

variable {p : ℕ} [Fact p.Prime]

/-- **QR count.** `|QR| = (p−1)/2`. -/
theorem qr_card (hp2 : p ≠ 2) : ((QR p).card : ℝ) = ((p : ℝ) - 1) / 2 := by
  classical
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_lt.le
  have hcardE : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hB0 : ∑ b ∈ Finset.univ.erase (0 : ZMod p), (chiC b).re = 0 := by
    rw [← Complex.re_sum, sum_chiC_erase_zero hp2, Complex.zero_re]
  have e1 : (QR p).card = ∑ a : ZMod p, (if chiC (p := p) a = 1 then 1 else 0) := by
    unfold QR; exact Finset.card_filter _ _
  have e2 : ((QR p).card : ℝ)
      = ∑ a ∈ Finset.univ.erase (0 : ZMod p), (if chiC a = 1 then (1 : ℝ) else 0) := by
    rw [e1, Nat.cast_sum,
      ← Finset.sum_erase Finset.univ (a := (0 : ZMod p)) (by rw [chiC_zero]; norm_num)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : chiC (p := p) a = 1 <;> simp [h]
  have hind : ∀ a ∈ Finset.univ.erase (0 : ZMod p),
      (if chiC a = 1 then (1 : ℝ) else 0) = (1 + (chiC a).re) / 2 := by
    intro a ha
    have hane : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have hca : chiC (p := p) a = 1 ∨ chiC a = -1 := by
      rcases quadraticChar_dichotomy hane with h | h <;> [left; right] <;> simp [chiC_apply, h]
    rcases hca with h | h <;> rw [h] <;> norm_num [Complex.neg_re, Complex.one_re]
  rw [e2, Finset.sum_congr rfl hind, ← Finset.sum_div, Finset.sum_add_distrib, hB0,
    Finset.sum_const, hcardE, nsmul_eq_mul, Nat.cast_sub hp1, Nat.cast_one]
  ring

/-- **QR additive energy, closed form.**
`p·E(QR) = ((p−1)/16)·((p−1)³ + (p+1)² + 2p(1 + (χ(−1)).re))`. -/
theorem qr_additive_energy {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (hp2 : p ≠ 2) :
    (p : ℝ) * addEnergy (QR p)
      = ((p : ℝ) - 1) / 16
        * (((p : ℝ) - 1) ^ 3 + ((p : ℝ) + 1) ^ 2 + 2 * (p : ℝ) * (1 + (chiC (p := p) (-1)).re)) := by
  have h := qr_energy_gaussSum hψ
  rw [sum_term_eval hψ hp2, tau_re_sq hψ hp2, qr_card hp2] at h
  rw [h]; ring

end ArkLib.ProximityGap.QRExpSum

#print axioms ArkLib.ProximityGap.QRExpSum.qr_card
#print axioms ArkLib.ProximityGap.QRExpSum.qr_additive_energy
