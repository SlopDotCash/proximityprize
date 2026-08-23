/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import ArkLib.Data.CodingTheory.ProximityGap.QRExponentialSum

/-!
# The quadratic-residue additive energy via the Gauss sum (#389)

Combining the 4th-moment bridge `∑_b ‖η_b‖⁴ = p·E(QR)` (`SubgroupGaussSumFourthMoment`, QR a
multiplicative subgroup) with `eta_QR_eq` (`η_b = (χ(b)·τ − 1)/2`, `τ = gaussSum χ ψ`):

> **`qr_energy_gaussSum`** — `p·E(QR) = |QR|⁴ + (1/16)·∑_{b≠0} ‖χ(b)·τ − 1‖⁴`.

This reduces the QR additive energy to an explicit Gauss-sum character sum. Evaluating it (via
`ττ̄=p`, `τ²=χ(−1)p`, `∑_{b≠0}χ(b)=0`, `∑χ(b)²=p−1`, `|QR|=(p−1)/2`) yields the closed form
`(p−1)(p²−2p+9)/16` (`p≡1 mod 4`) / `(p−1)(p²−2p+5)/16` (`p≡3 mod 4`) — the exact "bad-side"
extreme of the δ\* dichotomy. Axiom-clean. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.QRExpSum

namespace ArkLib.ProximityGap.QREnergy

variable {p : ℕ} [Fact p.Prime]

/-- **QR additive energy via the Gauss sum.** -/
theorem qr_energy_gaussSum {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    (p : ℝ) * addEnergy (QR p)
      = ((QR p).card : ℝ) ^ 4
        + (1 / 16) * ∑ b ∈ Finset.univ.erase (0 : ZMod p),
            ‖chiC b * gaussSum chiC ψ - 1‖ ^ 4 := by
  classical
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hfm := subgroup_gaussSum_fourthMoment hψ (QR p)
  rw [hcard] at hfm
  rw [← hfm, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
  have h0 : eta ψ (QR p) 0 = ((QR p).card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have hn0 : ‖eta ψ (QR p) 0‖ ^ 4 = ((QR p).card : ℝ) ^ 4 := by rw [h0, Complex.norm_natCast]
  rw [hn0]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hbne : b ≠ 0 := (Finset.mem_erase.mp hb).1
  rw [eta_QR_eq hψ hbne, norm_div, div_pow]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  ring

end ArkLib.ProximityGap.QREnergy

#print axioms ArkLib.ProximityGap.QREnergy.qr_energy_gaussSum
