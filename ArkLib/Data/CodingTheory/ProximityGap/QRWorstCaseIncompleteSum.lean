/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRExponentialSum
import ArkLib.Data.CodingTheory.ProximityGap.QuadraticGaussSumNorm
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# The exact worst-case per-frequency bound for the quadratic-residue subgroup (#407)

The δ\* prize's per-frequency core is the named open Prop `WorstCaseIncompleteSumBound ψ G M`
(`InteriorWorstCaseIncompleteSum.lean`): `∀ b ≠ 0, ‖η_b‖² ≤ M`, where `η_b = Σ_{y∈G} ψ(b·y)`.
For a general 2-power NTT subgroup `μ_n` this is the BGK / Paley-graph open problem (no proven
`√(n·polylog)` worst-case bound — that is the prize wall).

**This file discharges that open Prop UNCONDITIONALLY for the index-2 (quadratic-residue) subgroup**
`QR(p) = {a : χ(a) = 1}` — the one case where square-root cancellation is *classical*, given by the
quadratic Gauss-sum magnitude `‖τ‖² = p` (Mathlib `gaussSum_sq`, in-tree `gaussSum_normSq`).  No
wall, no open input: it reduces entirely to proven number theory.

## The result (axiom-clean)

* `eta_QR_norm_le` — for `b ≠ 0`, `‖η_b(QR)‖ ≤ (√p + 1)/2`.  Since `|QR| = (p−1)/2`, this is
  `‖η_b‖ ≈ √(p)/2 ≈ √(|QR|/2)` — genuine √-cancellation (the beyond-Johnson, sub-`√q` per-frequency
  object), EXACT, for free from the classical Gauss sum.
* `worstCaseIncompleteSumBound_QR` — packages it as the named Prop
  `WorstCaseIncompleteSumBound ψ (QR p) ((√p + 1)²/4)`: the open per-frequency core, discharged with
  **no hypothesis beyond `p` odd prime**.

Mechanism (proof of `eta_QR_eq`, in-tree): `η_b(QR) = (χ(b)·τ − 1)/2`, `τ = gaussSum χ ψ`; with
`‖χ(b)‖ = 1` (b ≠ 0) and `‖τ‖ = √p` the triangle inequality gives `‖η_b‖ ≤ (√p + 1)/2`.

**Scope (honest).**  This is the `index = 2` case.  It does NOT reach the prize 2-power FFT subgroup
(`μ_n`, index `≈ 2¹²⁸`), where the same per-frequency bound is the open BGK wall.  But it is a
genuine, exact, axiom-clean, beyond-Johnson discharge of the named open Prop — the index-2 lane of
the worst-case incomplete-sum problem, solved by the classical quadratic Gauss sum.  Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.QRExpSum

variable {p : ℕ} [Fact p.Prime]

/-- `‖χ(b)‖ = 1` for every `b ≠ 0` (the quadratic character is `±1`-valued off `0`).  The general-`b`
companion of `norm_chiC_neg_one`. -/
theorem norm_chiC_unit {b : ZMod p} (hb : b ≠ 0) : ‖chiC (p := p) b‖ = 1 := by
  rcases quadraticChar_dichotomy hb with h | h <;> rw [chiC_apply, h] <;> norm_num

/-- The quadratic Gauss-sum magnitude `‖τ‖ = √p` (from `‖τ‖² = p`). -/
theorem norm_gaussSum_chiC {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (hp2 : p ≠ 2) :
    ‖gaussSum (chiC (p := p)) ψ‖ = Real.sqrt (p : ℝ) := by
  rw [← gaussSum_normSq hψ hp2, Real.sqrt_sq (norm_nonneg _)]

/-- **The exact QR per-frequency worst-case bound.**  For `b ≠ 0`, `‖η_b(QR)‖ ≤ (√p + 1)/2`.
Proof: `η_b = (χ(b)·τ − 1)/2` (`eta_QR_eq`); `‖χ(b)·τ − 1‖ ≤ ‖χ(b)‖·‖τ‖ + 1 = √p + 1`. -/
theorem eta_QR_norm_le {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) :
    ‖eta ψ (QR p) b‖ ≤ (Real.sqrt (p : ℝ) + 1) / 2 := by
  rw [eta_QR_eq hψ hb, norm_div]
  have hnum : ‖chiC (p := p) b * gaussSum chiC ψ - 1‖ ≤ Real.sqrt (p : ℝ) + 1 := by
    calc ‖chiC (p := p) b * gaussSum chiC ψ - 1‖
        ≤ ‖chiC (p := p) b * gaussSum chiC ψ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖chiC (p := p) b‖ * ‖gaussSum chiC ψ‖ + 1 := by rw [norm_mul, norm_one]
      _ = Real.sqrt (p : ℝ) + 1 := by
            rw [norm_chiC_unit hb, norm_gaussSum_chiC hψ hp2, one_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  gcongr

/-- **The named open per-frequency core, discharged for the index-2 subgroup.**
`WorstCaseIncompleteSumBound ψ (QR p) ((√p + 1)²/4)` holds with NO hypothesis beyond `p ≠ 2`. -/
theorem worstCaseIncompleteSumBound_QR {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (hp2 : p ≠ 2) :
    WorstCaseIncompleteSumBound ψ (QR p) ((Real.sqrt (p : ℝ) + 1) ^ 2 / 4) := by
  intro b hb
  have hle : ‖eta ψ (QR p) b‖ ≤ (Real.sqrt (p : ℝ) + 1) / 2 := eta_QR_norm_le hψ hp2 hb
  calc ‖eta ψ (QR p) b‖ ^ 2
      ≤ ((Real.sqrt (p : ℝ) + 1) / 2) ^ 2 := by gcongr
    _ = (Real.sqrt (p : ℝ) + 1) ^ 2 / 4 := by ring

/-- **End-to-end energy budget for the quadratic residues.**  The discharged worst-case bound feeds
the in-tree consumer `addEnergy_le_of_worstCase`, giving an unconditional additive-energy envelope
`q·E(QR) ≤ |QR|⁴ + ((√p+1)²/4)·(q·|QR|)` — no regime hypothesis. -/
theorem addEnergy_QR_le {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (hp2 : p ≠ 2) :
    (Fintype.card (ZMod p) : ℝ) * (addEnergy (QR p) : ℝ)
      ≤ (QR p).card ^ 4
        + ((Real.sqrt (p : ℝ) + 1) ^ 2 / 4) * ((Fintype.card (ZMod p) : ℝ) * (QR p).card) := by
  refine addEnergy_le_of_worstCase hψ (QR p) ?_ (worstCaseIncompleteSumBound_QR hψ hp2)
  positivity

end ArkLib.ProximityGap.QRExpSum

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.QRExpSum.norm_chiC_unit
#print axioms ArkLib.ProximityGap.QRExpSum.norm_gaussSum_chiC
#print axioms ArkLib.ProximityGap.QRExpSum.eta_QR_norm_le
#print axioms ArkLib.ProximityGap.QRExpSum.worstCaseIncompleteSumBound_QR
#print axioms ArkLib.ProximityGap.QRExpSum.addEnergy_QR_le
