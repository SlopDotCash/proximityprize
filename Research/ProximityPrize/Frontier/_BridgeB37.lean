/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Bridge B37 — far-line incidence equals the period sum (#444)

This frontier brick **consumes** the proven, axiom-clean substrate identity
`ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence_period_sum` and restates it
cleanly as a self-contained B37 target.

The far-line incidence `I(s₀, s₁) = #{γ : s₀ + γ·s₁ ∈ G}` over the field syndrome space
`V = F` equals, term by term, the sum of Gaussian periods `η_b = ∑_{y∈G} ψ(b·y)` over the
frequencies `b` annihilating the line direction `s₁`:

  `I(s₀, s₁) = ∑_{b : b·s₁ = 0} conj(η_b) · ψ(b·s₀)`.

This is face F1 (line–ball incidence) written verbatim in the F2 period basis — the exact
spectral skeleton on which the prize's far-coset attack lives. The proof is a single
delegation to the substrate; everything is additive-character orthogonality, with no
field-size or regime hypotheses.

Issue #444.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.IncidencePeriodBridge

namespace ArkLib.ProximityGap.Frontier.BridgeB37

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **B37 (far-line incidence = period sum).** For a primitive additive character `ψ`, any
ball `G`, and any affine line `s₀ + γ·s₁` over the field syndrome space `V = F`, the
line–ball incidence count equals the sum of Gaussian periods over the direction-annihilating
frequencies:

  `I(s₀, s₁) = ∑_{b : b·s₁ = 0} conj(η_b) · ψ(b·s₀)`.

A clean restatement of the substrate identity
`IncidencePeriodBridge.lineIncidence_period_sum`. -/
theorem farLineIncidence_eq_periodSum {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) :
    (lineIncidence G s₀ s₁ : ℂ)
      = ∑ b ∈ Finset.univ.filter (fun b : F => b * s₁ = 0),
          (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀) :=
  lineIncidence_period_sum hψ G s₀ s₁

/-- **B37, far-direction (`s₁ ≠ 0`) specialization.** When the line has a genuine direction
the only annihilating frequency is `b = 0`, so the incidence collapses to the average
`η₀ = |G|`: the affine line is a bijection of `F`, hitting `G` exactly `|G|` times. -/
theorem farLineIncidence_far_dir {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) (hs₁ : s₁ ≠ 0) :
    (lineIncidence G s₀ s₁ : ℂ) = (G.card : ℂ) := by
  rw [farLineIncidence_eq_periodSum hψ G s₀ s₁]
  have hfilt : (Finset.univ.filter (fun b : F => b * s₁ = 0)) = {0} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact (mul_eq_zero.mp h).resolve_right hs₁
    · intro h; subst h; simp
  rw [hfilt]
  simp only [Finset.sum_singleton, zero_mul]
  rw [eta]
  simp [conj_eta, AddChar.map_zero_eq_one]

end ArkLib.ProximityGap.Frontier.BridgeB37

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.Frontier.BridgeB37.farLineIncidence_eq_periodSum
#print axioms ArkLib.ProximityGap.Frontier.BridgeB37.farLineIncidence_far_dir
