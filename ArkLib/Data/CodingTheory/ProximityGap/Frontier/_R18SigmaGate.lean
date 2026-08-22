/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17QuadrupleWeilRung

/-!
# Round 18: Sigma lower-envelope gate for the r = 2 Weil rung

The R17 r = 2 Weil rung consumes the probe-only hypothesis

`|G| * q ≤ 2 * m * Σ`.

The draft R18 Σ-equidistribution lane aims to prove a sharper lower envelope

`|G| * q - |G|^2 - (m-1) * |G| * (|G|-1) * sqrt(q) ≤ m * Σ`

from a character-indicator decomposition plus Gauss-sum bounds.  This file isolates the purely
real-variable final gate: in the R17 regime `16*m^2*|G|^2 ≤ q`, that lower envelope implies the
exact `hSig` input consumed by `_R17QuadrupleWeilRung`.

No analytic closure is claimed here; the load-bearing analytic statement remains the lower envelope.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue

namespace ArkLib.ProximityGap.Frontier.R18SigmaGate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The abstract real-variable Σ lower envelope produced by the character-indicator/Gauss-sum
calculation.  `m` is the subgroup index/order, `n` is `|G|`, `q` is the field cardinality, and `Sig`
is the mass `∑_{b∈H} ‖η_b‖²`. -/
def SigmaLowerEnvelope (m n q Sig : ℝ) : Prop :=
  n * q - n ^ 2 - (m - 1) * (n * (n - 1) * Real.sqrt q) ≤ m * Sig

/-- **Regime algebra for `hSig`.**  In the R17 Weil regime `16*m²*n² ≤ q`, the Σ lower envelope
implies the exact input `n*q ≤ 2*m*Σ` consumed by `r2Rung_of_weil`.

The proof is deliberately pure real arithmetic so the analytic expansion can be developed
separately and plugged in as `SigmaLowerEnvelope`. -/
theorem hSig_of_sigmaLowerEnvelope
    {m n q Sig : ℝ}
    (hm : 2 ≤ m) (hn : 1 ≤ n)
    (hq0 : 0 ≤ q)
    (hreg : 16 * m ^ 2 * n ^ 2 ≤ q)
    (hlow : SigmaLowerEnvelope m n q Sig) :
    n * q ≤ 2 * m * Sig := by
  unfold SigmaLowerEnvelope at hlow
  set s : ℝ := Real.sqrt q with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg q
  have hssq : s ^ 2 = q := by rw [hsdef, Real.sq_sqrt hq0]
  have hmn : 4 * m * n ≤ s := by
    have hsq : (4 * m * n) ^ 2 ≤ s ^ 2 := by
      rw [hssq]
      nlinarith [hreg]
    have hnonneg : 0 ≤ 4 * m * n := by nlinarith [hm, hn]
    nlinarith [hsq, hnonneg, hs0]
  have hterm1 : (m - 1) * (n * (n - 1) * s) ≤ n * q / 4 := by
    have hmn_s : m * n * s ≤ s * s / 4 := by nlinarith [hmn, hs0]
    have hmono : (m - 1) * (n - 1) * s ≤ m * n * s := by nlinarith [hm, hn, hs0]
    have hrewrite : (m - 1) * (n * (n - 1) * s) = n * ((m - 1) * (n - 1) * s) := by ring
    rw [hrewrite]
    nlinarith [hmono, hmn_s, hssq, hn]
  have hterm2 : n ^ 2 ≤ n * q / 4 := by
    have hs8 : 8 ≤ s := by nlinarith [hmn, hm, hn]
    have hns : n ≤ s := by nlinarith [hmn, hm]
    have hs_le : s ≤ s * s / 4 := by nlinarith [hs8]
    nlinarith [hns, hs_le, hssq, hn]
  nlinarith [hlow, hterm1, hterm2, hm]

/-- Field-cardinality form of `hSig_of_sigmaLowerEnvelope`, matching the notation in the R17
Weil rung. -/
theorem hSig_of_sigmaLowerEnvelope_field
    (ψ : AddChar F ℂ) (G H : Finset F) {m : ℝ}
    (hm : 2 ≤ m) (hn : 1 ≤ G.card)
    (hreg : 16 * m ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hlow :
      SigmaLowerEnvelope m (G.card : ℝ) (Fintype.card F : ℝ)
        (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)) :
    (G.card : ℝ) * (Fintype.card F : ℝ)
      ≤ 2 * m * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
  have hSig0 : 0 ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by positivity
  have hq0 : 0 ≤ (Fintype.card F : ℝ) := by positivity
  have hnR : (1 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hn
  exact hSig_of_sigmaLowerEnvelope hm hnR hq0 hreg hlow

/-- R17 r = 2 Weil rung with `hSig` supplied by the Σ lower-envelope gate. -/
theorem r2Rung_of_weil_of_sigmaLowerEnvelope
    (ψ : AddChar F ℂ) (G H D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) {m : ℕ} {Cw : ℝ}
    (hm : 1 ≤ m) (hm2 : 2 ≤ (m : ℝ)) (hn : 1 ≤ G.card) (hCw : 0 ≤ Cw)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G H D X g m)
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (m : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hlow :
      SigmaLowerEnvelope (m : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
        (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidenceMomentAway ψ G H D 2
      ≤ (32 * (Cw * (X.card : ℝ) ^ 4 + 1) / (m : ℝ) ^ 2)
        * ((Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2) :=
  ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.r2Rung_of_weil
    ψ G H D X g m hm hCw hdec hg h4 hq1 hnq
    (hSig_of_sigmaLowerEnvelope_field ψ G H hm2 hn hreg hlow)

/-- `WickAwayAtWithConstant` version of the same Σ lower-envelope gate. -/
theorem wickAwayAtWithConstant_two_of_weil_of_sigmaLowerEnvelope
    (ψ : AddChar F ℂ) (G H D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) {m : ℕ} {Cw : ℝ}
    (hm : 1 ≤ m) (hm2 : 2 ≤ (m : ℝ)) (hn : 1 ≤ G.card) (hCw : 0 ≤ Cw)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G H D X g m)
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (m : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hlow :
      SigmaLowerEnvelope (m : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
        (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)) :
    WickAwayAtWithConstant ψ G H D 2
      (32 * (Cw * (X.card : ℝ) ^ 4 + 1) / (m : ℝ) ^ 2 / 3) :=
  ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.wickAwayAtWithConstant_two_of_weil
    ψ G H D X g m hm hCw hdec hg h4 hq1 hnq
    (hSig_of_sigmaLowerEnvelope_field ψ G H hm2 hn hreg hlow)

end ArkLib.ProximityGap.Frontier.R18SigmaGate

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R18SigmaGate.hSig_of_sigmaLowerEnvelope
#print axioms ArkLib.ProximityGap.Frontier.R18SigmaGate.hSig_of_sigmaLowerEnvelope_field
#print axioms ArkLib.ProximityGap.Frontier.R18SigmaGate.r2Rung_of_weil_of_sigmaLowerEnvelope
#print axioms ArkLib.ProximityGap.Frontier.R18SigmaGate.wickAwayAtWithConstant_two_of_weil_of_sigmaLowerEnvelope
