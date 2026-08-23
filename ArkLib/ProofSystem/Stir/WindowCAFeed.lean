/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.CheckingVerifier
import ArkLib.ToMathlib.UnifiedProducerWindowGlue

/-!
# Issue #301 — the window CA feed: the checking bridge's `hCA` leg from the
# `UnifiedProducer` window glue

`stirCheckingCABridge` (the named open soundness bridge of #301) consumes the full
positive-width strict residual family `∀ k' > 0, StrictCoeffPolysResidual` at the protocol
proximity parameter `δ`.  Until now the only unconditional sources of that family were the
small-field discharges (`|F| ≤ |ι|`, `|F| ≤ deg²·10⁷`) — regimes that pin `secpar = 0`
(the budgets exceed total probability mass).  This file feeds the family from
`UnifiedProducerWindowGlue` instead:

* `strictCoeffPolys_all_of_window` — the family from a per-width window family
  hypothesis;
* `stirCheckingRbrSoundness_of_window` / `stir_main_of_checkingIOP_window` — the rbr-soundness
  and Theorem-5.1 front doors with the `hCA` leg discharged by the window glue, mirrors of
  the `_large` variants;
* `stir_main_of_checkingIOP_window_corner` — the zero-error-corner instantiation
  (`⌊δ·n⌋ = 0`, `deg ≤ n`): the window holds at **every** width, so `hCA` is fully
  discharged with no per-width hypothesis left.

**What this changes for #301 at `secpar > 0`**: unlike the small-field routes, nothing here
forces `ε_rbr ≥ 1` — the window discharge of `hCA` is compatible with sub-unit budgets
`ε_rbr ≤ 2^{−secpar}` at `secpar > 0`.  The remaining open soundness surface at sub-unit
budgets is therefore exactly the protocol-level bridge `stirCheckingCABridge` itself
(CA ⟹ per-round flip-probability bounds), plus `stir_main`'s own free-parameter legs.

HONESTY (regime): the window at width `k'` forces `δ ≲ (1−ρ)/(k'+2)`; demanding it at every
width (as the bridge's `∀ k'` family requires) confines `δ` to the zero-error corner
`⌊δ·n⌋ = 0` unless the caller supplies a finer per-width argument.  Within that corner the
discharge is genuine (Lagrange pinning through the `UnifiedProducer`), not small-field
vacuity; outside it the family remains open #304 content.

## References
* [BCIKS20] §4–§5; [ACFY24] STIR; issues #301, #304.
-/

set_option linter.style.longLine false

namespace StirIOP

namespace MultiRound

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal WhirIOP.Construction
open OracleInterface VectorIOP LinearCode
open ArkLib.ProofSystem.Stir.ErrorAccumulation

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [SampleableType F] in
/-- The full positive-width strict residual family from a per-width window family: every
instance routes through `unifiedProducer_of_window` (genuine Lagrange pinning, no
small-field vacuity). -/
theorem strictCoeffPolys_all_of_window
    (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) (hdeg : 0 < deg)
    (hwin : ∀ k' : ℕ, 0 < k' →
      ArkLib.UnifiedProducerWindowGlue.curveUDWindow k' deg (Fintype.card ι) δ) :
    ∀ k' : ℕ, 0 < k' →
      ProximityGap.StrictCoeffPolysResidual (ι := ι) (F := F)
        (k := k') (deg := deg) (domain := φ) (δ := δ) :=
  fun k' hk' =>
    ArkLib.UnifiedProducerWindowGlue.strictCoeffPolysResidual_of_window hdeg (hwin k' hk')

/-- RBR knowledge soundness of the checking verifier from the window family, conditional only
on the protocol-level checking bridge — the window mirror of
`stirCheckingRbrSoundness_of_large`. -/
theorem stirCheckingRbrSoundness_of_window
    (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) (hdeg : 0 < deg)
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ deg δ ε_rbr ProxGapBound ProxGapBound)
    (hwin : ∀ k' : ℕ, 0 < k' →
      ArkLib.UnifiedProducerWindowGlue.curveUDWindow k' deg (Fintype.card ι) δ) :
    stirCheckingRbrSoundnessResidual M φ deg δ ε_rbr :=
  stirCheckingRbrSoundness_of_CA M φ deg δ ε_rbr ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_window φ deg δ hdeg hwin)
    (PerRoundProximityGap.refl ProxGapBound)

/-- **Theorem 5.1 through the CHECKING IOPP, window CA discharge**: as
`stir_main_of_checkingIOP_large`, but with the `hCA` leg produced by the
`UnifiedProducer` window glue.  Compatible with sub-unit `ε_rbr` at `secpar > 0`: the
remaining soundness hypothesis is exactly the protocol-level bridge. -/
theorem stir_main_of_checkingIOP_window
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / rate (code φ degree)))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ degree δ ε_rbr ProxGapBound ProxGapBound)
    (hdeg : 0 < degree)
    (hwin : ∀ k' : ℕ, 0 < k' →
      ArkLib.UnifiedProducerWindowGlue.curveUDWindow k' degree (Fintype.card ι) δ)
    (hε : ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hM : ∃ c > 0, M ≤ c * (Real.log degree / Real.log k))
    (hLen : ∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree))
    (hQin : (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ)))
    (hQpf : ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
      (cₖ k) * ((Real.log degree) +
        secpar * (Real.log ((Real.log degree) / Real.log (1 / rate (code φ degree)))))) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF :=
  stir_main_of_checkingIOP_CA secpar hk hkGe δ hδub hF ε_rbr
    ProxGapBound ProxGapBound hBridge
    (strictCoeffPolys_all_of_window φ degree δ hdeg hwin)
    (PerRoundProximityGap.refl ProxGapBound)
    hε hM hLen hQin hQpf

/-- **Theorem 5.1 through the CHECKING IOPP, zero-error-corner CA discharge**: in the corner
`⌊δ·n⌋ = 0` (with `degree ≤ n`) the window holds at every width, so the `hCA` leg is fully
discharged with no per-width hypothesis.  The first `stir_main` route whose CA leg holds
genuinely (Lagrange pinning, not small-field vacuity) while remaining compatible with
sub-unit `ε_rbr` at `secpar > 0`; the open soundness surface is exactly `hBridge`. -/
theorem stir_main_of_checkingIOP_window_corner
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ] [NeZero degree]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / rate (code φ degree)))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ degree δ ε_rbr ProxGapBound ProxGapBound)
    (hfloor : Nat.floor (δ * (Fintype.card ι : ℝ≥0)) = 0)
    (hdeg_le : degree ≤ Fintype.card ι)
    (hε : ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hM : ∃ c > 0, M ≤ c * (Real.log degree / Real.log k))
    (hLen : ∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree))
    (hQin : (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ)))
    (hQpf : ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
      (cₖ k) * ((Real.log degree) +
        secpar * (Real.log ((Real.log degree) / Real.log (1 / rate (code φ degree)))))) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF :=
  stir_main_of_checkingIOP_CA secpar hk hkGe δ hδub hF ε_rbr
    ProxGapBound ProxGapBound hBridge
    (ArkLib.UnifiedProducerWindowGlue.strictCoeffPolys_all_of_floor_eq_zero
      (Nat.pos_of_ne_zero (NeZero.ne degree)) hfloor hdeg_le)
    (PerRoundProximityGap.refl ProxGapBound)
    hε hM hLen hQin hQpf

end MultiRound

end StirIOP

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms StirIOP.MultiRound.strictCoeffPolys_all_of_window
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundness_of_window
#print axioms StirIOP.MultiRound.stir_main_of_checkingIOP_window
#print axioms StirIOP.MultiRound.stir_main_of_checkingIOP_window_corner
