/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CurveFamilyLines
import ArkLib.ProofSystem.Fri.Spec.PerRoundCA
import ArkLib.ProofSystem.Stir.ErrorAccumulation

/-!
# Issue #304 — the faithful front door wired into the WHIR/FRI/STIR per-round consumers

`CurveFamilyLines.lean` produced the numeric keystone wrappers from the *satisfiable* faithful
curve-family interface (`CurveFamilyData`): `keystone_curves_bound_of_curveFamilyData` gives
`epsCA_curves ≤ k · errorBound` from a per-`(u, P)` producer of the faithful §5 datum, with NO
small-field hypothesis.  This file routes that front door into every in-tree per-round consumer:

* **WHIR keystone reduction** (`Whir/KeystoneReduction.lean`):
  `roundKeystoneData_of_curveFamilyData` constructs `Core2Keystone.RoundKeystoneData` from
  per-round faithful producers in the *strict* Johnson regime — the `hStrictCoeff` field is
  discharged by `strictCoeffPolysResidual_of_curveFamilyData` and the `hBoundary` field is
  discharged *outright* (`boundaryProbabilityResidual_of_strict`: at `δ < 1 − √ρ` the boundary
  branch is unreachable).  The downstream payoffs
  (`Core2Keystone.perRoundProximityGap_of_correlatedAgreement`, `…_transfer`,
  `RoundKeystoneData.curves_bound`) then flow through unchanged
  (`perRoundProximityGap_of_curveFamilyData`, `perRoundProximityGap_transfer_of_curveFamilyData`,
  `roundKeystoneData_curves_bound_of_curveFamilyData`), as does the `k = 1` proximity-gap bound
  `perRound_epsPG_bound_of_curveFamilyData` (ABF26 Fact 4.5 chain).
* **FRI round-error accounting** (`Fri/Spec/PerRoundCA.lean` pattern):
  `friPerRound_epsCA_le_roundError_of_curveFamilyData` — the round-`i` curve CA error is
  `≤ κ · roundError i`, from a faithful producer at the round parameters (the satisfiable
  replacement for the vacuous `perRound_epsCA_le_roundError_of_card_le`, which needs
  `|F| ≤ κ · 2^(n−N)`).
* **STIR fold-budget accounting** (`Stir/ErrorAccumulation.lean`):
  `stir_perRound_foldBudget_of_curveFamilyData` — the genuine in-tree
  `PerRoundProximityGap` hypothesis family is discharged with the keystone-supplied
  `errorBound` values, the fold budget is bounded via `foldBudget_le_of_keystone`, AND each
  accounting error is certified non-vacuously by the faithful per-round CA bound.

Honest residual: the per-`(u, P)` producer (`CurveFamilyProducer`) — i.e. the BCIKS20 §5
statement that every good decoded family lies on a polynomial curve — remains the open core
(issue #304); everything downstream of it is PROVEN here.  Unlike the small-field route, this
hypothesis is *satisfiable* in the deployed large-field regime
(`curveFamilyData_self` / `curveFamilyData_const` anti-vacuity witnesses).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, Theorems 1.4/1.5, §5.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace FaithfulCurveExtraction

namespace RoundConsumers

/-! ## §0. The per-round producer surface -/

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The per-`(u, P)` faithful curve-family producer at one round's parameters.**  This is
exactly the `hInput` hypothesis of `keystone_curves_bound_of_curveFamilyData`
(`CurveFamilyLines.lean`), named so the per-round consumers can quantify over rounds: given the
keystone branch context (probability above threshold, Johnson radius, strict square-root radius)
and any decoded family `P` of the stack `u`, produce the faithful §5 curve datum
`CurveFamilyData u P`. -/
abbrev CurveFamilyProducer (k deg : ℕ) (domain : ι ↪ F) (δ : ℝ≥0) : Type :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    δ < 1 - ReedSolomon.sqrtRate deg domain →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
      CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P

/-- **In the strict Johnson regime the §6.2 boundary residual is vacuous.**  The
`BoundaryProbabilityResidual` only fires on the branch `¬ δ < 1 − √ρ`; with the strict radius
hypothesis that branch is unreachable.  This is what lets the faithful (strict-regime) front
door fill BOTH residual fields of the WHIR `RoundKeystoneData`. -/
theorem boundaryProbabilityResidual_of_strict {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
    BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro _hk _u _hprob _hJ hnot
  exact absurd hδ hnot

/-! ## §1. Brick 1 — WHIR `RoundKeystoneData` from per-round faithful producers -/

/-- **WHIR per-round keystone data from the faithful front door.**  Constructs
`Core2Keystone.RoundKeystoneData` (`Whir/KeystoneReduction.lean`) from a per-round family of
faithful curve-family producers in the strict square-root regime:

* `hStrictCoeff i` — discharged by `strictCoeffPolysResidual_of_curveFamilyData (hInput i)`;
* `hBoundary i`   — discharged outright by `boundaryProbabilityResidual_of_strict (hδ i)`;
* `hδ i`          — the weak form of the strict radius.

Every WHIR/STIR consumer of `RoundKeystoneData` (the `curves_bound` numeric guarantee, the
`PerRoundProximityGap` discharge, the budget accounting) is now reachable from the satisfiable
faithful interface instead of the vacuous small-field one. -/
noncomputable def roundKeystoneData_of_curveFamilyData {n : ℕ}
    (k deg : Fin n → ℕ) (degNeZero : ∀ i, NeZero (deg i))
    (domain : Fin n → (ι ↪ F)) (δ : Fin n → ℝ≥0)
    (hδ : ∀ i, δ i < 1 - ReedSolomon.sqrtRate (deg i) (domain i))
    (hInput : ∀ i, CurveFamilyProducer (k i) (deg i) (domain i) (δ i)) :
    Core2Keystone.RoundKeystoneData n F ι where
  k := k
  deg := deg
  degNeZero := degNeZero
  domain := domain
  δ := δ
  hStrictCoeff := fun i => strictCoeffPolysResidual_of_curveFamilyData (hInput i)
  hBoundary := fun i => boundaryProbabilityResidual_of_strict (k := k i) (hδ i)
  hδ := fun i => le_of_lt (hδ i)

/-- **Per-round numeric CA bound through the constructed `RoundKeystoneData`.**  For every
round `i`, `epsCA_curves Cᵢ kᵢ δᵢ δᵢ ≤ kᵢ · errorBound δᵢ degᵢ domainᵢ` — the WHIR §2.1
`RoundKeystoneData.curves_bound` instantiated at the faithful datum. -/
theorem roundKeystoneData_curves_bound_of_curveFamilyData {n : ℕ}
    (k deg : Fin n → ℕ) (degNeZero : ∀ i, NeZero (deg i))
    (domain : Fin n → (ι ↪ F)) (δ : Fin n → ℝ≥0)
    (hδ : ∀ i, δ i < 1 - ReedSolomon.sqrtRate (deg i) (domain i))
    (hInput : ∀ i, CurveFamilyProducer (k i) (deg i) (domain i) (δ i)) (i : Fin n) :
    epsCA_curves (F := F) (ReedSolomon.code (domain i) (deg i) : Set (ι → F))
        (k i) (δ i) (δ i) ≤
      ((k i * errorBound (δ i) (deg i) (domain i) : ℝ≥0) : ENNReal) :=
  (roundKeystoneData_of_curveFamilyData k deg degNeZero domain δ hδ hInput).curves_bound i

/-! ## §2. Brick 2 — the per-round proximity-gap discharge, faithful entrance -/

/-- **`PerRoundProximityGap` (WHIR form) + the genuine numeric guarantee, from the faithful
front door.**  Composes brick 1 through `Core2Keystone.perRoundProximityGap_of_correlatedAgreement`:
the abstract Core-2 predicate holds at the keystone-supplied `errorBound` values, and — the
non-vacuous half — every round's `epsCA_curves` is genuinely bounded by `kᵢ · errorBound i`. -/
theorem perRoundProximityGap_of_curveFamilyData {n : ℕ}
    (k deg : Fin n → ℕ) (degNeZero : ∀ i, NeZero (deg i))
    (domain : Fin n → (ι ↪ F)) (δ : Fin n → ℝ≥0)
    (hδ : ∀ i, δ i < 1 - ReedSolomon.sqrtRate (deg i) (domain i))
    (hInput : ∀ i, CurveFamilyProducer (k i) (deg i) (domain i) (δ i)) :
    Core2Keystone.PerRoundProximityGap
        (fun i => errorBound (δ i) (deg i) (domain i))
        (fun i => errorBound (δ i) (deg i) (domain i)) ∧
      (∀ i, epsCA_curves (F := F) (ReedSolomon.code (domain i) (deg i) : Set (ι → F))
          (k i) (δ i) (δ i) ≤
        ((k i * errorBound (δ i) (deg i) (domain i) : ℝ≥0) : ENNReal)) :=
  Core2Keystone.perRoundProximityGap_of_correlatedAgreement
    (roundKeystoneData_of_curveFamilyData k deg degNeZero domain δ hδ hInput)

/-- **Transfer form: any independently declared accounting error `e` agreeing with the keystone
`errorBound` values is discharged with the numeric guarantee.**  This is the form the FRI/STIR
accounting (`foldBudget_le_of_keystone`) consumes: `e i` is the accounting `roundError`, and the
faithful keystone certifies it per round. -/
theorem perRoundProximityGap_transfer_of_curveFamilyData {n : ℕ}
    (k deg : Fin n → ℕ) (degNeZero : ∀ i, NeZero (deg i))
    (domain : Fin n → (ι ↪ F)) (δ : Fin n → ℝ≥0)
    (hδ : ∀ i, δ i < 1 - ReedSolomon.sqrtRate (deg i) (domain i))
    (hInput : ∀ i, CurveFamilyProducer (k i) (deg i) (domain i) (δ i))
    (e : Fin n → ℝ≥0) (he : ∀ i, e i = errorBound (δ i) (deg i) (domain i)) :
    Core2Keystone.PerRoundProximityGap e
        (fun i => errorBound (δ i) (deg i) (domain i)) ∧
      (∀ i, epsCA_curves (F := F) (ReedSolomon.code (domain i) (deg i) : Set (ι → F))
          (k i) (δ i) (δ i) ≤ ((k i * e i : ℝ≥0) : ENNReal)) :=
  Core2Keystone.perRoundProximityGap_transfer
    (roundKeystoneData_of_curveFamilyData k deg degNeZero domain δ hδ hInput) e he

/-- **Per-round proximity-gap (`epsPG`) bound from the faithful front door, `k = 1`.**  The
ABF26 Fact-4.5 chain `epsPG ≤ epsCA = epsCA_curves(k=1) ≤ 1 · errorBound`
(`Core2Keystone.keystone_epsPG_bound`), with both residual slots filled by the faithful
producer (strict slot) and the strict-regime vacuity (boundary slot). -/
theorem perRound_epsPG_bound_of_curveFamilyData {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : CurveFamilyProducer 1 deg domain δ) :
    epsPG (F := F) (ReedSolomon.code domain deg : Set (ι → F)) δ ≤
      ((1 * errorBound δ deg domain : ℝ≥0) : ENNReal) :=
  Core2Keystone.keystone_epsPG_bound
    (strictCoeffPolysResidual_of_curveFamilyData hInput)
    (boundaryProbabilityResidual_of_strict hδ)
    (le_of_lt hδ)

/-! ## §3. Brick 3b — the genuine STIR accounting hypothesis, faithful entrance -/

/-- **STIR `PerRoundProximityGap` + fold budget + non-vacuity, from the faithful front door.**
Discharges the genuine in-tree STIR accounting hypothesis family
(`ArkLib.ProofSystem.Stir.ErrorAccumulation.PerRoundProximityGap`) with the keystone-supplied
`errorBound` values, bounds the fold budget via the PROVEN `foldBudget_le_of_keystone`, and —
the non-vacuous certificate — proves each accounting error genuinely dominates (up to `kᵢ`) the
round's curve CA error via the faithful keystone. -/
theorem stir_perRound_foldBudget_of_curveFamilyData {n : ℕ}
    (k deg : Fin n → ℕ) (degNeZero : ∀ i, NeZero (deg i))
    (domain : Fin n → (ι ↪ F)) (δ : Fin n → ℝ≥0)
    (hδ : ∀ i, δ i < 1 - ReedSolomon.sqrtRate (deg i) (domain i))
    (hInput : ∀ i, CurveFamilyProducer (k i) (deg i) (domain i) (δ i))
    (e : Fin n → ℝ≥0) (he : ∀ i, e i = errorBound (δ i) (deg i) (domain i))
    (ε : ℝ≥0) (hbound : ∀ i, errorBound (δ i) (deg i) (domain i) ≤ ε) :
    _root_.ArkLib.ProofSystem.Stir.ErrorAccumulation.PerRoundProximityGap e
        (fun i => errorBound (δ i) (deg i) (domain i)) ∧
      _root_.ArkLib.ProofSystem.Stir.ErrorAccumulation.foldBudget e ≤ (n : ℝ≥0) * ε ∧
      (∀ i, epsCA_curves (F := F) (ReedSolomon.code (domain i) (deg i) : Set (ι → F))
          (k i) (δ i) (δ i) ≤ ((k i * e i : ℝ≥0) : ENNReal)) := by
  refine ⟨he, ?_, fun i => ?_⟩
  · exact _root_.ArkLib.ProofSystem.Stir.ErrorAccumulation.foldBudget_le_of_keystone e
      (fun i => errorBound (δ i) (deg i) (domain i)) ε he hbound
  · rw [he i]
    exact roundKeystoneData_curves_bound_of_curveFamilyData k deg degNeZero domain δ hδ hInput i

end General

/-! ## §4. Brick 3a — the FRI per-round `roundError` slot, faithful entrance -/

section Fri

open OracleSpec OracleComp ProtocolSpec Domain

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-- **The FRI per-round proximity-gap input from the faithful front door.**  For the `i`-th
fold round (parameters `N`, `dom`, `degBound` exactly as in `Fri.Spec.roundError`), the curve
correlated-agreement error of the round's Reed–Solomon code is bounded by `κ · roundError i`,
from a faithful curve-family producer at the round parameters.  This is the satisfiable
replacement for `Fri.Spec.perRound_epsCA_le_roundError_of_card_le` (which requires the vacuous
small-field condition `|F| ≤ κ · 2^(n−N)`): since `roundError` is definitionally the BCIKS20
`errorBound` at the round parameters, this is `keystone_curves_bound_of_curveFamilyData`
instantiated per round. -/
theorem friPerRound_epsCA_le_roundError_of_curveFamilyData
    (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+) {ω : SmoothCosetFftDomain n F}
    (δ : ℝ≥0) (i : Fin k) (κ : ℕ)
    (N : ℕ) (hN : N = ∑ j' ∈ finRangeTo (k + 1) (Fin.last i.castSucc.val).val, (s j').1)
    (degBound : ℕ) (hdeg : degBound = 2 ^ ((∑ j', (s j').1) - N) * d.1)
    [NeZero degBound]
    (hδ : δ < 1 - ReedSolomon.sqrtRate degBound
      ((↑(ω.subdomain N) : Fin (2 ^ (n - N)) ↪ F)))
    (hInput : CurveFamilyProducer κ degBound
      ((↑(ω.subdomain N) : Fin (2 ^ (n - N)) ↪ F)) δ) :
    epsCA_curves (F := F)
        (ReedSolomon.code ((↑(ω.subdomain N) : Fin (2 ^ (n - N)) ↪ F)) degBound
          : Set (Fin (2 ^ (n - N)) → F)) κ δ δ
      ≤ ((κ * Fri.Spec.roundError k s d (ω := ω) δ i : ℝ≥0) : ENNReal) := by
  have hre : Fri.Spec.roundError k s d (ω := ω) δ i
      = errorBound δ degBound ((↑(ω.subdomain N) : Fin (2 ^ (n - N)) ↪ F)) := by
    subst hN hdeg
    rfl
  rw [hre]
  exact keystone_curves_bound_of_curveFamilyData hδ hInput

end Fri

end RoundConsumers

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FaithfulCurveExtraction.RoundConsumers.CurveFamilyProducer
#print axioms ArkLib.FaithfulCurveExtraction.RoundConsumers.boundaryProbabilityResidual_of_strict
#print axioms ArkLib.FaithfulCurveExtraction.RoundConsumers.roundKeystoneData_of_curveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.RoundConsumers.roundKeystoneData_curves_bound_of_curveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.RoundConsumers.perRoundProximityGap_of_curveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.RoundConsumers.perRoundProximityGap_transfer_of_curveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.RoundConsumers.perRound_epsPG_bound_of_curveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.RoundConsumers.stir_perRound_foldBudget_of_curveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.RoundConsumers.friPerRound_epsCA_le_roundError_of_curveFamilyData
