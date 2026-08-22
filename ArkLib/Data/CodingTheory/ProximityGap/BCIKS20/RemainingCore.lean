/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffLargeReduction
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardStrictInteriorRefutation

/-!
# Issue #304 — the remaining debt as ONE named Prop: `BCIKS20RemainingCore`

The [BCIKS20] Theorem 1.5 keystone (`correlatedAgreement_affine_curves`) was reduced to two
open obligations by two independent passes:

* **the large-sector strict-coefficient residual** (`StrictCoeffPolysLargeResidual`,
  `StrictCoeffLargeReduction.lean`): the §5 strict-Johnson extraction restricted to good sets of
  size `> k + 1` — the complementary sector is *free* (pure Lagrange interpolation; the cutoff
  is exact, probed in `scripts/probes/probe_strict_coeff_smallset.py`, 1861/2000 generic
  failures at `card = k + 2` over GF(13));
* **the corrected boundary threshold** (`BoundaryCardStrictInteriorRefutation.lean`,
  `BoundaryThresholdFloorCell.lean`): both nonemptiness leaves of the boundary quantization
  split are *false* (kernel-checked witnesses), and the honest closed-boundary export is the
  §5 statement at a **floor-matched strict** radius `δ'`, transported to the boundary with
  `ε = errorBound δ' > 0` — never the refuted `errorBound (1 − √ρ) = 0`
  (probed in `scripts/probes/probe_boundary_strict_interior.py` and exhaustively at
  `q = 5, n = 4, k = 1` in `scripts/probes/probe_boundary_threshold_floorcell.py`:
  390,625 stacks, threshold fired on 60,625, 0 violations).

This file unifies the two into a single named Prop and a single consuming theorem:

* `BCIKS20RemainingCore k deg domain δ δ'` — the conjunction
  `StrictCoeffPolysLargeResidual δ ∧ StrictCoeffPolysLargeResidual δ'`: the large-sector
  residual at the target radius `δ` (carrying the strict-interior regime) and at the
  floor-matched working radius `δ'` (carrying the corrected boundary route).  The corrected
  boundary threshold *reduces* to the second conjunct: at a strict radius the §6.2 boundary
  residual is vacuous (`¬ δ' < 1 − √ρ` is unreachable), so the O70 front door turns the
  large-sector residual at `δ'` into the full §5 statement at `δ'`, and the O76 floor
  transport carries it to the boundary.
* `correlatedAgreement_of_remainingCore` — **the wiring theorem**: `BCIKS20RemainingCore`
  implies the Theorem 1.5 keystone `δ_ε_correlatedAgreementCurves` at `δ` with
  `ε = max (errorBound δ) (errorBound δ')`.  In the strict interior the max is realized by the
  first conjunct at `ε = errorBound δ` (the literal in-tree Theorem 1.5 shape); at the closed
  boundary `errorBound δ = 0` and the max is the honest O76 export `ε = errorBound δ' > 0`.

Joint satisfiability of the side hypotheses (the conjunction is not demanded in an empty
regime) is probed exactly in `scripts/probes/probe_remaining_core_wiring.py` (exit 0):
8,255 grid points `(n, deg)`, all 8,113 non-lattice boundaries admit the canonical
floor-matched strict `δ' = ⌊δ·n⌋/n` with `errorBound δ' > 0`, lattice boundaries are honestly
excluded (no strict floor-matched radius exists there — that branch stays behind
`BoundaryCardLatticeData`), and the O76 witness reproduces to the digit
(`δ' = 1/4`, `k · errorBound δ' = 4/5`).  Formal satisfiability at the closed boundary is
certified in-tree below (`remainingCore_boundary_witness`), with the honest caveat that at toy
field size both Johnson-branch obligations hold vacuously — the genuine §5 content is a
large-`q` phenomenon.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, §6.2.
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode ProbabilityTheory ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The one remaining Prop of issue #304.**  The conjunction of the two reduced open
obligations behind the [BCIKS20] Theorem 1.5 keystone:

1. `StrictCoeffPolysLargeResidual` at the target radius `δ` — the §5 strict-Johnson
   extraction on large good sets (O70: the small sector is free Lagrange interpolation);
2. `StrictCoeffPolysLargeResidual` at the working radius `δ'` — intended floor-matched and
   strictly below the Johnson boundary, where it carries the **corrected boundary threshold**
   (O76/O78): the §6.2 boundary residual is vacuous at strict radii, so this conjunct alone
   produces the full §5 statement at `δ'`, which floor-transports to the closed boundary with
   the honest `ε = errorBound δ' > 0`.

Producers discharge `#304` by proving exactly this Prop; consumers obtain Theorem 1.5 through
`correlatedAgreement_of_remainingCore`.  In the strict interior, instantiate with `δ' = δ`
(the floor match is `rfl`) and the two conjuncts coincide. -/
def BCIKS20RemainingCore (k deg : ℕ) (domain : ι ↪ F) (δ δ' : ℝ≥0) : Prop :=
  StrictCoeffPolysLargeResidual (k := k) (deg := deg) (domain := domain) (δ := δ) ∧
    StrictCoeffPolysLargeResidual (k := k) (deg := deg) (domain := domain) (δ := δ')

omit [Nonempty ι] [DecidableEq ι] in
/-- `δ_ε_correlatedAgreementCurves` is antitone in the error parameter: weakening `ε` upward
only strengthens the probability premise. -/
theorem correlatedAgreementCurves_mono_eps {k : ℕ} {C : Set (ι → F)} {δ ε ε' : ℝ≥0}
    (hε : ε ≤ ε')
    (hCA : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι) C δ ε) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι) C δ ε' :=
  fun u hu =>
    hCA u (lt_of_le_of_lt (mul_le_mul_right (by exact_mod_cast hε) _) hu)

/-- **Strict-interior branch.**  In the open Johnson regime `δ < 1 − √ρ` the first conjunct of
`BCIKS20RemainingCore` already yields the literal Theorem 1.5 statement at `δ`: the §6.2
boundary residual is vacuous there (its branch hypothesis `¬ δ < 1 − √ρ` is unreachable, cf.
`ArkLib.FaithfulCurveExtraction.RoundConsumers.boundaryProbabilityResidual_of_strict`), so the
O70 front door fires on the large-sector residual alone. -/
theorem correlatedAgreementCurves_strict_of_remainingCore {k deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hCore : BCIKS20RemainingCore k deg domain δ δ') :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_largeResidual (k := k) (deg := deg)
    (domain := domain) (δ := δ) hCore.1
    (fun _hk _u _hprob _hJ hnot => absurd hδ hnot) hδ.le

/-- **Corrected-boundary branch.**  The second conjunct of `BCIKS20RemainingCore` at a
floor-matched radius `δ'` strictly below the Johnson boundary yields the correlated-agreement
statement at the target `δ` with the working radius's error `ε = errorBound δ'`: the O70 front
door produces the §5 statement at `δ'` (boundary residual vacuous at strict radii), and the
O76 step-function transport carries it across the floor cell.  Taking `δ = 1 − √ρ` non-lattice
and `δ' = ⌊δ·n⌋/n`, this is the honest closed-boundary export — never the refuted
`errorBound (1 − √ρ) = 0` shape. -/
theorem correlatedAgreementCurves_floorMatched_of_remainingCore {k deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hCore : BCIKS20RemainingCore k deg domain δ δ') :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := errorBound δ' deg domain) :=
  ArkLib.BoundaryQuantizationCorrected.correlatedAgreementCurves_boundary_of_floorEq_strict
    (k := k) (deg := deg) (domain := domain) hfloor
    (correlatedAgreement_affine_curves_of_largeResidual (k := k) (deg := deg)
      (domain := domain) (δ := δ') hCore.2
      (fun _hk _u _hprob _hJ hnot => absurd hδ' hnot) hδ'.le)

/-- **The wiring theorem: `BCIKS20RemainingCore` ⟹ Theorem 1.5.**  The one named Prop yields
the [BCIKS20] correlated-agreement keystone at the target radius `δ` with
`ε = max (errorBound δ) (errorBound δ')`:

* in the strict interior `δ < 1 − √ρ` the first conjunct fires through the O70 front door
  (boundary residual vacuous) at `ε = errorBound δ ≤ max …`;
* otherwise (in particular at the closed boundary `δ = 1 − √ρ`, where
  `errorBound δ = 0`) the second conjunct fires at the floor-matched strict radius and
  transports across the cell at `ε = errorBound δ' ≤ max …` — the corrected boundary route.

Side hypotheses are jointly satisfiable at every non-lattice boundary with the canonical
`δ' = ⌊δ·n⌋/n` (probed over 8,255 grid points, 0 violations:
`scripts/probes/probe_remaining_core_wiring.py`); lattice boundaries admit no strict
floor-matched radius and honestly remain behind the `BoundaryCardLatticeData` branch. -/
theorem correlatedAgreement_of_remainingCore {k deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hCore : BCIKS20RemainingCore k deg domain δ δ') :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := max (errorBound δ deg domain) (errorBound δ' deg domain)) := by
  rcases lt_or_ge δ (1 - ReedSolomon.sqrtRate deg domain) with h | _h
  · exact correlatedAgreementCurves_mono_eps (le_max_left _ _)
      (correlatedAgreementCurves_strict_of_remainingCore h hCore)
  · exact correlatedAgreementCurves_mono_eps (le_max_right _ _)
      (correlatedAgreementCurves_floorMatched_of_remainingCore hδ' hfloor hCore)

end ProximityGap

/-! ## Satisfiability at the closed boundary (the O76 witness instance)

`BCIKS20RemainingCore` is **satisfiable at the closed boundary**: at the O76 witness point
(`ι = Fin 4`, `F = ZMod 5`, `deg = 2`, `k = 1`, `δ = 1 − √(1/2)` non-lattice, canonical
floor-matched `δ' = 1/4`) both conjuncts are theorems.  Honest caveat: both hold *vacuously*
there — at `δ` the strict-Johnson hypothesis `δ < 1 − √ρ` fails, and at `δ' = 1/4` the
Johnson-side hypothesis `(1 − ρ)/2 < δ'` fails (`(1 − 1/2)/2 = 1/4` exactly) — so the toy
instance certifies *consistency* of the conjunction, not its large-`q` content.  The genuine
content of the conclusion at this instance is nonetheless real: the resulting unconditional
export `correlatedAgreementCurves_boundary_witness` asserts the closed-boundary correlated
agreement at threshold `max (0, 4/5) = 4/5`, verified exhaustively over all 390,625 stacks in
`scripts/probes/probe_boundary_threshold_floorcell.py` (threshold fired on 60,625 stacks,
0 violations). -/

namespace ArkLib

namespace RemainingCoreWitness

open ArkLib.BoundaryCardResidualRefutation ArkLib.BoundaryCardStrictInteriorRefutation
  ProximityGap Code NNReal
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The witness Reed–Solomon code has rate exactly `1/2` (`dim 2`, length `4`). -/
theorem rate_eq_half :
    (LinearCode.rate (ReedSolomon.code domain 2) : ℝ≥0) = 1 / 2 := by
  have h := ReedSolomon.rateOfLinearCode_eq_div' (n := 2) (α := domain)
    (by norm_num [I])
  rw [h]
  have hcard : (Fintype.card I : ℚ≥0) = 4 := by norm_num [I]
  rw [hcard]
  norm_num

/-- At the canonical floor-matched radius `δ' = 1/4` the Johnson-side hypothesis
`(1 − ρ)/2 < δ'` fails *exactly*: `(1 − 1/2)/2 = 1/4`. -/
theorem not_johnson_at_quarter :
    ¬ ((1 - (LinearCode.rate (ReedSolomon.code domain 2) : ℝ≥0)) / 2 < (1 / 4 : ℝ≥0)) := by
  rw [rate_eq_half,
    show (1 : ℝ≥0) - 1 / 2 = 1 / 2 from tsub_eq_of_eq_add (by norm_num)]
  norm_num

/-- **`BCIKS20RemainingCore` is satisfiable at the closed boundary.**  At the O76 witness
instance both conjuncts hold (vacuously at toy field size, as documented above): the target
conjunct because `δ = 1 − √ρ` is not strictly below the boundary, the working conjunct because
`δ' = 1/4` sits exactly at the unique-decoding edge `(1 − ρ)/2`.  The side hypotheses of the
wiring theorem hold non-vacuously: `1/4 < 1 − √(1/2)` and the floors match at `1`. -/
theorem remainingCore_boundary_witness :
    ProximityGap.BCIKS20RemainingCore (ι := I) (F := F) 1 2 domain
      (1 - ReedSolomon.sqrtRate 2 domain) (1 / 4 : ℝ≥0) := by
  constructor
  · intro _hk _u _hprob _hJ hsqrt _hcard _P _hP
    exact absurd hsqrt (lt_irrefl _)
  · intro _hk _u _hprob hJ _hsqrt _hcard _P _hP
    exact absurd hJ not_johnson_at_quarter

/-- **Unconditional closed-boundary export at the witness.**  Feeding the satisfiability
witness through the wiring theorem yields an in-tree, hypothesis-free correlated-agreement
statement at the non-lattice boundary `δ = 1 − √(1/2)` with the honest error
`max (errorBound δ) (errorBound (1/4)) = max 0 (4/5) = 4/5` — exhaustively verified
(390,625 stacks, 0 violations) in `scripts/probes/probe_boundary_threshold_floorcell.py`. -/
theorem correlatedAgreementCurves_boundary_witness :
    ProximityGap.δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := I)
      (C := (ReedSolomon.code domain 2 : Set (I → F)))
      (δ := 1 - ReedSolomon.sqrtRate 2 domain)
      (ε := max (ProximityGap.errorBound (1 - ReedSolomon.sqrtRate 2 domain) 2 domain)
        (ProximityGap.errorBound (1 / 4 : ℝ≥0) 2 domain)) :=
  ProximityGap.correlatedAgreement_of_remainingCore quarter_lt_boundary
    floor_quarter_eq_floor_boundary remainingCore_boundary_witness

end RemainingCoreWitness

end ArkLib

/-! ## Axiom audit -/
#print axioms ProximityGap.correlatedAgreementCurves_mono_eps
#print axioms ProximityGap.correlatedAgreementCurves_strict_of_remainingCore
#print axioms ProximityGap.correlatedAgreementCurves_floorMatched_of_remainingCore
#print axioms ProximityGap.correlatedAgreement_of_remainingCore
#print axioms ArkLib.RemainingCoreWitness.remainingCore_boundary_witness
#print axioms ArkLib.RemainingCoreWitness.correlatedAgreementCurves_boundary_witness
