/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ3OverBudgetStackWitness
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ6FinerGradingCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ43AutoInstantiation
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount

/-!
# SYZ46 — the census bridge: from the strip per-stack bad-count budget to the `δ*` bracket

This file formalizes **wire (iv)** that SYZ33's header names as the last, "not-cheap" link of the
rate-`1/2` production chain:

> "the `MCAThresholdLedger` bridge from the count bound `#bad ≤ n − 1` to the `δ*` floor."

Nothing here is open math.  Every step below is a pure re-assembly of already-landed pieces.

## RETRACTION of the first (vacuous) SYZ46 draft — credit: the SYZ3 witness

The first draft of this file placed the strip census hypothesis at the `31/64`-predecessor radius
`predecessorRadius (2^30) (31·2^24)` and concluded a two-sided pin `δ* = 31/64`.  **That hypothesis
is unsatisfiable**: `_SYZ3OverBudgetStackWitness.lean` (`firstPrime_predecessor_cap_refuted`)
exhibits an explicit degenerate stack with `3·31·2^24 = 1560281088 > 2^30` bad scalars at exactly
that radius, so the draft's conditional was vacuously true — and its conclusion even contradicted
the unconditional SYZ4/SYZ6 ceiling `δ* ≤ 358612991/2^30 ≈ 0.334 < 31/64`.  The retraction is
machine-checked below (`refutedPredecessorCensusBound_is_false`): the old hypothesis is proved
**False**, so nothing may be routed through it.  The strip machinery bounds bad counts at radii
**inside the strip** (`δ < 1/3`), not at the `31/64` predecessor.

## The corrected deliverables

* **Task 1 — the general census bound** (`epsMCA_le_of_bad_count_le`).  Directly from the ABF26
  probability definition (`epsMCA` is a worst-case uniform probability), a uniform per-stack cap on
  the bad-scalar count `mcaBadCount C δ (u 0) (u 1) ≤ B` gives `ε_mca(C, δ) ≤ B / |F|`.  A thin
  re-export of `ProximityGap.epsMCA_le_of_badCount_le` phrased through `mcaBadCount`.

* **`StripCensusBound`** — the transported strip conclusion at the concrete `evalCode`, now at the
  correct radius: the lattice predecessor of `a/n` with `a = 357913941 = (2^30 − 1)/3`, the largest
  numerator with `a/n ≤ 1/3`.  The census radius `(a−1)/n = 357913940/2^30 < 1/3` is strictly
  inside the strip — exactly where the strip theorem's budget `#bad ≤ n − 1` lives.  (The floor
  boundary is the `1/3 − 1/(3n)` shape: `a/n = (2^30 − 1)/(3·2^30) = 1/3 − 1/(3·2^30)`.)

* **The conditional floor** (`deltaStar_ge_stripBoundary_of_census`): census at the strip
  predecessor ⟹ `ε_mca ≤ (2^30 − 1)/P ≤ 2^30/P ≤ 2^-128 = ε*` there (the `hbudget` arithmetic of
  `_PrizeShapeRateHalfBracket`) ⟹ by `latticeBoundary_le_mcaDeltaStar_of_predecessor_good`,
  `δ* ≥ 357913941/2^30 = 1/3 − 1/(3·2^30)`.  **Floor only** — no equality is claimed.

* **The two-sided bracket** (`deltaStar_bracket_of_census`): the conditional floor joined with the
  **unconditional** SYZ6 ceiling (`firstPrime_rateHalf_mcaDeltaStar_le_exact`):

    `357913941/2^30 ≤ δ* ≤ 358612991/2^30`  (both endpoints ≈ 1/3; width `699050/2^30 ≈ 6.5·10⁻⁴`).

* **The final conditional** (`deltaStar_bracket_of_strip_master_hypothesis`).  The whole chain as
  one Lean statement: the SYZ42 two-field master hypothesis `StripMasterHypothesis''` plus the
  honestly-named abstract-to-concrete `transport` yield the bracket.

## Scrupulous honesty — the full residual list behind `StripCensusBound`

`StripCensusBound` is **not proved here**; it is the single Lean hypothesis of the bracket's floor.
Discharging it requires, verbatim (cf. SYZ33 header items (i)–(iv), SYZ40, SYZ42, SYZ43):

  (i)   `StripMasterHypothesis''.uniformSylvester` — `SYZ40.UniformSylvesterInjective (ZMod P) n k`,
        the sole substantive open input (SYZ38 Sylvester injectivity, SYZ39 bounded-height resultant
        non-vanishing, BGK type at `n = 2³⁰`).  This is the spread branch (`m ≥ 4`) of the strip.
  (ii)  the SYZ18 / `twist_pair_indep` disjoint-residual support control (lemma-1 input (a)).
  (iii) `StripMasterHypothesis''.realizabilityCore` — the SYZ22 `SuperadditiveUnion` production-ledger
        join, in generation language; its existence residue is auto-instantiated by any over-budget
        `mcaEvent` stack via the G87 bridge (SYZ43 `realizabilityCore_of_mcaEvent_witnesses`),
        leaving only the union-rank lower bound `hrank`
        (SYZ43 `realizabilityCore_of_overBudget_stack`'s sole hypothesis), which is a **separate**
        residual from `uniformSylvester`.
  (iv)  the abstract-to-concrete transport itself: routing SYZ40's abstract band-triple / union-budget
        strip conclusion, through the G87 `mcaEvent`→syndrome bridge, to the per-stack `mcaBadCount`
        cap at the concrete smooth-domain `evalCode` **at the strip radius**.  Not formalized; it is
        the `transport` hypothesis of the capstone.

The merged branch (`m ≤ 3`) of the strip is already unconditional
(`SYZ40.merged_branch_unconditional`); only the spread branch consumes (i).

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger Code

namespace ArkLib.ProximityGap.Frontier.SYZ46

open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26

/-- The certified first prize field is a field (its modulus is prime). -/
local instance primeFactP30 : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

attribute [local instance] Classical.propDecidable

/-! ## Task 1 — the general census bound (`#bad ≤ B ⟹ ε_mca ≤ B/|F|`) -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The census bound (ABF26 Grand Challenge 1, `poly/q` shape).**  A uniform per-stack cap on the
bad-scalar count `mcaBadCount C δ (u 0) (u 1) ≤ B` gives `ε_mca(C, δ) ≤ B / |F|`, straight from the
worst-case-uniform-probability definition of `epsMCA` (via `epsMCA_eq_iSup_mcaBadCount`).  Thin
`mcaBadCount`-phrased re-export of `ProximityGap.epsMCA_le_of_badCount_le`. -/
theorem epsMCA_le_of_bad_count_le (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (h : ∀ u : WordStack A (Fin 2) ι, mcaBadCount (F := F) C δ (u 0) (u 1) ≤ B) :
    epsMCA (F := F) (A := A) C δ ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  ProximityGap.epsMCA_le_of_badCount_le C δ B h

/-! ## Machine-checked retraction of the first draft's hypothesis -/

/-- **[RETRACTED HYPOTHESIS — provably False, do not use.]**  The first SYZ46 draft's census bound,
placed at the `31/64`-predecessor radius.  Kept only to record its refutation below. -/
def RefutedPredecessorCensusBound : Prop :=
  ∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
    mcaBadCount (F := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) (31 * 2 ^ 24))
        (u 0) (u 1) ≤ 2 ^ 30 - 1

/-- **The first draft's hypothesis is False** — via the explicit SYZ3 over-budget degenerate stack
(`3·31·2^24 = 1560281088 > 2^30` bad scalars at the `31/64` predecessor).  Any conditional routed
through `RefutedPredecessorCensusBound` is vacuous; the `δ* = 31/64` pin of the first draft is
hereby retracted (it also contradicted the unconditional SYZ6 ceiling `δ* ≤ 358612991/2^30`). -/
theorem refutedPredecessorCensusBound_is_false : ¬ RefutedPredecessorCensusBound := by
  intro h
  exact ArkLib.ProximityGap.Frontier.SYZ3OverBudgetStackWitness.firstPrime_predecessor_cap_refuted
    (fun u => le_trans (h u) (by norm_num))

/-! ## The corrected census hypothesis, inside the strip -/

/-- The strip lattice numerator: `a = 357913941 = (2^30 − 1)/3`, the largest `a` with
`a/2^30 ≤ 1/3`.  The census radius is its predecessor `(a − 1)/2^30 = 357913940/2^30 < 1/3`,
strictly inside the strip; the resulting floor boundary is `a/2^30 = 1/3 − 1/(3·2^30)`. -/
def stripNumerator : ℕ := 357913941

/-- **The strip census bound at the concrete prize field (corrected radius).**  The transported
strip conclusion at the smooth-domain `evalCode` for the first certified rate-`1/2` prize field:
every word stack has at most `n − 1 = 2^30 − 1` bad scalars at the strip lattice predecessor
`357913940/2^30 < 1/3`.

This is the single Lean hypothesis of the bracket's floor below; it is the strip's per-stack budget
carried to the concrete code, **at a radius the strip machinery actually covers** (`δ < 1/3`).  Its
provenance (items (i)–(iv) in the module docstring) is documented, **not** re-proved here.  Unlike
the retracted `31/64`-predecessor variant, no in-tree witness refutes it. -/
def StripCensusBound : Prop :=
  ∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
    mcaBadCount (F := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) stripNumerator)
        (u 0) (u 1) ≤ 2 ^ 30 - 1

/-! ## The conditional floor and the two-sided bracket -/

/-- **The conditional floor.**  Census at the strip predecessor ⟹
`δ* ≥ 357913941/2^30 = 1/3 − 1/(3·2^30)`.  Chain: the census budget clears the prize arithmetic
`(2^30 − 1)/P ≤ 2^30/P ≤ 2^-128 = ε*` (so `ε_mca ≤ ε*` at the predecessor, by
`epsMCA_le_of_bad_count_le`), then `latticeBoundary_le_mcaDeltaStar_of_predecessor_good` lifts the
good predecessor to the lattice boundary.  **Floor only** — no equality with any ceiling is
claimed. -/
theorem deltaStar_ge_stripBoundary_of_census (h : StripCensusBound) :
    ((stripNumerator : ℕ) : NNReal) / ((2 ^ 30 : ℕ) : NNReal) ≤
      mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ENNReal) := by
  letI : NeZero (2 ^ 30 : Nat) := ⟨by norm_num⟩
  have hbudget : ((2 ^ 30 : Nat) : ENNReal) /
      (Fintype.card (ZMod P) : ENNReal) ≤ (ProximityGap.epsStar : ENNReal) := by
    rw [ZMod.card]
    have hb := natCast_div_le_inv_of_mul_le (E := 2 ^ 30) (Q := 2 ^ 128) (p := P)
      (by norm_num) prime_P.pos (by norm_num)
    rwa [epsStar_coe_eq_natCast_inv]
  have hcount : ∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
      mcaBadCount (F := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (predecessorRadius (2 ^ 30) stripNumerator)
          (u 0) (u 1) ≤ 2 ^ 30 :=
    fun u => le_trans (h u) (by norm_num)
  have hprev : epsMCA (F := ZMod P) (A := ZMod P)
      (evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) stripNumerator) ≤ (ProximityGap.epsStar : ENNReal) :=
    le_trans
      (epsMCA_le_of_bad_count_le
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) stripNumerator) (2 ^ 30) hcount)
      hbudget
  exact latticeBoundary_le_mcaDeltaStar_of_predecessor_good
    (F := ZMod P) (n := 2 ^ 30) (a := stripNumerator)
    (by norm_num [stripNumerator]) (by norm_num [stripNumerator])
    (evalCode g (2 ^ 30) (2 ^ 29 - 1)) (ProximityGap.epsStar : ENNReal) hprev

/-- **The two-sided bracket from the strip census budget.**  The conditional floor joined with the
**unconditional** SYZ6 finer-grading ceiling:

  `357913941/2^30 ≤ δ* ≤ 358612991/2^30`

(both endpoints ≈ `1/3`: the floor is `1/3 − 1/(3·2^30)`, the ceiling ≈ `0.33398`; bracket width
`699050/2^30 ≈ 6.5·10⁻⁴`).  Only the floor consumes `StripCensusBound`. -/
theorem deltaStar_bracket_of_census (h : StripCensusBound) :
    (357913941 : NNReal) / (2 ^ 30 : NNReal) ≤
        mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ∧
      mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ≤ (358612991 : NNReal) / (2 ^ 30 : NNReal) := by
  constructor
  · have hfloor := deltaStar_ge_stripBoundary_of_census h
    convert hfloor using 2 <;> norm_num [stripNumerator]
  · exact
      ArkLib.ProximityGap.Frontier.SYZ6FinerGradingCeiling.firstPrime_rateHalf_mcaDeltaStar_le_exact

/-! ## The final conditional — the full chain as one Lean statement

The census bound is the transported strip conclusion.  Here we expose its dependence on the SYZ42
master hypothesis explicitly: the `transport` field carries `StripMasterHypothesis''` (plus, in its
documented body, the SYZ43 union-rank residual `hrank` and the G87 abstract-to-concrete bridge) to
the concrete census bound at the strip radius.  Consuming both, the bracket holds. -/

section Capstone

variable {V : Type*} [AddCommGroup V] [Module (ZMod P) V] [Module.Finite (ZMod P) V]

/-- **THE conditional rate-`1/2` prize-shape bracket, assembled on one named master hypothesis.**

Given
* `H : SYZ42.StripMasterHypothesis'' (ZMod P) V (2³⁰) (2²⁹)` — the two-field strip master
  hypothesis (its only substantive open field is `uniformSylvester`, the SYZ38/SYZ39 BGK-type
  residual; the second is the SYZ22 realizability existence), and
* `transport` — the honestly-named abstract-to-concrete wire that routes the strip conclusion
  produced from `H` (through the G87 `mcaEvent`→syndrome bridge and the SYZ43 union-rank residual
  `hrank`, items (ii)–(iv) of the module docstring) to the per-stack `mcaBadCount` cap at the
  concrete `evalCode`, at the strip lattice predecessor `357913940/2^30 < 1/3`,

the two-sided bracket

  `1/3 − 1/(3·2^30) = 357913941/2^30 ≤ δ* ≤ 358612991/2^30 ≈ 0.33398`

holds for the first certified rate-`1/2` prize-shaped smooth-domain RS code at `n = 2³⁰`,
`ε* = 2⁻¹²⁸`.  The ceiling half is unconditional (SYZ6); only the floor half consumes the
hypotheses.  No equality (`δ*` pin) is claimed — the residual width `699050/2^30` is the honest
remaining lattice/grading gap. -/
theorem deltaStar_bracket_of_strip_master_hypothesis
    (H : ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29))
    (transport :
      ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29) →
        StripCensusBound) :
    (357913941 : NNReal) / (2 ^ 30 : NNReal) ≤
        mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ∧
      mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ≤ (358612991 : NNReal) / (2 ^ 30 : NNReal) :=
  deltaStar_bracket_of_census (transport H)

end Capstone

end ArkLib.ProximityGap.Frontier.SYZ46

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.Frontier.SYZ46.epsMCA_le_of_bad_count_le
#print axioms ArkLib.ProximityGap.Frontier.SYZ46.refutedPredecessorCensusBound_is_false
#print axioms ArkLib.ProximityGap.Frontier.SYZ46.deltaStar_ge_stripBoundary_of_census
#print axioms ArkLib.ProximityGap.Frontier.SYZ46.deltaStar_bracket_of_census
#print axioms ArkLib.ProximityGap.Frontier.SYZ46.deltaStar_bracket_of_strip_master_hypothesis
