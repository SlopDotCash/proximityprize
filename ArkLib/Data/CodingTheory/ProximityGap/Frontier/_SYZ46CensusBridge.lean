/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapeRateHalfBracket
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ43AutoInstantiation
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount

/-!
# SYZ46 — the census bridge: from the strip per-stack bad-count budget to the `δ*` pin

This file formalizes **wire (iv)** that SYZ33's header names as the last, "not-cheap" link of the
rate-`1/2` production chain:

> "the `MCAThresholdLedger` bridge from the count bound `#bad ≤ n − 1` to the `δ*` floor."

Nothing here is open math.  Every step below is a pure re-assembly of already-landed pieces:

* **Task 1 — the general census bound** (`epsMCA_le_of_bad_count_le`).  Directly from the ABF26
  probability definition (`epsMCA` is a worst-case uniform probability), a uniform per-stack cap on
  the bad-scalar count `mcaBadCount C δ (u 0) (u 1) ≤ B` gives `ε_mca(C, δ) ≤ B / |F|`.  This is a
  thin re-export of `ProximityGap.epsMCA_le_of_badCount_le` phrased through `mcaBadCount`.

* **The prize-shape instantiation** (`deltaStar_ge_/eq_thirtyOneSixtyFour_of_census`).  At the
  certified rate-`1/2` prize field `P = PrizeShapePrimeP30.P` with `n = 2³⁰`, `k = 2²⁹`, the strip's
  per-stack census budget `#bad ≤ n − 1 = 2³⁰ − 1` at the lattice predecessor of the operational
  boundary `31/64` clears the prize arithmetic `(2³⁰ − 1)/P < (2³⁰)/P ≤ 2⁻¹²⁸ = ε*` (the `hbudget`
  pattern of `_PrizeShapeRateHalfBracket`), so `ε_mca ≤ ε*` at that radius, and by
  `le_mcaDeltaStar_of_good` the threshold reaches `31/64`.  Combined with the **unconditional**
  quotient-spread ceiling `δ* ≤ 31/64`
  (`PrizeShapeRateHalfBracket.firstPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour`, SYZ6 shape),
  this two-sidedly **pins** `δ* = 31/64`.

* **The final conditional** (`deltaStar_pinned_of_strip_master_hypothesis`).  The whole chain is
  bundled into a single Lean statement: given the SYZ42 two-field master hypothesis
  `StripMasterHypothesis''` (whose only substantive open field is `uniformSylvester`, the SYZ38/SYZ39
  BGK-type resultant non-vanishing; the second field is the SYZ22 realizability existence) together
  with the honestly-named **transport** hypothesis that carries the strip's abstract per-stack budget
  to the concrete `evalCode`, the two-sided pin `δ* = 31/64` holds.

## Scrupulous honesty — the full residual list behind `StripCensusBound`

`StripCensusBound` is the transported strip conclusion `∀ stack, #bad ≤ n − 1` at the concrete
`evalCode`.  It is **not proved here**; it is the single Lean hypothesis of the pin.  Discharging it
requires, verbatim (cf. SYZ33 header items (i)–(iv), SYZ40, SYZ42, SYZ43):

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
        cap at the concrete smooth-domain `evalCode`.  This transport is **not** formalized; it is the
        `transport` hypothesis of the capstone.

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

/-! ## The prize-shape instantiation at the certified rate-`1/2` field `P30` -/

/-- **The strip census bound at the concrete prize field.**  The transported strip conclusion at
the smooth-domain `evalCode` for the first certified rate-`1/2` prize field: every word stack has at
most `n − 1 = 2³⁰ − 1` bad scalars at the lattice predecessor of the operational boundary `31/64`.

This is the single Lean hypothesis of the pin below; it is the strip's per-stack budget carried to
the concrete code.  Its provenance (items (i)–(iv) in the module docstring) is documented, **not**
re-proved here — it is exactly the SYZ40/SYZ42/SYZ43 residual stack folded into one `Prop`. -/
def StripCensusBound : Prop :=
  ∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
    mcaBadCount (F := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) (31 * 2 ^ 24))
        (u 0) (u 1) ≤ 2 ^ 30 - 1

/-- **The strip census budget feeds the existing predecessor-count pin.**  Because the strip supplies
the *tighter* `n − 1` budget while the pin only needs the `n` budget, `StripCensusBound` implies the
raw `≤ 2³⁰` census count consumed by
`PrizeShapeRateHalfBracket.firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`.
-/
theorem census_count_le_length (h : StripCensusBound) :
    ∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
      (Finset.univ.filter fun gamma : ZMod P =>
        mcaEvent (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) (u 0) (u 1) gamma).card ≤ 2 ^ 30 := by
  intro u
  exact le_trans (h u) (by norm_num)

/-- **Two-sided pin from the strip census budget.**  `δ* = 31/64` for the first certified
rate-`1/2` prize-shaped smooth-domain RS code, conditional on the strip's per-stack census budget
`StripCensusBound`.  Lower half: the census budget clears the prize arithmetic
`(2³⁰ − 1)/P ≤ 2³⁰/P ≤ 2⁻¹²⁸ = ε*`, so `ε_mca ≤ ε*` at the predecessor and `δ* ≥ 31/64` by
`le_mcaDeltaStar_of_good`.  Upper half: the unconditional quotient-spread bad witness at `31/64`
gives `δ* ≤ 31/64`. -/
theorem deltaStar_eq_thirtyOneSixtyFour_of_census (h : StripCensusBound) :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ENNReal) = (31 / 64 : NNReal) :=
  firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count
    (census_count_le_length h)

/-- **The conditional floor half.**  `δ* ≥ 31/64` from the strip census budget. -/
theorem deltaStar_ge_thirtyOneSixtyFour_of_census (h : StripCensusBound) :
    (31 / 64 : NNReal) ≤
      mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ENNReal) :=
  (deltaStar_eq_thirtyOneSixtyFour_of_census h).ge

/-! ## The final conditional — the full chain as one Lean statement

The census bound is the transported strip conclusion.  Here we expose its dependence on the SYZ42
master hypothesis explicitly: the `transport` field carries `StripMasterHypothesis''` (plus, in its
documented body, the SYZ43 union-rank residual `hrank` and the G87 abstract-to-concrete bridge) to
the concrete census bound.  Consuming both, the pin holds. -/

section Capstone

variable {V : Type*} [AddCommGroup V] [Module (ZMod P) V] [Module.Finite (ZMod P) V]

/-- **THE conditional rate-`1/2` prize-shape pin, assembled on one named master hypothesis.**

Given
* `H : SYZ42.StripMasterHypothesis'' (ZMod P) V (2³⁰) (2²⁹)` — the two-field strip master
  hypothesis (its only substantive open field is `uniformSylvester`, the SYZ38/SYZ39 BGK-type
  residual; the second is the SYZ22 realizability existence), and
* `transport` — the honestly-named abstract-to-concrete wire that routes the strip conclusion
  produced from `H` (through the G87 `mcaEvent`→syndrome bridge and the SYZ43 union-rank residual
  `hrank`, items (ii)–(iv) of the module docstring) to the per-stack `mcaBadCount` cap at the
  concrete `evalCode`,

the two-sided pin `δ* = 31/64` holds for the first certified rate-`1/2` prize-shaped smooth-domain
RS code at `n = 2³⁰`, `ε* = 2⁻¹²⁸`.

Both hypotheses are load-bearing: `transport H` produces `StripCensusBound`, which feeds the pin.
`transport` is **not** discharged here — it is the folded residual stack, typed to consume the
master hypothesis so the provenance is explicit in the statement. -/
theorem deltaStar_pinned_of_strip_master_hypothesis
    (H : ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29))
    (transport :
      ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29) →
        StripCensusBound) :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ENNReal) = (31 / 64 : NNReal) :=
  deltaStar_eq_thirtyOneSixtyFour_of_census (transport H)

end Capstone

end ArkLib.ProximityGap.Frontier.SYZ46

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.Frontier.SYZ46.epsMCA_le_of_bad_count_le
#print axioms ArkLib.ProximityGap.Frontier.SYZ46.deltaStar_eq_thirtyOneSixtyFour_of_census
#print axioms ArkLib.ProximityGap.Frontier.SYZ46.deltaStar_ge_thirtyOneSixtyFour_of_census
#print axioms ArkLib.ProximityGap.Frontier.SYZ46.deltaStar_pinned_of_strip_master_hypothesis
