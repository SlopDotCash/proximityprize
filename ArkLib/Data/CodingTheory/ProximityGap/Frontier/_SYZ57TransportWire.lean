/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ46CensusBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ42Realizability

/-!
# SYZ57 — the transport wire: reducing SYZ46's opaque `transport` to a named counting dictionary

SYZ46's capstone `deltaStar_bracket_of_strip_master_hypothesis` carries an **opaque** hypothesis

    `transport : StripMasterHypothesis'' (ZMod P) V (2³⁰) (2²⁹) → StripCensusBound`,

the module docstring's wire **(iv)**: "routing SYZ40's abstract union-budget strip conclusion,
through the G87 `mcaEvent`→syndrome bridge, to the per-stack `mcaBadCount` cap at the concrete
`evalCode`.  Not formalized."  This file dissects that black box.

## What the strip theorem actually delivers, and what is missing

SYZ42's `strip_theorem_of_master_hypothesis''` (given `n = 2k`) yields a conjunction whose **second**
component is the abstract union budget

    `∀ Ucard, k ≤ Ucard → Ucard ≤ n → Ucard ≤ n − 1`.                                    (★)

This is a statement about an **abstract union cardinality `Ucard`**, *not* about `mcaBadCount` at the
concrete smooth-domain `evalCode`.  The entire residual content of wire (iv) is therefore the
**counting dictionary**: for each concrete word stack `u`, exhibit a `Ucard` in the admissible band
`k ≤ Ucard ≤ n` that *dominates* the concrete bad-scalar count
`mcaBadCount (evalCode …) (predecessorRadius …) (u 0) (u 1)`.  Producing that `Ucard` is exactly the
G87 `mcaEvent`→syndrome bridge composed with the SYZ29 core-attribution map (the honest open piece:
whether every bad scalar is core-attributed, so that the union it generates lands `≤ n`).

## The deliverable — a strict reduction, not a discharge

* `CountingDictionary` — the precisely-named residual: `∀ u, ∃ Ucard, k ≤ Ucard ∧ Ucard ≤ n ∧
  mcaBadCount … (u 0)(u 1) ≤ Ucard`.  This is *all* that wire (iv) needs beyond the strip theorem.
* `stripCensusBound_of_master_hypothesis` — **the wire, partially closed**:
  `StripMasterHypothesis'' → CountingDictionary → StripCensusBound`.  The `≤ n − 1` half is
  discharged *mechanically* from the strip theorem's (★); only the counting dictionary survives.
* `deltaStar_bracket_of_master_hypothesis` — the SYZ46 bracket, re-derived with the opaque
  `transport` **replaced** by `H` (already present) `+ CountingDictionary`.

So wire (iv) is reduced from an unstructured `H → StripCensusBound` function to the single named
`CountingDictionary` obligation, with the arithmetic budget side proved.  This does **not** close
`δ*`: the counting dictionary (bridge + attribution) is the genuine remaining transport gap, and it
is honestly named here rather than absorbed.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger Code

namespace ArkLib.ProximityGap.Frontier.SYZ57Transport

open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.SYZ46

/-- The certified first prize field is a field (its modulus is prime). -/
local instance primeFactP30 : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

/-- **The counting dictionary — wire (iv)'s single surviving obligation.**

For every concrete word stack `u`, the strip's abstract union budget applies through *some*
admissible union cardinality `Ucard ∈ [k, n]` that dominates the concrete bad-scalar count.
Constructing this `Ucard` is the G87 `mcaEvent`→syndrome bridge composed with the SYZ29
core-attribution map; it is the genuine, isolated transport gap (not proved here). -/
def CountingDictionary : Prop :=
  ∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
    ∃ Ucard : ℕ, 2 ^ 29 ≤ Ucard ∧ Ucard ≤ 2 ^ 30 ∧
      mcaBadCount (F := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) stripNumerator)
        (u 0) (u 1) ≤ Ucard

section Wire

variable {V : Type*} [AddCommGroup V] [Module (ZMod P) V] [FiniteDimensional (ZMod P) V]

/-- **The transport wire, partially closed.**  Given the SYZ42 master hypothesis `H` and the named
`CountingDictionary`, the concrete `StripCensusBound` holds.  The abstract union budget (★) supplied
by `strip_theorem_of_master_hypothesis''` discharges the `≤ n − 1` side *mechanically*; the only
non-arithmetic input consumed is the counting dictionary.  This replaces SYZ46's opaque
`transport : H → StripCensusBound` with `H → CountingDictionary → StripCensusBound`, exposing that
the residual is exactly `CountingDictionary`. -/
theorem stripCensusBound_of_master_hypothesis
    (H : ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29))
    (dict : CountingDictionary) :
    StripCensusBound := by
  -- The abstract union budget (★): `∀ Ucard, 2^29 ≤ Ucard → Ucard ≤ 2^30 → Ucard ≤ 2^30 − 1`.
  have hstrip := (ArkLib.ProximityGap.SYZ42.strip_theorem_of_master_hypothesis''
    (K := ZMod P) (V := V) H (by norm_num)).2
  intro u
  obtain ⟨Ucard, hkU, hUn, hbad⟩ := dict u
  -- strip: Ucard ≤ 2^30 − 1, and the bad count is ≤ Ucard, so ≤ 2^30 − 1.
  exact le_trans hbad (hstrip Ucard hkU hUn)

/-- **The rate-`1/2` prize bracket, transport gap named.**  Identical conclusion to SYZ46's
`deltaStar_bracket_of_strip_master_hypothesis`, but with the opaque `transport` hypothesis
**replaced** by the SYZ42 master hypothesis `H` (already required) together with the single named
`CountingDictionary`.  The floor consumes `H + CountingDictionary`; the ceiling is unconditional
(SYZ6).  No equality (`δ*` pin) is claimed. -/
theorem deltaStar_bracket_of_master_hypothesis
    (H : ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29))
    (dict : CountingDictionary) :
    (357913941 : NNReal) / (2 ^ 30 : NNReal) ≤
        mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ∧
      mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ≤ (358612991 : NNReal) / (2 ^ 30 : NNReal) :=
  deltaStar_bracket_of_census (stripCensusBound_of_master_hypothesis H dict)

end Wire

end ArkLib.ProximityGap.Frontier.SYZ57Transport

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.Frontier.SYZ57Transport.stripCensusBound_of_master_hypothesis
#print axioms ArkLib.ProximityGap.Frontier.SYZ57Transport.deltaStar_bracket_of_master_hypothesis
