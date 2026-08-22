/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ57TransportWire

/-!
# SYZ60 (part A) — collapsing the counting dictionary to a single bad-count ceiling

SYZ57 reduced wire (iv) to `SYZ57Transport.CountingDictionary`:

    `∀ u, ∃ Ucard, 2²⁹ ≤ Ucard ∧ Ucard ≤ 2³⁰ ∧ mcaBadCount … (u 0)(u 1) ≤ Ucard`.

This asks, per stack `u`, for an *admissible band member* `Ucard ∈ [2²⁹, 2³⁰]` dominating the concrete
bad-scalar count.  The band's **upper** edge `2³⁰` is itself admissible (`2²⁹ ≤ 2³⁰ ≤ 2³⁰`), so the
existential collapses: choosing `Ucard = 2³⁰` discharges the band membership *unconditionally*, and
the only surviving content is that the bad count never exceeds `2³⁰`.  We name that residual

    `BadCountCeiling : ∀ u, mcaBadCount … (u 0)(u 1) ≤ 2³⁰`

and prove `BadCountCeiling → CountingDictionary` (`countingDictionary_of_badCountCeiling`).  So the
whole per-stack "produce a dominating admissible union cardinality" obligation shrinks to the plain
scalar inequality "the bad count is at most `2³⁰`".

## What supplies the ceiling (the traced wire, not discharged here)

`BadCountCeiling` is exactly the target of the SYZ29 accounting route:

* `SYZ29.bad_card_le_pool_of_attribution` : `#B ≤ Σᵢ |Tᵢ|` — once every bad scalar is *core-attributed*
  (it is a root `d₀ + γ d₁ = 0` on some core's witness support `Tᵢ`, `mem_pencilImage_of_root`),
  the bad set is covered by the `D` per-core witness images, whose support sizes sum to the pool;
* `SYZ29.bad_card_le_pool_add_fresh` + `SYZ30.fresh_card_le_codim` /
  `SYZ31.fresh_card_le_codim_of_private_coord` bound the *fresh* (unattributed) remainder by a
  codimension;
* `SYZ18.no_two_bad_scalars_share_witness` gives scalar↦support injectivity (no double counting);
* `SYZ56.cross_witness_region_card_ge` controls witness-support overlaps.

Their conjunction yields `#B ≤ 2³⁰` provided the concrete `mcaBadCount` at `evalCode g (2³⁰)(2²⁹−1)`
is identified with the SYZ29 root set `B` through the **G87 `mcaEvent`→syndrome→pencil bridge** — the
one concrete identification Mathlib/​the substrate does not yet provide.  That bridge is the genuine,
now-isolated residual; it is *named*, not absorbed.  This file does **not** close `δ*`.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger Code

namespace ArkLib.ProximityGap.Frontier.SYZ60Dictionary

open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.SYZ46
open ArkLib.ProximityGap.Frontier.SYZ57Transport

/-- The certified first prize field is a field (its modulus is prime). -/
local instance primeFactP30 : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

/-- **The bad-count ceiling — part A's single surviving residual.**  For every concrete word stack
`u`, the bad-scalar count at the smooth-domain `evalCode` is at most the band's upper edge `2³⁰`.
This is the SYZ29 accounting conclusion `#B ≤ Σᵢ|Tᵢ| ≤ 2³⁰` transported through the G87
`mcaEvent`→syndrome→pencil bridge (the isolated open identification). -/
def BadCountCeiling : Prop :=
  ∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
    mcaBadCount (F := ZMod P)
      (evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) stripNumerator)
      (u 0) (u 1) ≤ 2 ^ 30

/-- **The dictionary collapses to the ceiling.**  Choosing the admissible band's *upper* edge
`Ucard = 2³⁰` discharges the two band-membership conjuncts of `CountingDictionary` outright, leaving
exactly the domination `mcaBadCount … ≤ 2³⁰`.  Hence the per-stack "exhibit a dominating admissible
union cardinality" obligation is *equivalent to* the plain ceiling `BadCountCeiling`. -/
theorem countingDictionary_of_badCountCeiling (h : BadCountCeiling) : CountingDictionary := by
  intro u
  refine ⟨2 ^ 30, ?_, le_rfl, h u⟩
  norm_num

/-- The reduction is in fact an equivalence: the ceiling is *necessary* too (take the witnessed
`Ucard ≤ 2³⁰` and compose with the domination), so no content is lost by naming `BadCountCeiling` as
the residual. -/
theorem badCountCeiling_of_countingDictionary (h : CountingDictionary) : BadCountCeiling := by
  intro u
  obtain ⟨Ucard, _, hUn, hbad⟩ := h u
  exact le_trans hbad hUn

/-- `CountingDictionary ↔ BadCountCeiling`: the whole counting dictionary is precisely the bad-count
ceiling. -/
theorem countingDictionary_iff_badCountCeiling : CountingDictionary ↔ BadCountCeiling :=
  ⟨badCountCeiling_of_countingDictionary, countingDictionary_of_badCountCeiling⟩

section Wire

variable {V : Type*} [AddCommGroup V] [Module (ZMod P) V] [FiniteDimensional (ZMod P) V]

/-- **The transport wire, re-expressed against the ceiling.**  Identical to
`SYZ57Transport.stripCensusBound_of_master_hypothesis` but consuming the collapsed residual
`BadCountCeiling` in place of the full `CountingDictionary`. -/
theorem stripCensusBound_of_badCountCeiling
    (H : ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29))
    (ceil : BadCountCeiling) :
    StripCensusBound :=
  stripCensusBound_of_master_hypothesis H (countingDictionary_of_badCountCeiling ceil)

/-- **The rate-`1/2` prize bracket, transport gap collapsed to the ceiling.**  Identical conclusion
to `SYZ57Transport.deltaStar_bracket_of_master_hypothesis`, but the opaque counting dictionary is
replaced by the single scalar residual `BadCountCeiling` (bad count `≤ 2³⁰`). -/
theorem deltaStar_bracket_of_badCountCeiling
    (H : ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29))
    (ceil : BadCountCeiling) :
    (357913941 : NNReal) / (2 ^ 30 : NNReal) ≤
        mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ∧
      mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ≤ (358612991 : NNReal) / (2 ^ 30 : NNReal) :=
  deltaStar_bracket_of_master_hypothesis H (countingDictionary_of_badCountCeiling ceil)

end Wire

end ArkLib.ProximityGap.Frontier.SYZ60Dictionary

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.Frontier.SYZ60Dictionary.countingDictionary_iff_badCountCeiling
#print axioms ArkLib.ProximityGap.Frontier.SYZ60Dictionary.stripCensusBound_of_badCountCeiling
#print axioms ArkLib.ProximityGap.Frontier.SYZ60Dictionary.deltaStar_bracket_of_badCountCeiling
