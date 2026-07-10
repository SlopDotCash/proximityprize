/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSaturatedSafeEvents
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSaturatedUnsafeEvents

/-!
# Saturated P1 common-factor construction

Compatibility module for the saturated core and its safe and unsafe event
certificates. The declarations retain their original namespace and names.
-/

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstruction
#print axioms amplifiedCoreSet_card
#print axioms amplified_core_pair_agreement
#print axioms saturated_safe_mcaEvent
#print axioms saturated_unsafe_mcaEvent
