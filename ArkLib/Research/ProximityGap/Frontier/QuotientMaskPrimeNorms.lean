/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuotientMaskLocator
import ArkLib.Research.ProximityGap.Frontier.NamedProductionLists

/-! # Signed locator factors at the two named order-64 roots -/

namespace ProximityGap.QuotientMaskPrimeNorms
open QuotientMaskLocator

namespace First
open ArkLib.ProximityGap.PrizeShapePrimeP30
local instance : Fact P.Prime := ⟨prime_P⟩

abbrev root : ZMod P := 321066668146402433440778728016715546214271526818

theorem root_eq : (NamedProductionLists.First.generator : ZMod P)^16777216 = root := by
  change g^16777216 = root
  decide +kernel

theorem order_factors : root^64=1 ∧ root^32= -1 := by decide +kernel

theorem valid : Valid root := by
  unfold Valid
  decide +kernel

#print axioms valid
end First

namespace Second
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
local instance : Fact P.Prime := ⟨prime_P⟩

abbrev root : ZMod P := 253714559090991542023132635617443420377057434819

theorem root_eq : (NamedProductionLists.Second.generator : ZMod P)^16777216 = root := by
  change g^16777216 = root
  decide +kernel

theorem order_factors : root^64=1 ∧ root^32= -1 := by decide +kernel

theorem valid : Valid root := by
  unfold Valid
  decide +kernel

#print axioms valid
end Second

end ProximityGap.QuotientMaskPrimeNorms
