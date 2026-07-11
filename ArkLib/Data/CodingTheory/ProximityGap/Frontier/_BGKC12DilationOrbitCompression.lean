/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKC12TranslateIntersectionReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKLateNewtonTwoColourPhysicalBridge

/-!
# Multiplicative-orbit compression of the late Newton `C12` alignment

Scratch lane for issue #466.  This file studies the exact multiplicative symmetry of the two
physical rows in the translate/intersection factorization of `C12`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKC12DilationOrbitCompression

open ArkLib.ProximityGap.Frontier.BGKLateNewtonSignedCovariance
open ArkLib.ProximityGap.Frontier.BGKC12TranslateIntersectionReduction
open ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge

section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

#check Equiv.subtypeEquiv
#check Equiv.finsetCongr
#check Finset.sum_subtype
#check Fintype.sum_equiv
#check Finset.sum_erase_add

end


end ArkLib.ProximityGap.Frontier.BGKC12DilationOrbitCompression
