/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Compatibility.BiniusChallengeOrder

/-! Two unequal challenges distinguish the canonical and historical storage conventions. -/

namespace ArkLibTest.Compatibility.BiniusChallengeOrder

open Binius.BinaryBasefold

theorem chronological_first :
    getFoldingChallenges (r := 4) (𝓡 := 1) (ϑ := 1)
      (Fin.last 2) ![0, 1] 0 (by decide) 0 = (0 : Nat) := rfl

theorem newestFirst_first :
    Binius.BinaryBasefold.Compatibility.newestFirstFoldingChallenges (r := 4) (𝓡 := 1) (ϑ := 1)
      (Fin.last 2) ![0, 1] 0 (by decide) 0 = (1 : Nat) := rfl

theorem reverse_input_recovers_chronological :
    Binius.BinaryBasefold.Compatibility.newestFirstFoldingChallenges (r := 4) (𝓡 := 1) (ϑ := 1)
      (Fin.last 2) (fun j => (![0, 1] : Fin 2 → Nat) j.rev) 0 (by decide) =
      getFoldingChallenges (r := 4) (𝓡 := 1) (ϑ := 1)
        (Fin.last 2) ![0, 1] 0 (by decide) :=
  Binius.BinaryBasefold.Compatibility.newestFirstFoldingChallenges_reverse
    (r := 4) (𝓡 := 1) (ϑ := 1) (Fin.last 2) ![0, 1] 0 (by decide)

#print axioms chronological_first
#print axioms newestFirst_first
#print axioms reverse_input_recovers_chronological

end ArkLibTest.Compatibility.BiniusChallengeOrder
