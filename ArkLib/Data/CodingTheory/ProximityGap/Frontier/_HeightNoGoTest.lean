/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic

/-!
# Height no-go regression test

This records a concrete canonical collision at a bad prime larger than `128^4`.  It is a small
decidable guard against resurrecting the false route "all canonical bad primes are below `n^4`".
-/

set_option autoImplicit false
set_option maxRecDepth 262144
set_option maxHeartbeats 2000000

namespace ArkLib.ProximityGap.Frontier.HeightNoGoTest

/-- Test whether `decide` can verify the canonical collision at a large bad prime
`p = 423237889 > 128^4`, primitive 128th root `ζ = 90645509`. -/
theorem heightnogo_collision_test :
    ((90645509 : ZMod 423237889) ^ 4 + 1) ^ 128 =
      ((90645509 : ZMod 423237889) ^ 2 + 1) ^ 128 := by
  decide

#print axioms heightnogo_collision_test

end ArkLib.ProximityGap.Frontier.HeightNoGoTest
