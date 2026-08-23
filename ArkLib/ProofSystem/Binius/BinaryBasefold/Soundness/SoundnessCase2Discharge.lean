/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessProposition
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessCase2Probability

/-!
# Proposition 4.21 Case 2 — residual retired (issue #317)

The former `Prop421Case2FiberwiseFarResidual` typeclass has been removed from the active
Proposition 4.21 API.  The fiberwise-far branch is now the direct theorem
`prop_4_21_case_2_fiberwise_far`, backed by `prop421Case2_probability_bound` in
`Soundness.Prop421Case2Probability`.
-/

namespace Binius.BinaryBasefold

noncomputable section

end

end Binius.BinaryBasefold
