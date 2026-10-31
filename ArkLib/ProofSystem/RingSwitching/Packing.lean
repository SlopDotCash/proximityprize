/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Batching
import ArkLib.ProofSystem.RingSwitching.Packing.CheckedObservation
import ArkLib.ProofSystem.RingSwitching.Packing.Multiplier
import ArkLib.ProofSystem.RingSwitching.Packing.Relations
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Quirky

/-!
# Independent finite-basis packing algebra

This umbrella exports independent packing/opening coordinates, polynomial round trips,
relations, batching separation, the matrix multiplier evaluator, and scalar layouts.
It makes no protocol-completeness, commitment-binding, or knowledge-soundness claim.
The native protocol and `RingSwitchingProfile` remain in their existing modules.
-/
