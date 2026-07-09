/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Relay
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Commit
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.FinalSumcheck

/-!
## Binary Basefold single steps

This module is the compatibility entry point for the maintained split step proofs:

* `Steps.Fold`
* `Steps.Relay`
* `Steps.Commit`
* `Steps.FinalSumcheck`

The former aggregate implementation duplicated stale versions of these definitions and contained
unprovable executable holes, notably perfect-completeness statements missing `NeverFail init`.
The split modules carry the repaired statements and the current relation layer used downstream by
`CoreInteractionPhase`.
-/
