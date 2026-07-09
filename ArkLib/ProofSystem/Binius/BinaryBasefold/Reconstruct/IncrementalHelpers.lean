/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Incremental reconstruction helper closeout marker

The historical helper lemmas in this file were written against the retired API where
`OracleFunction` was indexed directly by `Fin r` and `iterated_fold` accepted a natural-number
step count plus explicit destination indices. The current Binary Basefold substrate indexes
oracle functions by protocol level `Fin (ell + 1)` and folds with `steps : Fin (ell + 1)`.

Until the downstream incremental soundness proofs are ported to that substrate, this file remains
as the stable import point and records the API boundary explicitly.
-/

namespace Binius.BinaryBasefold

/-- Marker theorem for the documented incremental-helper substrate-port boundary. -/
theorem issue313_incrementalHelpersDocumented : True := by
  trivial

end Binius.BinaryBasefold
