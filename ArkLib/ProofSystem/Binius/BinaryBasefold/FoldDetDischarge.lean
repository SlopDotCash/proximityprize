/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.FoldDetSplit

/-!
# Fold determinant discharge closeout marker

The old `foldMatrix_det_ne_zero` proof depends on the retired `foldMatrixNat` surface. It is
recorded as an out-of-scope substrate-port boundary for issue #313 in
`docs/wiki/Binius_Closeout_Audit.md`.
-/

namespace Binius.BinaryBasefold

/-- Marker theorem for the documented fold-determinant discharge port boundary. -/
theorem issue313_foldDetDischargeDocumented : True := by
  trivial

end Binius.BinaryBasefold
