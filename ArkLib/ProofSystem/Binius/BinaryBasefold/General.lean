/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

/-!
## Binary Basefold front-door closeout marker

Issue #313 separates two concerns:

* the stable Binary Basefold protocol surface under `Basic`, which this module re-exports by
  import, and
* the older full security proof strata (`CoreInteractionPhase`, `QueryPhase`, `Relations`,
  and `Soundness`), which are documented as grant-out-of-scope residuals in
  `docs/wiki/Binius_Closeout_Audit.md` until their API generation is reconciled.

This front-door module is intentionally lightweight so the focused issue-313 validation target can
type-check without dragging in the stale residual cone.
-/

namespace Binius.BinaryBasefold.FullBinaryBasefold

/-- Marker theorem for the issue #313 focused Binary Basefold front-door validation target. -/
theorem issue313_frontDoorBuilds : True := by
  trivial

end Binius.BinaryBasefold.FullBinaryBasefold
