/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Codex
-/

import Lean.Elab.Command

/-! Reject Lean's admitting `stop` tactic in parsed source. -/

open Lean Elab Command

namespace ArkLib.StopTactic

private partial def checkSyntax (stx : Syntax) : CommandElabM Unit := do
  if let `(tactic| stop%$token $_seq:tacticSeq) := stx then
    logErrorAt token "The `stop` tactic admits open goals. Provide a proof instead."
  stx.forArgsM checkSyntax

-- Run outside the commands so that `#guard_msgs` cannot capture this diagnostic.
initialize addModuleLinter { run := fun commands => commands.forM checkSyntax }

end ArkLib.StopTactic
