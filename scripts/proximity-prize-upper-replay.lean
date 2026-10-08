/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/

import ProximityPrize.SubmissionUpper.Solution
import Lean
import Lean.Replay

/-!
# Pinned Proximity Prize upper-candidate replay

Adapted from CompPoly's KoalaBear `FreshReplay.lean` at
`da1e1b5d048d26eca4583ff930f248c5e2bb5d9e`, for the reference's Lean 4.32.2 API.
Run through `scripts/proximity-prize-reference.sh replay-upper` after building `upper`.
Imported proof dependencies are replayed into an empty kernel environment. Inspect that
kernel environment directly: the higher-level environment may hide private declarations.
-/

open Lean

deriving instance BEq for Lean.QuotKind, Lean.QuotVal, Lean.InductiveVal, Lean.ConstantInfo

private def exportClosure
    (env : Environment) (roots : Array Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut out : Std.HashMap Name ConstantInfo := {}
  let mut pending := roots
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if out.contains name then continue
    let some ci := env.find? name | throw <| IO.userError s!"Missing replay constant {name}"
    if ci.isUnsafe || ci.isPartial then
      throw <| IO.userError s!"Unsafe or partial constant in replay closure: {name}"
    if let .axiomInfo _ := ci then
      unless #[`propext, `Classical.choice, `Quot.sound].contains name do
        throw <| IO.userError s!"Unapproved axiom in replay closure: {name}"
    out := out.insert name ci
    for dep in ci.getUsedConstantsAsSet do pending := pending.push dep
    if let .inductInfo info := ci then
      pending := pending ++ info.all.toArray ++ info.ctors.toArray
    if let .quotInfo _ := ci then
      pending := pending ++ #[`Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Eq]
  return out

private def replayClosure (constants : Std.HashMap Name ConstantInfo) : IO Unit := do
  -- Adding `Quot` installs these three constants, so replay must not add them twice.
  let quotientChildren := #[`Quot.mk, `Quot.lift, `Quot.ind]
  let replayConstants := quotientChildren.foldl (fun cs name => cs.erase name) constants
  let checked := (← Lean.Environment.replay replayConstants (← mkEmptyEnvironment)).toKernelEnv
  for (name, _) in constants.toList do
    unless (checked.find? name).isSome do
      throw <| IO.userError s!"Fresh replay omitted {name}"
  for name in #[`Quot] ++ quotientChildren do
    if let some original := constants[name]? then
      let some actual := checked.find? name
        | throw <| IO.userError s!"Missing quotient constant: {name}"
      unless actual == original do
        throw <| IO.userError s!"Quotient constant mismatch: {name}"

run_elab do
  let env ← importModules
    #[{ module := `ProximityPrize.SubmissionUpper.Solution }]
    {} (trustLevel := 0) (loadExts := false) (level := .private)
  let constants ← exportClosure env
    #[`ProximityPrize.Benchmark.Upper.candidate]
  logInfo m!"Exported {constants.size} declarations for fresh replay"
  replayClosure constants
  logInfo "Fresh upper-candidate closure replay passed"
