/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.OracleInterface

/-!
# `simOracle` `foldlM` collapse

`simulateQ_simOracle_foldlM`: if every step of a `List.foldlM` simulates — under the honest
single-family oracle `OracleInterface.simOracle` — to a pure value, the whole `foldlM` collapses to
the corresponding pure `List.foldl`. This is the generic tool for showing that an oracle
reconstruction built as a fold over a Boolean cube (e.g. the Spartan matrix-vector / `Z`
reconstructions) evaluates deterministically under the honest oracle. Family- and
accumulator-generic.
-/

open OracleComp OracleSpec OracleInterface

variable {ι : Type} {oSpec : OracleSpec ι}
    {ιf : Type} {fam : ιf → Type} [∀ i, OracleInterface (fam i)]

/-- If every step of a `foldlM` simulates (under the honest single-family oracle) to a pure value,
the whole `foldlM` collapses to the corresponding pure `foldl`. -/
theorem simulateQ_simOracle_foldlM (oos : ∀ i, fam i) {α β : Type}
    (stepM : α → β → OracleComp (oSpec + [fam]ₒ) α) (stepPure : α → β → α)
    (xs : List β) (acc : α)
    (hstep : ∀ a y, simulateQ (simOracle oSpec oos) (stepM a y) = pure (stepPure a y)) :
    simulateQ (simOracle oSpec oos) (xs.foldlM stepM acc) = pure (xs.foldl stepPure acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      rw [List.foldlM_cons, List.foldl_cons, simulateQ_bind, hstep]
      simpa using ih (stepPure acc y)
