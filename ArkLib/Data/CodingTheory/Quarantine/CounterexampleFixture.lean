/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic

/-! Shared GF(3), length-four counterexample data for the promoted and quarantined hypotheses. -/

namespace ProximityGap.HypothesisCounterexample

abbrev F := ZMod 3
abbrev n : ℕ := 4
abbrev m : ℕ := 2

def H_matrix : Matrix (Fin 2) (Fin 4) F :=
  ![![1, 0, 1, 1],
    ![0, 1, 1, 2]]

-- Valid codewords
def w0 : Fin 4 → F := ![0, 0, 0, 0]
def w1 : Fin 4 → F := ![1, 1, 2, 0]
def w2 : Fin 4 → F := ![2, 1, 0, 1]

end ProximityGap.HypothesisCounterexample
