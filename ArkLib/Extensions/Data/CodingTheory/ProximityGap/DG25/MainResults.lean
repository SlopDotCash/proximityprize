/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ProximityGap.DG25.MainResults

/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGap.DG25.Basic

/-!
# DG25 Main Interleaved-Code Results

This module contains the main interleaved and tensor proximity-gap lemmas from the DG25
formalization, up to the generic tensor-gap lifting theorem.
-/

noncomputable section

open Code LinearCode InterleavedCode ReedSolomon ProximityGap ProbabilityTheory Filter
open NNReal Finset Function Real
open scoped BigOperators LinearCode ProbabilityTheory

universe u v w k l
variable {κ : Type k} {ι : Type l} [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq κ]
variable {F : Type v} [Semiring F] [Fintype F]
variable {A : Type w} [Fintype A] [DecidableEq A] [AddCommMonoid A] [Module F A]
section MainResults
variable {F : Type} [CommRing F] [Fintype F] [NoZeroDivisors F] [DecidableEq F]
  -- switch to Type for `Pr_{...}[...]` usage
  {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A] [Module.Free F A]
  -- Semiring.toModule (R := A) => Module A A, plus Ring A for `RS code` theorems?
variable (MC : ModuleCode ι F A) [Nontrivial MC]
  (C : Set (Word A ι)) [Nonempty C] -- note: change to Nontrivial if needed

instance moduleInstance_MainResults_1 : Nonempty MC := by exact instNonemptyOfInhabited

-- instance : ∀ (κ : Type*) [Fintype κ] [DecidableEq κ], Nonempty (C ^⋈ κ) := by
--   intro κ hκ hκ_dec
--   exact instNonemptyInterleavedCode A (κ := κ) (ι := ι) C

/-!
## Section 3: Main Results
-/

variable {m : Nat} -- Interleaving factor > 0 (Proof uses m>1 later)
variable {e ε : ℕ} -- Proximity parameter and false witness bound

end MainResults

end
