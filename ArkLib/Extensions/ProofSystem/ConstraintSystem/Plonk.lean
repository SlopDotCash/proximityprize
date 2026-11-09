/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.Data.MvPolynomial.Notation
import Mathlib.GroupTheory.Perm.List

/-! # The Plonk relation

We first define the initial relation of Plonk. The paper first defines a constraint system, then
define what it means for the constraint system to be satisfied. This forms the core relation of
Plonk. -/

namespace Plonk

namespace Gate

variable {𝓡 : Type} [CommRing 𝓡] {numWires : ℕ}

variable {a b c j : Fin numWires} {x : Fin numWires → 𝓡}

end Gate

variable {𝓡 : Type} [CommRing 𝓡] {numWires numGates : ℕ}

-- instance [Inhabited 𝓡] : Inhabited (ConstraintSystem 𝓡 numWires numGates) :=
--   inferInstance

-- instance : DecidableEq (ConstraintSystem 𝓡 numWires numGates) :=
--   inferInstance

namespace ConstraintSystem

end ConstraintSystem

section CopyConstraints

variable {n : ℕ} {𝓡 : Type} [CommRing 𝓡]

/-- Copy constraints are satisfied when the wire assignment is constant on orbits of
the permutation: every position that references the same wire carries the same value. -/
def CopyConstraintsSatisfied (f : Fin n → 𝓡) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, f (σ i) = f i

/-- The grand product identity: when copy constraints hold, the product with permuted
indices equals the product with identity indices. This is the completeness direction of
the Plonk permutation argument — the honest prover's accumulator telescopes to 1. -/
theorem prod_eq_of_copyConstraints (f g : Fin n → 𝓡) (σ : Equiv.Perm (Fin n)) (β γ : 𝓡)
    (hf : CopyConstraintsSatisfied f σ) :
    ∏ i : Fin n, (f i + β * g (σ i) + γ) =
    ∏ i : Fin n, (f i + β * g i + γ) := by
  conv_lhs => arg 2; ext i; rw [← hf i]
  exact Equiv.prod_comp σ (fun j => f j + β * g j + γ)

end CopyConstraints

-- Finally, we define the Plonk relation.

end Plonk
