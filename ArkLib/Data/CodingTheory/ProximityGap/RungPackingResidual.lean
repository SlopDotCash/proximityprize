/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungSummationScaffold
import ArkLib.Data.CodingTheory.ProximityGap.RungEventInterface

/-!
# The class-packing residual (#371, rung): the single named obligation

Following the project's modularity convention (name the obligation as a
`Prop`, machine-verify everything around it — as for `CellPackageSupply`),
this file isolates the ONE residual the level-1 rung pin now rests on.

`ClassPackingBound dom d t B` asserts that every stack's bad-scalar set
admits a good cover: a zero-class element, a family of frame classes each
within its cap, and a solo set, with `1 + Σ caps + #solo ≤ B`.  This
bundles the two open halves — that the cover *exists* (the assembly of the
landed coupling laws) and that its sum is bounded (the packing count from
the Fisher family `RungAgreementFisher` and the 3-dim factor confinement
`RungClassFamily`).

`identityCensus_of_classPacking` discharges `IdentityCensusBound` from it
in one step via the summation scaffold `bad_card_le_partition`.  Hence the
rung pin = `ClassPackingBound dom4134 2 7 31`, with the entire probabilistic
→ identity → census → scaffold chain proven and axiom-clean.  Probe state:
the bound holds with margin 9 (truth 22 ≤ 31), and multi-class coexistence
collapses (`probe_wb371_blockframe*`).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section PackingResidual

variable (dom : Fin n ↪ F)

open Classical in
/-- The bad-scalar set of a stack at the identity level (the object
`IdentityCensusBound` counts). -/
noncomputable def badIdentitySet (d t : ℕ) (u₀ u₁ : Fin n → F) : Finset F :=
  Finset.univ.filter (fun γ : F =>
    ∃ S : Finset (Fin n), t ≤ S.card ∧
      (∃ P : F[X], P.natDegree ≤ d ∧ ∃ q : F[X],
        rowPoly dom u₀ + C γ * rowPoly dom u₁ - P
          = q * vanishingPoly dom S) ∧
      ¬ ((∃ q₀ : F[X], q₀.natDegree ≤ d ∧ ∀ i ∈ S, q₀.eval (dom i) = u₀ i) ∧
         (∃ q₁ : F[X], q₁.natDegree ≤ d ∧ ∀ i ∈ S, q₁.eval (dom i) = u₁ i)))

open Classical in
/-- **The class-packing residual** — the single named obligation of the
rung pin.  Every stack's bad set admits a cover (zero-class ∪ frame classes
∪ solo) whose capped sum is `≤ B`. -/
def ClassPackingBound (d t B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F,
    ∃ (z : F) (classes : Finset (Finset F)) (solo : Finset F)
      (cap : Finset F → ℕ),
      badIdentitySet dom d t u₀ u₁ ⊆ insert z (classes.biUnion id ∪ solo) ∧
      (∀ K ∈ classes, K.card ≤ cap K) ∧
      1 + (∑ K ∈ classes, cap K) + solo.card ≤ B

open Classical in
/-- **The capstone reduction**: the packing residual discharges the
identity census bound.  (`badIdentitySet` is definitionally the set
`IdentityCensusBound` counts; the scaffold `bad_card_le_partition` closes
the gap.) -/
theorem identityCensus_of_classPacking {d t B : ℕ}
    (h : ClassPackingBound dom d t B) :
    IdentityCensusBound dom d t B := by
  intro u₀ u₁
  obtain ⟨z, classes, solo, cap, hcover, hcap, hsum⟩ := h u₀ u₁
  have hbad : (Finset.univ.filter (fun γ : F =>
      ∃ S : Finset (Fin n), t ≤ S.card ∧
        (∃ P : F[X], P.natDegree ≤ d ∧ ∃ q : F[X],
          rowPoly dom u₀ + C γ * rowPoly dom u₁ - P
            = q * vanishingPoly dom S) ∧
        ¬ ((∃ q₀ : F[X], q₀.natDegree ≤ d ∧ ∀ i ∈ S, q₀.eval (dom i) = u₀ i) ∧
           (∃ q₁ : F[X], q₁.natDegree ≤ d ∧ ∀ i ∈ S, q₁.eval (dom i) = u₁ i))))
      = badIdentitySet dom d t u₀ u₁ := rfl
  rw [hbad]
  exact le_trans (bad_card_le_partition hcover hcap) hsum

end PackingResidual

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.identityCensus_of_classPacking
