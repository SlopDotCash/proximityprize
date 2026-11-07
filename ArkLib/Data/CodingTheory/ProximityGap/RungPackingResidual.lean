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
admits a cover by one distinguished element `z`, a finite family of
`classes` each within a cap `cap K`, and a `solo` set, with
`1 + Σ caps + #solo ≤ B`.

**Scope (audit 2026-10-28, PG-077).** As formalized, the classes, caps and
solo set are *arbitrary*: nothing requires a class to arise from a frame, to
have its advertised agreement-set cap, to satisfy the Fisher intersections of
`RungAgreementFisher`, or to obey the factor confinement of
`RungClassFamily`. Consequently the predicate is a generic cover reformulation
of the same count budget, not an isolation of two structural open halves:
`classPacking_iff_identityCensus` proves `ClassPackingBound dom d t B ↔
IdentityCensusBound dom d t B` for every `B ≥ 1` (take `z` a bad element, no
classes, and the rest as `solo`). Cover existence is therefore not a new
obstruction, and theorems about frame classes do not apply to it by name
alone; a structural version would have to encode the frame/solo conditions in
the predicate.

`identityCensus_of_classPacking` discharges `IdentityCensusBound` from it
in one step via the summation scaffold `bad_card_le_partition`.  The rung
pin `ClassPackingBound dom4134 2 7 31` is thus equivalent to
`IdentityCensusBound dom4134 2 7 31`.  Probe state (not a proof): the count
holds with margin 9 (truth 22 ≤ 31), and multi-class coexistence collapses
(`probe_wb371_blockframe*`).
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
/-- **The class-packing cover predicate.**  Every stack's bad set admits a
cover (one element `z` ∪ capped classes ∪ solo) whose capped sum is `≤ B`.
The classes, caps and solo set are unrestricted (no frame, cap, Fisher or
confinement condition), so for `B ≥ 1` this is equivalent to
`IdentityCensusBound` (`classPacking_iff_identityCensus`). -/
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

open Classical in
/-- **The converse (PG-077)**: for `B ≥ 1`, the identity census bound already
yields a class-packing cover — take `z` to be a bad scalar (if any), no
classes, and the remaining bad scalars as `solo`. -/
theorem classPacking_of_identityCensus {d t B : ℕ} (hB : 1 ≤ B)
    (h : IdentityCensusBound dom d t B) :
    ClassPackingBound dom d t B := by
  intro u₀ u₁
  have hcard : (badIdentitySet dom d t u₀ u₁).card ≤ B := h u₀ u₁
  by_cases hne : (badIdentitySet dom d t u₀ u₁).Nonempty
  · obtain ⟨z, hz⟩ := hne
    refine ⟨z, ∅, (badIdentitySet dom d t u₀ u₁).erase z, fun _ => 0, ?_, ?_, ?_⟩
    · intro γ hγ
      rw [Finset.mem_insert]
      by_cases hγz : γ = z
      · exact Or.inl hγz
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hγz, hγ⟩))
    · intro K hK
      exact absurd hK (Finset.notMem_empty K)
    · rw [Finset.sum_empty, Finset.card_erase_of_mem hz]
      have hpos : 0 < (badIdentitySet dom d t u₀ u₁).card := Finset.card_pos.mpr ⟨z, hz⟩
      omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨0, ∅, ∅, fun _ => 0, ?_, ?_, ?_⟩
    · rw [hne]; exact Finset.empty_subset _
    · intro K hK
      exact absurd hK (Finset.notMem_empty K)
    · rw [Finset.sum_empty, Finset.card_empty]
      omega

open Classical in
/-- **`ClassPackingBound` is a reformulation of the census count (PG-077).**
For every `B ≥ 1`, `ClassPackingBound dom d t B ↔ IdentityCensusBound dom d t B`.
(For `B = 0` the cover predicate is unsatisfiable because of its `1 +` term.) -/
theorem classPacking_iff_identityCensus {d t B : ℕ} (hB : 1 ≤ B) :
    ClassPackingBound dom d t B ↔ IdentityCensusBound dom d t B :=
  ⟨identityCensus_of_classPacking dom, classPacking_of_identityCensus dom hB⟩

end PackingResidual

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.identityCensus_of_classPacking
#print axioms ProximityGap.WBPencil.classPacking_iff_identityCensus
