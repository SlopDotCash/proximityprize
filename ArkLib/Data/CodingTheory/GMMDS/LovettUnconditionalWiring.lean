/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.GMMDS.LovettDualSpanConnector
import ArkLib.Data.CodingTheory.GMMDS.LovettMergeIndepProof

/-!
# Discharging Lovett's Theorem 1.7 in the GM-MDS bridge (#389)

`LovettMergeIndepProof.lean` proves `lovettThm17_unconditional : LovettThm17 F n` for **every**
`n` and **every** field `F`, axiom-clean.  That theorem is the *exactly* the hypothesis
`(∀ m, LovettThm17 (F := F) m)` that every step of the Lovett ⟶ AGL24 GM-MDS bridge carries as
an assumption (`LovettToGMMDSBridge.lean`, `LovettToGZPDualBridgeReduction.lean`,
`LovettDualSpanConnector.lean`).

This file **removes that hypothesis from the chain**.  Each conditional consumer is re-stated
with the Lovett premise discharged by `lovettThm17_unconditional`, so the only remaining inputs
are the GM-MDS *encoding/dual* moves (`SymbolicMinorFromLovett`, `DualRowsFromNonsingularEval`,
`FieldLargeForMinor`) — the genuine linear-algebra-over-`F[a]` content of the GM-MDS matrix
construction — with Lovett's algebraic core no longer an open premise.

## What this does and does not close

* **Closed here.** The `(∀ m, LovettThm17)` premise: it is now a proved theorem, not an
  assumption.  Every theorem below is `lovett`-free.
* **Still required.** The two GM-MDS encoding residuals from `LovettDualSpanConnector.lean`:
  - `SymbolicMinorFromLovett` — Lovett's `pFamUnion` independence ⟹ a not-identically-zero
    `k × k` minor of the reduced intersection matrix `RIM F e` (the "Conjecture 1.3 follows
    from Theorem 1.7" encoding: translate `(e, δ)`+`GZPCondition` into a `V*(k)` system whose
    `pFamUnion` independence *is* the symbolic minor non-vanishing).  This is genuine
    linear-algebra content over `F[a]` that is **not** yet wired in-tree: `RIM` and
    `pFamUnion` live in disjoint developments, and the in-tree route to a nonzero `RIM` minor
    (`AGL24.exists_nonzero_poly_minor`) consumes `AGL24.SymbolicFullRankResidual`, which is
    itself only produced from `AGL24.GMMDSResidual` — the very target — so that route would be
    **circular**.  A non-circular discharge needs the direct `pFamUnion`-independence ⟹
    `RIM`-kernel-trivial identification.
  - `DualRowsFromNonsingularEval` — a nonsingular **evaluated** `RIM` minor at distinct field
    points ⟹ the edge-supported dual rows spanning the Reed–Solomon dual.  This is the GM-MDS
    "kernel of the nonsingular generator spans the dual" construction; the in-tree
    `AGL24.pinning_of_dual_span` runs the *opposite* direction (dual span ⟹ pinning), so this
    too is genuinely missing.

So the precise residual ledger after this file: **`SymbolicMinorFromLovett` ∧
`DualRowsFromNonsingularEval` ∧ `FieldLargeForMinor`** ⟹ unconditional
`GMMDSDualZeroPatternTheorem` / `GMMDSResidual`.  **Status correction:** this ledger is
vacuous in the intended regime. The target `GMMDSDualZeroPatternTheorem` is refuted for
`k < card ι` (`AGL24.not_gmmDsDualZeroPatternTheorem`), `DualRowsFromNonsingularEval` is refuted
(`not_dualRowsFromNonsingularEval`), and `SymbolicMinorFromLovett` is refuted for `1 ≤ k`
(`not_symbolicMinorFromLovett`, below). Earlier "satisfiable" claims only exhibited
goal-conditional implications, which supply no inhabitant. The theorems below are valid
conditional wiring, retained as historical records; they do not reduce GM-MDS to true
residuals.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
/-- **Lovett's Theorem 1.7, in the bridge's `∀ m`-uniform form.**  Just packages
`lovettThm17_unconditional` over every coordinate dimension.  Axiom-clean. -/
theorem lovettThm17_unconditional_forall : ∀ m : ℕ, LovettThm17 (F := F) m :=
  fun _ => lovettThm17_unconditional

/-- **Step 2 (`LovettSystemToDualSpan`) with Lovett discharged.**  From the two GM-MDS encoding
residuals plus the field-size regime, the step-2 reduction holds — and it no longer needs the
Lovett hypothesis to be *supplied*, because the proof of `LovettSystemToDualSpan` only uses
that hypothesis internally, and we now have it unconditionally.  (The `Prop`
`LovettSystemToDualSpan` still carries the premise in its statement; this lemma is its
hypothesis-discharged *use site*, packaged below as the unconditional boundary.)  Axiom-clean. -/
theorem lovettSystemToDualSpan_unconditional {k : ℕ}
    (hminor : SymbolicMinorFromLovett ι F k)
    (hdual : DualRowsFromNonsingularEval ι F k)
    (hfield : FieldLargeForMinor ι F k) :
    LovettSystemToDualSpan ι F k :=
  lovettSystemToDualSpan_of_connector hminor hdual hfield

/-- **UNCONDITIONAL `GMMDSDualZeroPatternTheorem` modulo the two GM-MDS encoding residuals.**
Composing the connector path with `lovettThm17_unconditional_forall` discharges the AGL24
dual-zero-pattern boundary with **no Lovett hypothesis remaining** — only the two genuinely
missing GM-MDS encoding/dual moves (and the field-size regime) are required.  Axiom-clean.

This is the wiring capstone of the Lovett route: Lovett's algebraic Theorem 1.7 is fully
discharged in-tree. The two remaining hypotheses are, however, both refuted as stated
(`not_symbolicMinorFromLovett`, `not_dualRowsFromNonsingularEval`), and so is the conclusion for
`k < card ι` (`AGL24.not_gmmDsDualZeroPatternTheorem`): this is a valid but vacuous conditional
theorem, kept as a historical record. -/
theorem gmmDsDualZeroPatternTheorem_unconditional {k : ℕ} (hk : 1 ≤ k)
    (hminor : SymbolicMinorFromLovett ι F k)
    (hdual : DualRowsFromNonsingularEval ι F k)
    (hfield : FieldLargeForMinor ι F k) :
    AGL24.GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k :=
  gmmDsDualZeroPatternTheorem_via_connector hk hminor hdual hfield
    lovettThm17_unconditional_forall

/-- **UNCONDITIONAL `GMMDSResidual` modulo the two GM-MDS encoding residuals.**  Forwarding the
unconditional dual-zero-pattern boundary to the older existential `GMMDSResidual` interface that
`AGL24.symbolicFullRank_of_classical_imports` consumes.  No Lovett hypothesis.  Axiom-clean.

Its hypotheses `hminor`/`hdual` are refuted as stated (`not_symbolicMinorFromLovett`,
`not_dualRowsFromNonsingularEval`), so this does **not** remove GM-MDS as an assumption of the
AGL24 cone; the consumer-facing GM-MDS boundary is the pinned
`AGL24.GMMDSDualZeroPatternTheoremPinned`. -/
theorem gmmDsResidual_unconditional {k : ℕ} (hk : 1 ≤ k)
    (hminor : SymbolicMinorFromLovett ι F k)
    (hdual : DualRowsFromNonsingularEval ι F k)
    (hfield : FieldLargeForMinor ι F k) :
    AGL24.GMMDSResidual ι F k :=
  AGL24.gmmDsResidual_of_dualZeroPatternTheorem
    (gmmDsDualZeroPatternTheorem_unconditional hk hminor hdual hfield)

/-! ## Status of the post-Lovett residual pair: both residuals are FALSE as stated

An earlier version of this section claimed the remaining obligation
`SymbolicMinorFromLovett ∧ DualRowsFromNonsingularEval ∧ FieldLargeForMinor` is "satisfiable /
not `False`" because the AGL24 goal `GMMDSDualZeroPatternTheorem` implies it. That inference is
invalid: an implication from an *unproved* goal supplies no inhabitant. Worse, the goal itself
is refuted in the intended regime `k < card ι` (`AGL24.not_gmmDsDualZeroPatternTheorem`, the
13th false-residual catch), and so are both residuals:

* `DualRowsFromNonsingularEval` is `False` whenever `k < card ι` and an embedding `ι ↪ F`
  exists (`not_dualRowsFromNonsingularEval`, the 12th catch);
* `SymbolicMinorFromLovett` is `False` whenever `1 ≤ k` (`not_symbolicMinorFromLovett` below):
  at `t = 1`, `e ≡ ∅`, `δ ≡ 0` the `GZPCondition` hypothesis holds vacuously, but the RIM has no
  rows, so no row selector `Fin 1 × Fin k → RIMRowIdx e` exists. This is the same
  missing-WPC mechanism as `rimKernelTrivialFromLovett_refuted` (the 14th catch).

So `gmmDsDualZeroPatternTheorem_unconditional` / `gmmDsResidual_unconditional` are valid
conditional theorems with unsatisfiable hypotheses in the intended regime; they are historical
wiring, not a reduction of GM-MDS to open-but-plausible residuals. The dimensionally faithful,
WPC-guarded objects are the pinned target `AGL24.GMMDSDualZeroPatternTheoremPinned` and
`RIMKernelTrivialFromLovettWPC`. -/

omit [DecidableEq ι] [Nonempty ι] [Fintype F] in
/-- `DualRowsFromNonsingularEval`'s dual-row conclusion shape, *conditional on* the AGL24 goal
(it discards the supplied `φ`/nonsingularity witness and uses the goal's own dual rows).
Axiom-clean. This is only a goal-conditional implication; it does **not** show the residual is
satisfiable (the goal is refuted for `k < card ι`, `AGL24.not_gmmDsDualZeroPatternTheorem`). -/
theorem dualRows_inhabited_of_goal {k : ℕ}
    (hgoal : AGL24.GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k)
    {t : ℕ} (e : ι → Finset (Fin (t + 1))) (δ : Fin (t + 1) → ℕ)
    (hgzp : AGL24.GZPCondition e δ k) :
    ∃ φ : ι ↪ F, ∃ h : AGL24.GZPCopyIdx δ → (ι → F),
      (∀ a : AGL24.GZPCopyIdx δ, ∀ i : ι, a.vertex ∉ e i → h a i = 0) ∧
      Submodule.span F (Set.range h) =
        AGL24.dotForm.orthogonal (ReedSolomon.code φ k) :=
  dualRowsFromNonsingularEval_inhabited_of_goal hgoal e δ hgzp

omit [Nonempty ι] [Fintype F] in
/-- **`SymbolicMinorFromLovett` is FALSE as stated** for every `1 ≤ k` (and every `ι`, `F`).
Witness: `t = 1`, the all-empty edge family and `δ ≡ 0`. `GZPCondition` holds vacuously (no
`κ ≤ 0` has positive total), Lovett's Theorem 1.7 holds (`lovettThm17_unconditional`), but
`RIMRowIdx (fun _ => ∅)` is empty while `Fin 1 × Fin k` is inhabited, so no row selector exists.
Same mechanism as `rimKernelTrivialFromLovett_refuted` (#389, 14th catch). Axiom-clean. -/
theorem not_symbolicMinorFromLovett {k : ℕ} (hk : 1 ≤ k) :
    ¬ SymbolicMinorFromLovett ι F k := by
  classical
  intro h
  have hgzp : AGL24.GZPCondition (fun _ : ι => (∅ : Finset (Fin (1 + 1))))
      (fun _ => 0) k := by
    intro κ hκ hpos
    exfalso
    have hz : ∀ j, κ j = 0 := fun j => Nat.le_zero.mp (hκ j)
    simp only [hz] at hpos
    simp at hpos
  obtain ⟨rows, _, _⟩ := h lovettThm17_unconditional_forall
    (fun _ : ι => (∅ : Finset (Fin (1 + 1)))) (fun _ => 0) hgzp
  exact absurd (rows (0, ⟨0, hk⟩)).2.property.1 (by simp)

end ArkLib.GMMDS

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.GMMDS.lovettThm17_unconditional_forall
#print axioms ArkLib.GMMDS.lovettSystemToDualSpan_unconditional
#print axioms ArkLib.GMMDS.gmmDsDualZeroPatternTheorem_unconditional
#print axioms ArkLib.GMMDS.gmmDsResidual_unconditional
#print axioms ArkLib.GMMDS.dualRows_inhabited_of_goal
#print axioms ArkLib.GMMDS.not_symbolicMinorFromLovett
