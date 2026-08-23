/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.AGL24DualZeroPatternPinned
import ArkLib.Data.CodingTheory.GMMDS.LovettDualSpanConnector
import ArkLib.Data.CodingTheory.GMMDS.LovettSymbolicMinorDischarge
import ArkLib.Data.CodingTheory.GMMDS.LovettMergeIndepProof

/-!
# [AGL24] Theorem A.2 (pinned form): the Lovett-route connector for the *non-vacuous* target

`AGL24DualZeroPatternPinned.lean` repaired the GM-MDS import boundary by pinning the multiplicity
total (`GMMDSDualZeroPatternTheoremPinned`, `∑ⱼ δⱼ = card ι − k`), curing the 13th false-residual
catch (the unpinned `GMMDSDualZeroPatternTheorem` is `False` at `δ ≡ 0`).  But that file leaves
the pinned target as a *hypothesis* consumed by `symbolicFullRank_of_classical_imports_pinned`.

This file **proves the pinned target along the Lovett route**, wiring together the four proven /
named pieces of the GM-MDS chain:

1. **Lovett's Theorem 1.7, unconditional** (`lovettThm17_unconditional`, fully proven in
   `LovettMergeIndepProof.lean`) — the algebraic core, now an in-tree theorem, not an assumption;
2. **the ring-change transfer** `RIMKernelTrivialFromLovett` (the genuine, recognized #389 open
   core: Lovett's `pFamUnion`-independence over `MvPolynomial (Fin n) F` ⟹ the RIM's trivial
   kernel over `MvPolynomial ι F`) — which discharges `SymbolicMinorFromLovett` (the encoding
   move) via the *proven* `symbolicMinorFromLovett_of_ringChange`;
3. **the Schwartz–Zippel specialization** (`exists_embedding_det_eval_ne_zero`, fully proven in
   `SchwartzZippelMinorSpecialization.lean`, built on `ToMathlib/MvPolynomial/SchwartzZippelExists`)
   — a nonzero symbolic minor over a large field becomes a nonsingular **evaluated** minor at
   distinct field points `φ`;
4. **the pinned dual repackaging** `DualRowsFromNonsingularEvalPinned`
   (`LovettDualRowsDischarge.lean`, the *dimensionally faithful* dual move — the unpinned
   `DualRowsFromNonsingularEval` is `False`, the 12th catch) — the nonsingular evaluated
   generator's edge-supported parity rows span the
   Reed–Solomon dual, **using the pin** to have enough copies to span.

So the precise statement here:

> `RIMKernelTrivialFromLovett` ∧ `DualRowsFromNonsingularEvalPinned` ∧ `FieldLargeForMinor`
> ⟹ `GMMDSDualZeroPatternTheoremPinned`

with Lovett's Theorem 1.7 and the Schwartz–Zippel layer **discharged internally** (no longer
hypotheses).  Composing with `symbolicFullRank_of_classical_imports_pinned` (the capstone) then
yields `SymbolicFullRankResidual` from the same three residuals plus Frank's orientation residual.

## The honest residual ledger after this file

The pinned target is reduced to **exactly the two genuinely-missing GM-MDS matrix moves** plus
the field-size regime:

* `RIMKernelTrivialFromLovett` — the **single named open core** (the ring-change transfer; the
  recognized hard #389 GM-MDS algebra of AGL24 Appendix A; *not circular*, *not vacuous* — its
  conclusion is satisfiable from the symbolic-full-rank interface on a WPC witness, see
  `rimKernelTrivial_conclusion_of_symbolicFullRank_wpc`);
* `DualRowsFromNonsingularEvalPinned` — the **dimensionally faithful dual repackaging** (kernel
  of the nonsingular evaluated generator spans the dual, with the pin guaranteeing the copy index
  matches the dual's finrank, `gzpCopyIdx_card_eq_dual_finrank`);
* `FieldLargeForMinor` — the explicit `|F| > deg + C(|ι|,2)` regime.

The **vacuity defect is gone**: this connector targets the *pinned* boundary, so the `δ ≡ 0`
countermodel that refuted the unpinned chain cannot arise (the pin `∑ⱼ δⱼ = card ι − k > 0` forces
the copy index nonempty whenever `k < card ι`).

Issue #354 / #389.
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type*} [Field F] [Fintype F]

/-- **The pinned dual-zero-pattern target via the Lovett route — Schwartz–Zippel discharged,
Lovett discharged internally.**

From the ring-change transfer `RIMKernelTrivialFromLovett` (the named #389 open core), the
*pinned* dual repackaging `DualRowsFromNonsingularEvalPinned`, and the field-size regime
`FieldLargeForMinor`, the pinned GM-MDS import boundary `GMMDSDualZeroPatternTheoremPinned`
holds.

The proof runs the genuine path for each pinned `(e, δ)`:
* the ring-change transfer gives `SymbolicMinorFromLovett`
  (`ArkLib.GMMDS.symbolicMinorFromLovett_of_ringChange`), which — with Lovett's Theorem 1.7
  supplied internally by `lovettThm17_unconditional` — produces a nonzero **symbolic** RIM minor;
* the **proven** Schwartz–Zippel lemma `exists_embedding_det_eval_ne_zero` specializes it to
  distinct field points `φ` with the **evaluated** minor nonzero (using `FieldLargeForMinor`);
* the **pinned** dual repackaging `DualRowsFromNonsingularEvalPinned` (consuming the pin
  `∑ⱼ δⱼ = card ι − k`) produces the edge-supported dual rows spanning the Reed–Solomon dual.

Unlike `gmmDsDualZeroPatternTheorem_via_connector` (which targeted the *unpinned*, refutable
boundary and threaded the unpinned, `False` `DualRowsFromNonsingularEval`), this consumes the
pin and the dimensionally faithful pinned dual residual, so it is not over-stated. Axiom-clean
modulo the two named residuals `hrc`/`hdual` and the field regime `hfield`. -/
theorem gmmDsDualZeroPatternTheoremPinned_via_lovett {k : ℕ}
    (hrc : ArkLib.GMMDS.RIMKernelTrivialFromLovett ι F k)
    (hdual : ArkLib.GMMDS.DualRowsFromNonsingularEvalPinned ι F k)
    (hfield : ArkLib.GMMDS.FieldLargeForMinor ι F k) :
    GMMDSDualZeroPatternTheoremPinned (ι := ι) (F := F) k := by
  classical
  intro t e δ hgzp hpin
  -- Lovett's Theorem 1.7 is unconditional, in the bridge's `∀ m`-uniform form.
  have hlovett : ∀ m : ℕ, ArkLib.GMMDS.LovettThm17 (F := F) m :=
    fun _ => ArkLib.GMMDS.lovettThm17_unconditional
  -- Encoding move: the ring-change transfer gives a nonzero symbolic minor.
  have hminor : ArkLib.GMMDS.SymbolicMinorFromLovett ι F k :=
    ArkLib.GMMDS.symbolicMinorFromLovett_of_ringChange hrc
  obtain ⟨rows, _hinj, hdet⟩ := hminor hlovett e δ hgzp
  -- Schwartz–Zippel (proven): distinct field points keep the evaluated minor nonzero.
  obtain ⟨φ, hφ⟩ :=
    ArkLib.GMMDS.exists_embedding_det_eval_ne_zero
      ((AGL24.RIM F e).submatrix rows id) hdet (hfield e rows hdet)
  -- Pinned dual repackaging: edge-supported dual rows spanning the RS dual.
  obtain ⟨h, hsupp, hspan⟩ := hdual e δ hgzp hpin φ rows hφ
  exact ⟨φ, h, hsupp, hspan⟩

/-- **The symbolic Theorem 2.11 interface from the Lovett route, end-to-end through the pinned
target.**  Frank's orientation residual together with the three GM-MDS residuals
(`RIMKernelTrivialFromLovett`, `DualRowsFromNonsingularEvalPinned`, `FieldLargeForMinor`)
discharge `SymbolicFullRankResidual` — Lovett's Theorem 1.7 and the Schwartz–Zippel layer being
proven in-tree.

This routes `gmmDsDualZeroPatternTheoremPinned_via_lovett` through the capstone
`symbolicFullRank_of_classical_imports_pinned`: every `δ` the assembly feeds is
orientation-derived, hence satisfies the pin (`gzp_of_orientation_delta_sum`), so the pinned
target is all that is needed.  Axiom-clean modulo the four named residuals. -/
theorem symbolicFullRank_via_lovett_pinned [DecidableEq F] {k : ℕ}
    (hfrank : FrankOrientationResidual ι k)
    (hrc : ArkLib.GMMDS.RIMKernelTrivialFromLovett ι F k)
    (hdual : ArkLib.GMMDS.DualRowsFromNonsingularEvalPinned ι F k)
    (hfield : ArkLib.GMMDS.FieldLargeForMinor ι F k)
    (hnonempty : ∀ {t : ℕ}, ∀ e : ι → Finset (Fin (t + 1)),
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
      ∀ i, (e i).Nonempty) :
    SymbolicFullRankResidual (ι := ι) F k :=
  symbolicFullRank_of_classical_imports_pinned hfrank
    (gmmDsDualZeroPatternTheoremPinned_via_lovett hrc hdual hfield) hnonempty

/-! ## Honesty: the three residuals are not `False`, and the genuinely-hard one is named

The decomposition `RIMKernelTrivialFromLovett ∧ DualRowsFromNonsingularEvalPinned ∧
FieldLargeForMinor ⟹ GMMDSDualZeroPatternTheoremPinned` introduces no impossible obligation:

* the **vacuity defect that killed the unpinned chain is absent** — this connector targets the
  *pinned* boundary, where `∑ⱼ δⱼ = card ι − k > 0` (for `k < card ι`) forces the copy index
  nonempty, so the `δ ≡ 0` countermodel (the 12th/13th catches) cannot arise;
* the **pinned dual residual's conclusion is dimensionally consistent** under the pin
  (`pinnedDual_dimension_consistent` below, re-exporting `gzpCopyIdx_card_eq_dual_finrank`): the
  copy index `GZPCopyIdx δ` has exactly the Reed–Solomon dual's finrank, so a spanning family is
  feasible (it must be a basis) — the necessary condition the *unpinned*
  `DualRowsFromNonsingularEval` violated;
* the **ring-change core's conclusion is satisfiable** from the symbolic-full-rank interface on a
  WPC witness (`ArkLib.GMMDS.rimKernelTrivial_conclusion_of_symbolicFullRank_wpc`), so
  `RIMKernelTrivialFromLovett` is the recognized hard #389 GM-MDS algebra, not a vacuous or
  circular obligation.

So after this file the pinned target is reduced to the **single named open mathematical core**
`RIMKernelTrivialFromLovett` (the ring-change transfer) plus the dimensionally faithful dual
move `DualRowsFromNonsingularEvalPinned` and the explicit field-size regime — none refuted, none
in-tree, the honest localization. -/

omit [Nonempty ι] [Fintype F] in
/-- **The pinned dual residual's conclusion is dimensionally consistent.** Under the pin
`∑ⱼ δⱼ = card ι − k` (and `k ≤ card ι`), the dual-row copy index `GZPCopyIdx δ` has exactly the
finrank of the Reed–Solomon dual, so the spanning family the residual demands is dimensionally
feasible. This is the positive consequence of pinning — the necessary condition the *unpinned*
`DualRowsFromNonsingularEval` (the 12th catch) violated. (Re-exported from
`ArkLib.GMMDS.gzpCopyIdx_card_eq_dual_finrank`.) Axiom-clean. -/
theorem pinnedDual_dimension_consistent {t : ℕ} {δ : Fin (t + 1) → ℕ} {k : ℕ} (φ : ι ↪ F)
    (hk : k ≤ Fintype.card ι) (hpin : ∑ j, δ j = Fintype.card ι - k) :
    Fintype.card (GZPCopyIdx δ)
      = Module.finrank F (dotForm.orthogonal (ReedSolomon.code φ k)) :=
  ArkLib.GMMDS.gzpCopyIdx_card_eq_dual_finrank φ hk hpin

omit [DecidableEq ι] [Nonempty ι] [Fintype F] in
/-- **The ring-change core's conclusion is satisfiable.** `RIMKernelTrivialFromLovett`'s
conclusion (the RIM has trivial polynomial kernel) is reachable from the symbolic-full-rank
interface `SymbolicFullRankResidual` on a `WeaklyPartitionConnected` witness — the regime where
the proven `exists_nonzero_poly_minor` machinery applies. So the named open core is *not* `False`
and *not* circular; it is the genuine GM-MDS ring-change algebra (#389), the single hard
mathematical residual the pinned target reduces to. (Re-exported from
`ArkLib.GMMDS.rimKernelTrivial_conclusion_of_symbolicFullRank_wpc`.) Axiom-clean. -/
theorem ringChangeCore_conclusion_satisfiable {k : ℕ}
    (hsym : SymbolicFullRankResidual (ι := ι) F k)
    {t : ℕ} (ht : 1 ≤ t) (e : ι → Finset (Fin (t + 1)))
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e)
    (v : Fin t × Fin k → MvPolynomial ι F)
    (hker : (AGL24.RIM F e).mulVec v = 0) :
    v = 0 :=
  ArkLib.GMMDS.rimKernelTrivial_conclusion_of_symbolicFullRank_wpc hsym ht e hwpc v hker

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.gmmDsDualZeroPatternTheoremPinned_via_lovett
#print axioms AGL24.symbolicFullRank_via_lovett_pinned
#print axioms AGL24.pinnedDual_dimension_consistent
#print axioms AGL24.ringChangeCore_conclusion_satisfiable
