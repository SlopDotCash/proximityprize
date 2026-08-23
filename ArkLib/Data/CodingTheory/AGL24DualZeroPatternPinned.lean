/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.AGL24GrandAssembly
import ArkLib.Data.CodingTheory.AGL24GMMDSInterface
import ArkLib.Data.CodingTheory.GMMDS.LovettDualRowsDischarge

/-!
# [AGL24] Theorem A.2: the unpinned dual-zero-pattern target is FALSE — the pinned repair

This file records the **13th machine-checked false-residual catch** of the GM-MDS cone
(#346/#389/#354) and supplies the faithful repair.

## The catch: `AGL24.GMMDSDualZeroPatternTheorem` is FALSE as stated

`AGL24.GMMDSDualZeroPatternTheorem k` (`AGL24GMMDSInterface.lean`) is the named GM-MDS import
consumed by `symbolicFullRank_of_classical_imports` (`AGL24GrandAssembly.lean`, via
`gmmDsResidual_of_dualZeroPatternTheorem`). It asserts:

> for **every** `δ` with `GZPCondition e δ k`, there are dual rows
> `h : GZPCopyIdx δ → (ι → F)`, each edge-supported, whose span is the **entire** Reed–Solomon
> dual `dotForm.orthogonal (ReedSolomon.code φ k)`.

But the dual-row index `GZPCopyIdx δ = Σⱼ Fin (δ j)` has cardinality `∑ⱼ δⱼ`, so the span of
`h` has dimension at most `∑ⱼ δⱼ`. The Reed–Solomon dual has dimension `card ι − k` (for
`k ≤ card ι`). `GZPCondition` only delivers the **length bound** `∑ⱼ δⱼ ≤ card ι − k` (taking
`κ = δ`), and is satisfied **vacuously** by `δ ≡ 0` (no `κ ≤ 0` has positive total). With
`δ ≡ 0` the index `GZPCopyIdx δ` is **empty**, hence `Set.range h = ∅` and the span is `⊥`;
but the RS dual is nonzero whenever `k < card ι`. So the demanded equality `⊥ = (RS dual)`
is impossible.

This is the **same** dimensional obstruction that already refuted the connector residual
`DualRowsFromNonsingularEval` (`LovettDualRowsDischarge.lean`, the 12th catch). The catch was
hiding one level up, at the named *target* boundary itself.

* `not_gmmDsDualZeroPatternTheorem` — the refutation, axiom-clean, for any `k < card ι`;
* `not_gmmDsDualZeroPatternTheorem_fin2` — a concrete inhabited instance
  (`ι = Fin 2`, `F = ZMod 2`, `k = 1`).

## The faithful repair: pin the multiplicity total

The fix is exactly the one `LovettDualRowsDischarge.lean` already isolated for the connector
residual: **restrict the target to multiplicity functions carrying the genuine GM-MDS
dimension count** `∑ⱼ δⱼ = card ι − k`, so the dual-row index has *exactly* the cardinality of
the dual's finrank (`gzpCopyIdx_card_eq_dual_finrank`) and the span equality is dimensionally
possible.

* `GMMDSDualZeroPatternTheoremPinned` — the repaired target (`GZPCondition` **and** the pin);

The repair is **non-vacuous and sufficient for the assembly**:

* `gzp_of_orientation_delta_sum` — the `δ` that `gzp_of_orientation` actually produces (from a
  head orientation with root `r`, `δⱼ = indeg j` off the root, `δᵣ = indeg r − k`) sums to
  `(∑ⱼ indeg j) − k = card ι − k`, i.e. it **satisfies the pin**;
* `gmmDsResidual_of_dualZeroPatternTheoremPinned` — the pinned target implies the older
  `GMMDSResidual` interface **for orientation-derived `δ`** (the only `δ` the assembly feeds);
* `symbolicFullRank_of_classical_imports_pinned` — **the capstone, re-routed**: Frank's
  orientation theorem and the *pinned* GM-MDS target jointly discharge the symbolic Theorem 2.11
  interface. Every orientation-derived `δ` satisfies the pin, so the pinned target is all the
  assembly ever needs.

So the GM-MDS import is correctly stated as `GMMDSDualZeroPatternTheoremPinned`; the unpinned
`GMMDSDualZeroPatternTheorem` is an over-statement that no GM-MDS theorem can satisfy.

Issue #354 / #389.
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type*} [Field F]

/-! ## The catch: the unpinned target is FALSE -/

omit [Nonempty ι] in
/-- **The 13th catch.** `GMMDSDualZeroPatternTheorem` (the named GM-MDS import of
`symbolicFullRank_of_classical_imports`) is `False` whenever `k < Fintype.card ι`: instantiate
at `t = 0`, `δ ≡ 0` (so `GZPCondition` holds vacuously and `GZPCopyIdx δ` is empty, forcing the
produced span to be `⊥`), but the Reed–Solomon dual is nonzero, so the demanded span equality
`⊥ = (RS dual)` is impossible. Axiom-clean.

Same dimensional obstruction as `ArkLib.GMMDS.not_dualRowsFromNonsingularEval` (the 12th catch),
hoisted to the target boundary. -/
theorem not_gmmDsDualZeroPatternTheorem {k : ℕ}
    (hk : k < Fintype.card ι) :
    ¬ GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k := by
  classical
  intro hgm
  -- `t = 0`, `δ ≡ 0`, empty edges.
  set e : ι → Finset (Fin (0 + 1)) := fun _ => (∅ : Finset (Fin 1)) with he
  set δ : Fin (0 + 1) → ℕ := fun _ => 0 with hδ
  -- `GZPCondition e δ k` holds vacuously: no `κ ≤ δ ≡ 0` has positive total.
  have hgzp : GZPCondition e δ k := by
    intro κ hκ hpos
    exfalso
    have hzero : ∑ j, κ j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have := hκ j; simp only [hδ] at this; omega
    omega
  obtain ⟨φ, h, _hsupp, hspan⟩ := hgm e δ hgzp
  -- `GZPCopyIdx δ` is empty (each fibre `Fin (δ j) = Fin 0`), so `Set.range h = ∅`.
  haveI hidx_empty : IsEmpty (GZPCopyIdx δ) := by
    constructor
    rintro ⟨j, m⟩
    exact (Nat.not_lt_zero m.val (by simpa [hδ] using m.isLt))
  have hrange : Set.range h = (∅ : Set (ι → F)) := Set.range_eq_empty h
  rw [hrange, Submodule.span_empty] at hspan
  exact ArkLib.GMMDS.reedSolomonDual_ne_bot φ hk hspan.symm

/-- **Concrete instance of the 13th catch.** Over `ι = Fin 2`, `F = ZMod 2`, `k = 1`
(so `k = 1 < 2 = card ι`), the unpinned target fails. This shows the countermodel is inhabited,
not vacuous. Axiom-clean. -/
theorem not_gmmDsDualZeroPatternTheorem_fin2 :
    ¬ GMMDSDualZeroPatternTheorem (ι := Fin 2) (F := ZMod 2) 1 :=
  not_gmmDsDualZeroPatternTheorem (by decide)

/-! ## The faithful repair: the pinned target -/

/-- **The repaired GM-MDS import boundary** (AGL24 Theorem A.2, dimensionally faithful form):
for every generic zero pattern `(e, δ)` satisfying `GZPCondition e δ k` **and carrying the
GM-MDS dimension count** `∑ⱼ δⱼ = card ι − k`, there are evaluation points and one dual row per
copied vertex, each edge-supported, spanning the Reed–Solomon dual.

The added hypothesis `∑ⱼ δⱼ = card ι − k` is the genuine dimension count produced by
`gzp_of_orientation` (`gzp_of_orientation_delta_sum`); the unpinned target dropped it, which is
what made it refutable. -/
def GMMDSDualZeroPatternTheoremPinned (k : ℕ) : Prop :=
  ∀ {t : ℕ}, ∀ e : ι → Finset (Fin (t + 1)), ∀ δ : Fin (t + 1) → ℕ,
    GZPCondition e δ k →
    (∑ j, δ j = Fintype.card ι - k) →
    ∃ φ : ι ↪ F, ∃ h : GZPCopyIdx δ → (ι → F),
      (∀ a : GZPCopyIdx δ, ∀ i : ι, a.vertex ∉ e i → h a i = 0) ∧
      Submodule.span F (Set.range h) =
        dotForm.orthogonal (ReedSolomon.code φ k)

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Nonempty ι] in
/-- **The pin holds at `gzp_of_orientation`'s `δ`.** The multiplicity function
`δⱼ = if j = r then indeg j − k else indeg j` produced by `gzp_of_orientation` sums to
`(∑ⱼ indeg j) − k = card ι − k` (each edge has exactly one head). This is the dimension count
the pinned target requires, and the unpinned target silently dropped. Axiom-clean. -/
theorem gzp_of_orientation_delta_sum {e : ι → Finset V} (O : HeadOrientation e) (r : V) (k : ℕ)
    (hroot : k ≤ O.inDegree r) :
    ∑ j, (fun j => if j = r then O.inDegree j - k else O.inDegree j) j
      = Fintype.card ι - k := by
  classical
  simp only
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r)]
  rw [if_pos rfl]
  have herase : ∑ j ∈ Finset.univ.erase r,
      (if j = r then O.inDegree j - k else O.inDegree j)
      = ∑ j ∈ Finset.univ.erase r, O.inDegree j :=
    Finset.sum_congr rfl fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]
  rw [herase]
  have hfull : (∑ j ∈ Finset.univ.erase r, O.inDegree j) + O.inDegree r
      = Fintype.card ι := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ r)]
    exact O.sum_inDegree
  omega

/-! ## The pinned target suffices for the assembly -/

omit [Nonempty ι] in
/-- **The pinned dual-zero-pattern target yields the dual span at orientation-derived `δ`.**
Given the pinned target and a head orientation supplying the GZP via `gzp_of_orientation`
(whose `δ` satisfies the pin by `gzp_of_orientation_delta_sum`), we obtain evaluation points
`φ` and an `ι`-indexed family of edge-supported dual rows spanning the Reed–Solomon dual —
exactly the shape `pinning_of_dual_span` consumes. Axiom-clean.

This is the pinned analogue of `gmmDsResidual_of_dualZeroPatternTheorem`: it forgets the
structured `GZPCopyIdx δ` index by reindexing through `Fintype.equivFin`, after the pin has
guaranteed the index is large enough to span. -/
theorem dualSpan_of_pinned_at_orientation {k : ℕ}
    (hgm : GMMDSDualZeroPatternTheoremPinned (ι := ι) (F := F) k)
    {t : ℕ} (e : ι → Finset (Fin (t + 1))) (O : HeadOrientation e) (r : Fin (t + 1))
    (hne : ∀ i, (e i).Nonempty)
    (hroot : k ≤ O.inDegree r)
    (hcross : ∀ T : Finset (Fin (t + 1)), r ∈ T → T ≠ Finset.univ →
      k ≤ (Finset.univ.filter (fun i => O.head i ∈ T ∧ ¬ e i ⊆ T)).card) :
    ∃ φ : ι ↪ F, ∃ d : ℕ, ∃ h : Fin d → (ι → F),
      (∀ ℓ, ∃ j : Fin (t + 1), ∀ i : ι, j ∉ e i → h ℓ i = 0) ∧
      Submodule.span F (Set.range h) = dotForm.orthogonal (ReedSolomon.code φ k) := by
  classical
  set δ : Fin (t + 1) → ℕ := fun j => if j = r then O.inDegree j - k else O.inDegree j with hδ
  have hgzp : GZPCondition e δ k := gzp_of_orientation O r k hne hroot hcross
  have hpin : ∑ j, δ j = Fintype.card ι - k := gzp_of_orientation_delta_sum O r k hroot
  obtain ⟨φ, h, hsupp, hspan⟩ := hgm e δ hgzp hpin
  -- Forget the structured copy index, reindexing by `Fin (card (GZPCopyIdx δ))`.
  refine ⟨φ, Fintype.card (GZPCopyIdx δ),
    fun a => h ((Fintype.equivFin (GZPCopyIdx δ)).symm a), ?_, ?_⟩
  · intro a
    refine ⟨((Fintype.equivFin (GZPCopyIdx δ)).symm a).vertex, ?_⟩
    intro i hi
    exact hsupp ((Fintype.equivFin (GZPCopyIdx δ)).symm a) i hi
  · rw [span_range_reindex_equivFin]
    exact hspan

/-- **THE CAMPAIGN CAPSTONE, RE-ROUTED THROUGH THE PINNED TARGET.** Frank's orientation theorem
and the **pinned** GM-MDS target jointly discharge the symbolic Theorem 2.11 interface — and
with it every layer of the tower above, up to the front door.

Unlike `symbolicFullRank_of_classical_imports`, this consumes the *dimensionally faithful*
GM-MDS boundary `GMMDSDualZeroPatternTheoremPinned`, which (unlike the unpinned
`GMMDSDualZeroPatternTheorem`, refuted above) is not over-stated. Every `δ` the assembly feeds
comes from `gzp_of_orientation` and so satisfies the pin (`gzp_of_orientation_delta_sum`), so
the pinned target is **all the assembly needs**. Axiom-clean. -/
theorem symbolicFullRank_of_classical_imports_pinned
    [Fintype F] [DecidableEq F] {k : ℕ}
    (hfrank : FrankOrientationResidual ι k)
    (hgm : GMMDSDualZeroPatternTheoremPinned (ι := ι) (F := F) k)
    (hnonempty : ∀ {t : ℕ}, ∀ e : ι → Finset (Fin (t + 1)),
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
      ∀ i, (e i).Nonempty) :
    SymbolicFullRankResidual (ι := ι) F k := by
  refine symbolicFullRank_of_pinning ?_ hnonempty
  intro t ht e hne hwpc
  -- Frank: the orientation with root and crossing supply.
  obtain ⟨O, r, hroot, hcross⟩ := hfrank ht e hne hwpc
  -- The pinned GM-MDS target at the orientation-derived (pin-satisfying) `δ`.
  obtain ⟨φ, d, h, hsupp, hspan⟩ :=
    dualSpan_of_pinned_at_orientation hgm e O r hne hroot hcross
  -- Brick 25: pinning.
  exact ⟨φ, pinning_of_dual_span φ e h hsupp hspan⟩

/-! ## Non-vacuity of the pinned target

Two honesty checks that the repair did not over-correct into an impossible obligation:

* the **hypothesis class is inhabited** — a generic zero pattern satisfying both `GZPCondition`
  *and* the pin `∑ⱼ δⱼ = card ι − k` exists for every head orientation with `k ≤ indeg r`
  (`gzp_of_orientation` produces the GZP, `gzp_of_orientation_delta_sum` the pin); and
* the **conclusion is dimensionally consistent** — under the pin the dual-row index
  `GZPCopyIdx δ` has *exactly* the cardinality of the Reed–Solomon dual's finrank
  (`ArkLib.GMMDS.gzpCopyIdx_card_eq_dual_finrank`), so a spanning family of edge-supported dual
  rows is dimensionally possible (it must be a basis). The unpinned target violated this; the
  pinned one restores it. -/

omit [Nonempty ι] in
/-- **The pinned hypothesis class is inhabited.** For every head orientation with root `r` of
in-degree `≥ k`, the orientation-derived `δ` satisfies both `GZPCondition e δ k` and the pin
`∑ⱼ δⱼ = card ι − k`. So the pinned target quantifies over a *nonempty* class of `(e, δ)`; the
pin is not an unsatisfiable side condition (it is exactly the GM-MDS dimension count). Axiom-clean. -/
theorem pinned_hypothesis_inhabited {V : Type*} [Fintype V] [DecidableEq V]
    {e : ι → Finset V} (O : HeadOrientation e) (r : V) (k : ℕ)
    (hne : ∀ i, (e i).Nonempty)
    (hroot : k ≤ O.inDegree r)
    (hcross : ∀ T : Finset V, r ∈ T → T ≠ Finset.univ →
      k ≤ (Finset.univ.filter (fun i => O.head i ∈ T ∧ ¬ e i ⊆ T)).card) :
    ∃ δ : V → ℕ, GZPCondition e δ k ∧ ∑ j, δ j = Fintype.card ι - k :=
  ⟨_, gzp_of_orientation O r k hne hroot hcross,
    gzp_of_orientation_delta_sum O r k hroot⟩

omit [Nonempty ι] in
/-- **The pinned conclusion is dimensionally possible.** Under the pin `∑ⱼ δⱼ = card ι − k`
(and `k ≤ card ι`), the dual-row index `GZPCopyIdx δ` has exactly the finrank of the
Reed–Solomon dual, so a spanning family is feasible — the necessary condition the unpinned
target violated. (Re-exported from `ArkLib.GMMDS.gzpCopyIdx_card_eq_dual_finrank`.) Axiom-clean. -/
theorem pinned_dimension_consistent {t : ℕ} {δ : Fin (t + 1) → ℕ} {k : ℕ} (φ : ι ↪ F)
    (hk : k ≤ Fintype.card ι) (hpin : ∑ j, δ j = Fintype.card ι - k) :
    Fintype.card (GZPCopyIdx δ)
      = Module.finrank F (dotForm.orthogonal (ReedSolomon.code φ k)) :=
  ArkLib.GMMDS.gzpCopyIdx_card_eq_dual_finrank φ hk hpin

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.not_gmmDsDualZeroPatternTheorem
#print axioms AGL24.not_gmmDsDualZeroPatternTheorem_fin2
#print axioms AGL24.gzp_of_orientation_delta_sum
#print axioms AGL24.dualSpan_of_pinned_at_orientation
#print axioms AGL24.symbolicFullRank_of_classical_imports_pinned
#print axioms AGL24.pinned_hypothesis_inhabited
#print axioms AGL24.pinned_dimension_consistent
