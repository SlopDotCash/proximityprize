/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.GMMDS.LovettDualSpanConnector

/-!
# `DualRowsFromNonsingularEval` is FALSE as stated — a machine-checked countermodel (#389)

This file investigates the second residual of `LovettDualSpanConnector.lean`,
`DualRowsFromNonsingularEval`, which the connector chain expects to discharge by
"the nonsingular evaluated generator's zero-pattern parity rows span the dual".

## The honesty finding (a false residual caught)

The residual asks: from `GZPCondition e δ k` *and* a nonsingular **evaluated**
`(Fin t × Fin k)`-minor of the RIM at `φ`, produce dual rows
`h : GZPCopyIdx δ → (ι → F)` whose span is the **entire** Reed–Solomon dual
`dotForm.orthogonal (ReedSolomon.code φ k)`.

But the dual-row index `GZPCopyIdx δ = Σⱼ Fin (δ j)` has cardinality `∑ⱼ δ j`, so the span
of `h` has dimension at most `∑ⱼ δ j`.  Meanwhile the Reed–Solomon dual has dimension
`Fintype.card ι − k` (for `k ≤ card ι`).  For the span to **equal** the dual we would need
`∑ⱼ δ j ≥ card ι − k`.

Now `GZPCondition` only ever delivers the *length bound* `∑ⱼ δ j ≤ card ι − k` (taking
`κ = δ`; see the in-tree documentation in `LovettToGZPDualBridgeReduction.lean`, lines
"taking `κ = δ` only yields `∑ⱼ δⱼ ≤ Fintype.card ι − k`"), and it is satisfied **vacuously**
by `δ ≡ 0` (no `κ ≤ 0` has positive total).  Crucially, the multiplicity `δ` does **not**
appear anywhere in the nonsingular-minor hypothesis — that hypothesis constrains only
`e`, `φ`, and the chosen `rows`.  So we may take `δ ≡ 0` *independently* of any minor.

With `δ ≡ 0` the index `GZPCopyIdx δ` is **empty**, hence `Set.range h = ∅` and
`Submodule.span F (Set.range h) = ⊥`.  But the Reed–Solomon dual is **nonzero** whenever
`k < card ι` (it has dimension `card ι − k > 0`).  So the demanded equality `⊥ = (RS dual)`
is impossible.

To make the countermodel fully concrete (so the nonsingular-minor hypothesis is genuinely
satisfiable, not vacuously assumed-then-contradicted), we take `t = 0`: then
`Fin t × Fin k = Fin 0 × Fin k` is **empty**, the selected submatrix is the `0 × 0` matrix,
whose determinant is `1 ≠ 0` *automatically*.  Thus the hypothesis holds with no work, for
any `e`, `φ`, `rows`.

Conclusion: `DualRowsFromNonsingularEval ι F k` is **refutable** for every `ι, F, k` with
`k < Fintype.card ι` (e.g. `ι = Fin 2`, `F = ZMod 2`, `k = 1`).  It is therefore NOT
dischargeable as stated; the connector's reliance on it is the place where the missing GM-MDS
content (the multiplicity total `∑ⱼ δ j = card ι − k` and the actual kernel construction) was
silently dropped.

This is the canonical "named residual is actually `False`" catch: the fix is to **re-state**
the residual with the multiplicity total pinned (`∑ⱼ δ j = Fintype.card ι − k`, the genuine
GM-MDS dimension count, which holds in every intended instance via `gzp_of_orientation` where
`δⱼ = indeg(j)` summing to `card ι − k`), so that the span equality is dimensionally possible.
We do not edit `LovettDualSpanConnector.lean` (a sibling agent owns that surface); we record
the refutation here, axiom-clean.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

/-- The Reed–Solomon dual is nonzero when `k < card ι`: it has finrank `card ι − k > 0`. -/
theorem reedSolomonDual_ne_bot {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [Field F] {k : ℕ} (φ : ι ↪ F) (hk : k < Fintype.card ι) :
    AGL24.dotForm.orthogonal (ReedSolomon.code φ k) ≠ ⊥ := by
  classical
  intro hbot
  -- finrank of the dual is `card ι − k`, which is positive; but `⊥` has finrank 0.
  have hcode : Module.finrank F (ReedSolomon.code φ k) = k := by
    have := ReedSolomon.dim_eq_deg_of_le' (α := φ) (n := k) (le_of_lt hk)
    simpa [LinearCode.dim] using this
  -- The ambient space `ι → F` has finrank `card ι`.
  have hamb : Module.finrank F (ι → F) = Fintype.card ι := by
    simp
  -- For a nondegenerate form, `finrank (orthogonal W) = finrank ambient − finrank W`.
  have horth :
      Module.finrank F (AGL24.dotForm.orthogonal (ReedSolomon.code φ k))
        = Module.finrank F (ι → F) - Module.finrank F (ReedSolomon.code φ k) :=
    LinearMap.BilinForm.finrank_orthogonal AGL24.dotForm_nondegenerate (ReedSolomon.code φ k)
  rw [hbot, finrank_bot, hcode, hamb] at horth
  omega

/-- **The countermodel.**  `DualRowsFromNonsingularEval ι F k` is `False` whenever
`k < Fintype.card ι` and an evaluation embedding `φ : ι ↪ F` exists.  We instantiate the
residual at `t = 0` (so the selected minor is the `0 × 0` matrix, whose determinant is
`1 ≠ 0` *automatically*), `δ ≡ 0` (so `GZPCondition` holds vacuously and `GZPCopyIdx δ` is
empty, forcing the produced span to be `⊥`), and the supplied embedding `φ` — but the
Reed–Solomon dual is nonzero, so the demanded span equality `⊥ = (RS dual)` is impossible.
Axiom-clean. -/
theorem not_dualRowsFromNonsingularEval {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {F : Type*} [Field F] {k : ℕ} (φ : ι ↪ F) (hk : k < Fintype.card ι) :
    ¬ DualRowsFromNonsingularEval ι F k := by
  classical
  intro hdual
  -- `t = 0`: edges over `Fin 1`, the empty edge map.
  set e : ι → Finset (Fin (0 + 1)) := fun _ => (∅ : Finset (Fin 1)) with he
  -- `δ ≡ 0`.
  set δ : Fin (0 + 1) → ℕ := fun _ => 0 with hδ
  -- `GZPCondition e δ k` holds vacuously: no `κ ≤ δ` has positive total.
  have hgzp : AGL24.GZPCondition e δ k := by
    intro κ hκ hpos
    exfalso
    have hzero : ∑ j, κ j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have := hκ j
      simp only [hδ] at this
      omega
    omega
  -- The row selector `Fin 0 × Fin k → RIMRowIdx e` is the unique map out of an empty type.
  have hempty : IsEmpty (Fin 0 × Fin k) := inferInstance
  -- Choose the (unique) such map.
  let rows : Fin 0 × Fin k → AGL24.RIMRowIdx e := fun x => (hempty.elim x)
  -- The `0 × 0` evaluated minor has determinant `1 ≠ 0`.
  have hdet : (((AGL24.RIM F e).submatrix rows id).map (MvPolynomial.eval (φ ·))).det ≠ 0 := by
    have : (((AGL24.RIM F e).submatrix rows id).map (MvPolynomial.eval (φ ·))).det = 1 := by
      apply Matrix.det_isEmpty
    rw [this]; exact one_ne_zero
  -- Apply the residual.
  obtain ⟨h, _hsupp, hspan⟩ := hdual e δ hgzp φ rows hdet
  -- `GZPCopyIdx δ` is empty (each fibre `Fin (δ j) = Fin 0`), so `Set.range h = ∅`.
  haveI hidx_empty : IsEmpty (AGL24.GZPCopyIdx δ) := by
    constructor
    rintro ⟨j, m⟩
    exact (Nat.not_lt_zero m.val (by simpa [hδ] using m.isLt))
  have hrange : Set.range h = (∅ : Set (ι → F)) := Set.range_eq_empty h
  rw [hrange, Submodule.span_empty] at hspan
  exact reedSolomonDual_ne_bot φ hk hspan.symm

/-- **Concrete instance of the refutation.**  Over `ι = Fin 2`, `F = ZMod 2`, `k = 1`
(so `k = 1 < 2 = card ι`), with the identity embedding `Fin 2 ↪ ZMod 2`, the residual fails.
This shows the countermodel is inhabited (not a vacuous statement). Axiom-clean. -/
theorem not_dualRowsFromNonsingularEval_fin2 :
    ¬ DualRowsFromNonsingularEval (Fin 2) (ZMod 2) 1 := by
  have φ : (Fin 2) ↪ (ZMod 2) := ⟨fun i => (i : ZMod 2), by decide⟩
  exact not_dualRowsFromNonsingularEval φ (by decide)

/-! ## The repaired residual

The refutation isolates the missing hypothesis: the dual-row index must carry **enough**
copies to span a `card ι − k`-dimensional space.  In every *intended* GM-MDS instance the
multiplicity total is exactly the dual dimension — `gzp_of_orientation` builds `δ` from a head
orientation with `δⱼ = indeg(j)` off the root and `δᵣ = indeg(r) − k`, so
`∑ⱼ δⱼ = (∑ⱼ indeg j) − k = (number of edges) − k = card ι − k` (each edge has one head).
`GZPCondition` alone forgets this equality (it keeps only the `≤` direction), which is what made
the residual refutable.

The faithful statement pins the total.  We record it as a named `Prop`; its full proof is the
genuine GM-MDS kernel construction (build the `∑δ = card ι − k` edge-supported dual vectors from
the evaluated RIM kernel and apply `LinearIndependent.span_eq_top_of_card_eq_finrank`), which is
**not** in-tree — it is the actual mathematical content the connector was abstracting, and stays
an explicit named obligation rather than a vacuous discharge. -/
def DualRowsFromNonsingularEvalPinned (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : Type*) [Field F] (k : ℕ) : Prop :=
  ∀ {t : ℕ}, ∀ e : ι → Finset (Fin (t + 1)), ∀ δ : Fin (t + 1) → ℕ,
    AGL24.GZPCondition e δ k →
    -- the missing dimension pin: enough copies to span the dual.
    (∑ j, δ j = Fintype.card ι - k) →
    ∀ (φ : ι ↪ F) (rows : Fin t × Fin k → AGL24.RIMRowIdx e),
      (((AGL24.RIM F e).submatrix rows id).map (MvPolynomial.eval (φ ·))).det ≠ 0 →
    ∃ h : AGL24.GZPCopyIdx δ → (ι → F),
      (∀ a : AGL24.GZPCopyIdx δ, ∀ i : ι, a.vertex ∉ e i → h a i = 0) ∧
      Submodule.span F (Set.range h) =
        AGL24.dotForm.orthogonal (ReedSolomon.code φ k)

/-- **The dimensional obstruction vanishes under the pin.**  When `∑ⱼ δⱼ = card ι − k`, the
dual-row index `GZPCopyIdx δ` has exactly the cardinality of the Reed–Solomon dual's finrank,
so a spanning family of dual rows is dimensionally *possible* (it must be a basis).  This is the
positive consequence of the repair — the necessary condition the unpinned residual violated.
Axiom-clean. -/
theorem gzpCopyIdx_card_eq_dual_finrank {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [Field F] {t : ℕ} {δ : Fin (t + 1) → ℕ} {k : ℕ} (φ : ι ↪ F)
    (hk : k ≤ Fintype.card ι) (hpin : ∑ j, δ j = Fintype.card ι - k) :
    Fintype.card (AGL24.GZPCopyIdx δ)
      = Module.finrank F (AGL24.dotForm.orthogonal (ReedSolomon.code φ k)) := by
  classical
  have hcard : Fintype.card (AGL24.GZPCopyIdx δ) = ∑ j, δ j := by
    simp [AGL24.GZPCopyIdx, Fintype.card_sigma]
  have hcode : Module.finrank F (ReedSolomon.code φ k) = k := by
    have := ReedSolomon.dim_eq_deg_of_le' (α := φ) (n := k) hk
    simpa [LinearCode.dim] using this
  have hamb : Module.finrank F (ι → F) = Fintype.card ι := by simp
  have horth :
      Module.finrank F (AGL24.dotForm.orthogonal (ReedSolomon.code φ k))
        = Module.finrank F (ι → F) - Module.finrank F (ReedSolomon.code φ k) :=
    LinearMap.BilinForm.finrank_orthogonal AGL24.dotForm_nondegenerate (ReedSolomon.code φ k)
  rw [hcode, hamb] at horth
  rw [hcard, hpin, horth]

end ArkLib.GMMDS

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.GMMDS.reedSolomonDual_ne_bot
#print axioms ArkLib.GMMDS.not_dualRowsFromNonsingularEval
#print axioms ArkLib.GMMDS.not_dualRowsFromNonsingularEval_fin2
#print axioms ArkLib.GMMDS.gzpCopyIdx_card_eq_dual_finrank
