/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24KernelAgreement
import ArkLib.Data.CodingTheory.AGL24VertexDegree
import ArkLib.Data.CodingTheory.AGL24AgreementForcing
import ArkLib.Data.CodingTheory.AGL24RSInstance
import ArkLib.Data.CodingTheory.AGL24EvalToSymbolic

/-!
# [AGL24] the Appendix A main assembly (issue #346, brick 24)

The complete Appendix A argument, threaded: a **pinning witness** — an evaluation embedding
whose Reed–Solomon code absorbs every vector that agrees edge-wise with a codeword family
(the joint output of GM-MDS Theorem A.2 + Corollary A.4's zero pattern: display (A.6)) —
forces the evaluated reduced intersection matrix to have trivial kernel, and hence (brick 18)
discharges the symbolic Theorem 2.11 interface.

* `PinningProperty` — the (A.6) interface: what the zero-pattern dual span actually does;
* `evaluated_witness_of_pinning` — **the Appendix A main proof**: kernel vector → stacked
  blocks (`f⁽ᵗ⁾ = 0`) → edge agreement (brick 23) → the `y` vector → pinning → `y` is a
  codeword → vertex degree (brick 21) + agreement forcing (brick 22) → everything is `y` →
  everything is zero;
* `symbolicFullRank_of_pinning` — composed with brick 18: the Theorem 2.11 interface from
  pinning witnesses alone.

After this brick the **entire** [AGL24] formalization rests on: the pinning witness
(GM-MDS + Frank's theorem, via Corollary A.4's proven counting) and the §3 recursion.
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The (A.6) pinning interface**: every vector agreeing edge-wise with a family of
codewords is itself a codeword. This is exactly what the GM-MDS zero-pattern dual span
provides (each dual row is supported inside one edge-support, so it annihilates `y`). -/
def PinningProperty {t k : ℕ} (φ : ι ↪ F) (e : ι → Finset (Fin (t + 1))) : Prop :=
  ∀ y : ι → F, ∀ c : Fin (t + 1) → ι → F,
    (∀ j, c j ∈ ReedSolomon.code φ k) →
    (∀ i : ι, ∀ j ∈ e i, y i = c j i) →
    y ∈ ReedSolomon.code φ k

/-- **The Appendix A main proof** (conditional on pinning): a pinning witness forces the
evaluated reduced intersection matrix of a weakly-partition-connected hypergraph to have
trivial kernel. -/
theorem evaluated_witness_of_pinning {t k : ℕ} (ht : 1 ≤ t)
    (φ : ι ↪ F) (e : ι → Finset (Fin (t + 1)))
    (hne : ∀ i, (e i).Nonempty)
    (hwpc : WeaklyPartitionConnected k
      (Finset.univ : Finset (Fin (t + 1))) (fun i => e i))
    (hpin : PinningProperty (k := k) φ e)
    (w : Fin t × Fin k → F)
    (hker : ((RIM F e).map (MvPolynomial.eval (fun i => φ i))).mulVec w = 0) :
    w = 0 := by
  classical
  -- The stacked-block family with the last block zero.
  set g : Fin (t + 1) → Fin k → F :=
    fun j m => if h : (j : ℕ) < t then w (⟨(j : ℕ), h⟩, m) else 0 with hg
  have hglast : g (Fin.last t) = 0 := by
    funext m
    rw [hg]
    simp only [Fin.val_last]
    rw [dif_neg (lt_irrefl t)]
    rfl
  have hweq : (fun jm : Fin t × Fin k => g jm.1.castSucc jm.2) = w := by
    funext jm
    rw [hg]
    simp only [Fin.val_castSucc]
    rw [dif_pos jm.1.isLt]
  -- Brick 23: edge-wise agreement of the block evaluations.
  have hagree := kernel_gives_edge_agreement e (fun i => φ i) g hglast (by
    rw [hweq]
    exact hker)
  -- The codeword family.
  have hcode : ∀ j, (fun i => rsEval (fun i => φ i) g j i) ∈ ReedSolomon.code φ k := by
    intro j
    rw [mem_code_iff_exists_coeffs]
    exact ⟨g j, rfl⟩
  -- The y vector: the common edge value.
  set y : ι → F := fun i => rsEval (fun i => φ i) g ((e i).min' (hne i)) i with hy
  have hyagree : ∀ i : ι, ∀ j ∈ e i, y i = rsEval (fun i => φ i) g j i := by
    intro i j hj
    rw [hy]
    exact hagree i ((e i).min' (hne i)) (Finset.min'_mem _ _) j hj
  -- Pinning: y is a codeword.
  have hymem : y ∈ ReedSolomon.code φ k :=
    hpin y (fun j i => rsEval (fun i => φ i) g j i) hcode hyagree
  obtain ⟨f, hf⟩ := (mem_code_iff_exists_coeffs φ y).mp hymem
  -- Vertex degrees: y agrees with each block on ≥ k points.
  have h2 : 1 < Fintype.card (Fin (t + 1)) := by
    rw [Fintype.card_fin]
    omega
  have hforce : ∀ j, f = g j := by
    intro j
    have hdeg := wpc_vertex_degree (fun i => e i) h2 hwpc j
    refine coeff_eq_of_agree (fun i => φ i) φ.injective f (g j) ?_
    refine le_trans hdeg (Finset.card_le_card ?_)
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : y i = ∑ m : Fin k, f m * (φ i) ^ (m : ℕ) := by
      rw [hf]
    have h2 := hyagree i j hi.2
    unfold rsEval at h2
    rw [← h1, h2]
  -- The last block is zero, so everything is.
  have hf0 : f = 0 := by
    rw [hforce (Fin.last t), hglast]
  funext jm
  have := hforce jm.1.castSucc
  rw [hf0] at this
  have hzero : g jm.1.castSucc jm.2 = 0 := by
    rw [← this]
    rfl
  rw [← hweq]
  exact hzero

/-! ### Empty edges carry no rank information

The pinning route needs every edge nonempty (the `y` vector of `evaluated_witness_of_pinning`
reads a value off each edge, and `PinningProperty` genuinely fails when an edge is empty and
`k < card ι`). But weak partition connectivity does **not** force nonempty edges: an empty edge
touches no cell, so it contributes `0 - 1 = 0` to every partition sum. (For instance, at `t = 0`
the all-empty family is `k`-WPC for every `k`.) Earlier versions of the assembly therefore took
a global side premise "every WPC family has only nonempty edges", which is **false** for every
`k` and nonempty `ι`, making the composite discharges vacuous.

The repair below removes that premise: replacing each empty edge by the singleton `{0}` keeps
weak partition connectivity (edges only grow) and adds no RIM rows (a singleton has no
non-minimal vertex), so the symbolic kernel can only shrink. Hence it suffices to prove the
Theorem 2.11 interface for families whose edges are all nonempty. -/

/-- Replace every empty edge by the singleton `{0}`; nonempty edges are unchanged. -/
def fillEmptyEdges {ι' : Type*} {t : ℕ} (e : ι' → Finset (Fin (t + 1))) :
    ι' → Finset (Fin (t + 1)) :=
  fun i => if (e i).Nonempty then e i else {0}

theorem fillEmptyEdges_nonempty {ι' : Type*} {t : ℕ} (e : ι' → Finset (Fin (t + 1)))
    (i : ι') : (fillEmptyEdges e i).Nonempty := by
  unfold fillEmptyEdges
  split_ifs with h
  · exact h
  · exact Finset.singleton_nonempty _

theorem subset_fillEmptyEdges {ι' : Type*} {t : ℕ} (e : ι' → Finset (Fin (t + 1)))
    (i : ι') : e i ⊆ fillEmptyEdges e i := by
  unfold fillEmptyEdges
  split_ifs with h
  · exact Finset.Subset.refl _
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    exact Finset.empty_subset _

/-- Weak partition connectivity is monotone under enlarging edges. -/
theorem weaklyPartitionConnected_mono_edges {V ι' : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι'] {k : ℕ} {s : Finset V} {e e' : ι' → Finset V}
    (hsub : ∀ i, e i ⊆ e' i) (h : WeaklyPartitionConnected k s e) :
    WeaklyPartitionConnected k s e' := by
  intro P
  refine le_trans (h P) (Finset.sum_le_sum fun i _ => Nat.sub_le_sub_right ?_ 1)
  refine Finset.card_le_card fun c hc => ?_
  simp only [touchedCells, Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, hc.2.mono (Finset.inter_subset_inter
    (Finset.inter_subset_inter (hsub i) (Finset.Subset.refl _)) (Finset.Subset.refl _))⟩

omit [Nonempty ι] in
theorem min'_congr_of_eq {α : Type*} [LinearOrder α] {s s' : Finset α} (h : s = s')
    (hs : s.Nonempty) (hs' : s'.Nonempty) : s.min' hs = s'.min' hs' := by
  subst h
  rfl

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype F] [DecidableEq F] in
/-- Filling empty edges adds no RIM rows, so every symbolic kernel vector of `RIM F e` is a
kernel vector of `RIM F (fillEmptyEdges e)`. -/
theorem RIM_fillEmptyEdges_mulVec_eq_zero {t k : ℕ} (e : ι → Finset (Fin (t + 1)))
    (v : Fin t × Fin k → MvPolynomial ι F) (hker : (RIM F e).mulVec v = 0) :
    (RIM F (fillEmptyEdges e)).mulVec v = 0 := by
  classical
  funext r'
  obtain ⟨i, j, hj, j', hj', hlt⟩ := r'
  -- A row needs two distinct vertices, so `e i` was nonempty and is unchanged.
  have hnei : (e i).Nonempty := by
    by_contra hnone
    have hfill : fillEmptyEdges e i = {0} := by
      simp [fillEmptyEdges, hnone]
    rw [hfill, Finset.mem_singleton] at hj hj'
    rw [hj, hj'] at hlt
    exact lt_irrefl _ hlt
  have hfe : fillEmptyEdges e i = e i := by
    simp [fillEmptyEdges, hnei]
  have hj0 : j ∈ e i := hfe ▸ hj
  have hj0' : j' ∈ e i := hfe ▸ hj'
  have hrow := congrFun hker ⟨i, ⟨j, hj0, j', hj0', hlt⟩⟩
  have hentry : ∀ c : Fin t × Fin k,
      RIM F (fillEmptyEdges e) ⟨i, ⟨j, hj, j', hj', hlt⟩⟩ c =
        RIM F e ⟨i, ⟨j, hj0, j', hj0', hlt⟩⟩ c := by
    intro c
    simp only [RIM]
    rw [min'_congr_of_eq hfe ⟨j, hj⟩ ⟨j, hj0⟩]
  simp only [Matrix.mulVec, dotProduct] at hrow ⊢
  simp_rw [hentry]
  exact hrow

omit [DecidableEq ι] [Nonempty ι] [Fintype F] [DecidableEq F] in
/-- **The Theorem 2.11 interface from its nonempty-edge case.** It suffices to prove symbolic
full rank for weakly-partition-connected families all of whose edges are nonempty: a general
family reduces to `fillEmptyEdges e`. This replaces the former (false) global premise that
every WPC family has nonempty edges. -/
theorem symbolicFullRankResidual_of_nonempty_edges {k : ℕ}
    (h : ∀ {t : ℕ}, 1 ≤ t → ∀ e : ι → Finset (Fin (t + 1)),
      (∀ i, (e i).Nonempty) →
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
      ∀ v : Fin t × Fin k → MvPolynomial ι F,
        (RIM F e).mulVec v = 0 → v = 0) :
    SymbolicFullRankResidual (ι := ι) F k := by
  intro t ht e hwpc v hker
  exact h ht (fillEmptyEdges e) (fillEmptyEdges_nonempty e)
    (weaklyPartitionConnected_mono_edges (subset_fillEmptyEdges e) hwpc) v
    (RIM_fillEmptyEdges_mulVec_eq_zero e v hker)

/-- **The Theorem 2.11 interface from pinning witnesses**: composed with brick 18's
evaluated⟹symbolic reduction. Pinning witnesses are only requested for nonempty-edge WPC
families; empty edges are handled by `symbolicFullRankResidual_of_nonempty_edges`. -/
theorem symbolicFullRank_of_pinning {k : ℕ}
    (hwitness : ∀ {t : ℕ}, 1 ≤ t → ∀ e : ι → Finset (Fin (t + 1)),
      (∀ i, (e i).Nonempty) →
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
      ∃ φ : ι ↪ F, PinningProperty (k := k) φ e) :
    SymbolicFullRankResidual (ι := ι) F k := by
  refine symbolicFullRankResidual_of_nonempty_edges fun {t} ht e hne hwpc v hker => ?_
  obtain ⟨φ, hpin⟩ := hwitness ht e hne hwpc
  exact symbolic_kernel_trivial_of_evaluated e (fun i => φ i)
    (fun w hw => evaluated_witness_of_pinning ht φ e hne hwpc hpin w hw) v hker

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.evaluated_witness_of_pinning
#print axioms AGL24.RIM_fillEmptyEdges_mulVec_eq_zero
#print axioms AGL24.symbolicFullRankResidual_of_nonempty_edges
#print axioms AGL24.symbolicFullRank_of_pinning
