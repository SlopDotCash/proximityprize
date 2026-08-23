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

/-- **The Theorem 2.11 interface from pinning witnesses**: composed with brick 18's
evaluated⟹symbolic reduction. After this, the entire campaign rests on producing pinning
witnesses (GM-MDS + Frank) and the §3 recursion. -/
theorem symbolicFullRank_of_pinning {k : ℕ}
    (hwitness : ∀ {t : ℕ}, 1 ≤ t → ∀ e : ι → Finset (Fin (t + 1)),
      (∀ i, (e i).Nonempty) →
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
      ∃ φ : ι ↪ F, PinningProperty (k := k) φ e)
    (hnonempty : ∀ {t : ℕ}, ∀ e : ι → Finset (Fin (t + 1)),
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
      ∀ i, (e i).Nonempty) :
    SymbolicFullRankResidual (ι := ι) F k := by
  refine symbolicFullRankResidual_of_evaluated_witness fun {t} ht e hwpc => ?_
  obtain ⟨φ, hpin⟩ := hwitness ht e (hnonempty e hwpc) hwpc
  exact ⟨fun i => φ i, fun w hker =>
    evaluated_witness_of_pinning ht φ e (hnonempty e hwpc) hwpc hpin w hker⟩

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.evaluated_witness_of_pinning
#print axioms AGL24.symbolicFullRank_of_pinning
