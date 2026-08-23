/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24ReducedIntersectionMatrix
import ArkLib.Data.CodingTheory.AGL24DeletionRobustness

/-!
# [AGL24] Theorem 2.11 as the campaign's single deep interface + Lemma 2.14
# (issue #346, brick 14)

Brick 13's structural discovery: the §3 certificate machinery's only deep algebraic input is
**Theorem 2.11** — the reduced intersection matrix of a `k`-weakly-partition-connected
hypergraph has full column rank over `F_q(X₁,…,Xₙ)` (the GM-MDS-line theorem, proven in the
paper's Appendix A via the hypergraph GM-MDS connection). This brick:

* `SymbolicFullRankResidual` — the named interface, stated at the polynomial level (trivial
  `MvPolynomial` kernel — equivalent to fraction-field full column rank by clearing
  denominators, and the form every consumer wants);
* `RIM_deleted_kernel_trivial` — **Lemma 2.14 in full (conditional)**: row-deleted RIMs of
  `(k+m)`-WPC hypergraphs keep the trivial kernel. The structural choices pay off completely:
  row deletion *is* edge emptying (`RIMRowIdx` of an emptied family loses exactly the deleted
  rows), so the proof is the interface applied to brick 13's deletion robustness — a
  one-line weld where the paper needs a page.

The campaign's residual ledger after this brick: **Theorem 2.11 alone** (a self-contained
algebraic statement with its own Appendix-A proof) plus mechanical certificate bookkeeping.
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : Type*) [Field F]

/-- **The [AGL24] Theorem 2.11 interface** (the campaign's single deep algebraic input): the
reduced intersection matrix of every `k`-weakly-partition-connected edge family has trivial
kernel over the polynomial ring (equivalently, full column rank over the fraction field
`F(X₁,…,Xₙ)`). Proven in the paper's Appendix A through the hypergraph GM-MDS connection
([9, Thm A.2]); consumed here as a named hypothesis by the certificate machinery. -/
def SymbolicFullRankResidual (k : ℕ) : Prop :=
  ∀ {t : ℕ}, 1 ≤ t → ∀ e : ι → Finset (Fin (t + 1)),
    WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
    ∀ v : Fin t × Fin k → MvPolynomial ι F,
      (RIM F e).mulVec v = 0 → v = 0

/-- **[AGL24] Lemma 2.14, full conditional form**: under the Theorem 2.11 interface, the
row-deleted reduced intersection matrix of a `(k+m)`-weakly-partition-connected family
(deletion = emptying the edges of `B`, `|B| ≤ m` — which removes exactly the rows mentioning
those edges' variables) keeps the trivial polynomial kernel. -/
theorem RIM_deleted_kernel_trivial {k m : ℕ}
    (hres : SymbolicFullRankResidual (ι := ι) F k)
    {t : ℕ} (ht : 1 ≤ t) (e : ι → Finset (Fin (t + 1))) (B : Finset ι)
    (hB : B.card ≤ m)
    (hwpc : WeaklyPartitionConnected (k + m)
      (Finset.univ : Finset (Fin (t + 1))) e)
    (v : Fin t × Fin k → MvPolynomial ι F)
    (hker : (RIM F (fun i => if i ∈ B then ∅ else e i)).mulVec v = 0) :
    v = 0 :=
  hres ht (fun i => if i ∈ B then ∅ else e i)
    (weaklyPartitionConnected_delete (Finset.univ) e B hB hwpc) v hker

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.RIM_deleted_kernel_trivial
