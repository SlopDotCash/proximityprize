/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSLambdaSubJohnson
import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA

/-!
# Sub-Johnson list decoding ⇒ MCA for explicit RS codes (#389, the LD⇒MCA chain)

Composing the sub-Johnson `Λ` bound (`rsCode_Lambda_subJohnson_le`) with the ABF26 T5.1 consumer
gives the **full LD⇒MCA chain for explicit Reed–Solomon codes, below the Johnson radius** — the
first time the two grand challenges are wired end-to-end on the RS side without a Johnson gate:

> **`rsCode_epsMCA_subJohnson_le_of_residual`** — for `k ≤ a`, `a ≤ (1−δ)·n`, and `0 < η ≤ δ < 1`,
> with `L := C(n,k)/C(a,k)`,
> ```
> ε_mca(rsCode dom k, 1 − √(1−δ+η)) ≤ (L²·δ·n + 1/η) / |F|
> ```
> conditional on the single named GKL24 maximal-domain residual that the whole §5 first-moment
> route is already atomized to (`GKL24MaxCorrWitnessCoverHypothesis`, all in-tree glue proven).

The list-size input `Λ ≤ L` is supplied unconditionally and below Johnson by
`rsCode_Lambda_subJohnson_le`; the only external content is the GKL24 first-moment theorem, which
is the recognized open kernel of the MCA side.
-/

open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap ListDecodable CodingTheory

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The sub-Johnson LD⇒MCA bound for RS.** Composing `rsCode_Lambda_subJohnson_le` (the
list-size input, valid below Johnson) with ABF26 T5.1, conditional on the named GKL24
maximal-domain first-moment residual. -/
theorem rsCode_epsMCA_subJohnson_le_of_residual (dom : Fin n ↪ F) {k a : ℕ} {δ η : ℝ}
    (hk : 1 ≤ k) (hka : k ≤ a) (hn : 0 < Fintype.card (Fin n))
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (ha : (a : ℝ) ≤ (1 - δ) * (Fintype.card (Fin n) : ℝ))
    (hres : ProximityGap.GKL24MaxCorrWitnessCoverHypothesis (rsCode dom k)
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) δ.toNNReal
        (((n.choose k / a.choose k : ℕ) : ℝ) ^ 2)) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤
      ENNReal.ofReal
        ((((n.choose k / a.choose k : ℕ) : ℝ) ^ 2 * δ * Fintype.card (Fin n) + 1 / η)
          / Fintype.card F) :=
  CodingTheory.linear_listSize_to_epsMCA_gcxk25_of_gkl24_maxCorr_witnessCover_hypothesis
    (rsCode dom k) (n.choose k / a.choose k) δ η
    hδ_pos hδ_lt hη_pos hη_lt hη_le_δ
    (rsCode_Lambda_subJohnson_le dom hk hka hn ha)
    hres

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.rsCode_epsMCA_subJohnson_le_of_residual
