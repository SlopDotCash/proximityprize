/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.HigherOrderMDSList
import ArkLib.Data.CodingTheory.HigherOrderMDSReedSolomon


/-!
# Order-2 higher MDS is automatic (the base case of the GM-MDS tower) (#389)

The window-interior δ\* core reduces (see `InterleavedListMDSBound.lean`) to a *sub*-exponential
The window-interior δ\* core reduces (see `InterleavedListMDSBound.lean`) to a sub-exponential
explicit Reed–Solomon frame.  The repo's `IsHigherMDS` tower carried only *failure* certificates
(`not_higherMDS_of_not_generic`); this file adds the first *positive* result, pinning the boundary:

* `isHigherMDS_two_of_isMDSFrame` — **order 2 is automatic from ordinary MDS**.  For disjoint
  `≤ k`-column sets `J₀, J₁`, the sum `frameSpan J₀ ⊔ frameSpan J₁ = frameSpan (J₀ ∪ J₁)` has
  `≥ k` columns whenever `|J₀|+|J₁| ≥ k`, hence is everything (`frameSpan_eq_top_of_card_ge`), so
  Grassmann forces `dim(W₀ ∩ W₁) = |J₀|+|J₁|−k` exactly — generic position.
* `reedSolomonFrame_isHigherMDS_two` — the explicit RS frame at distinct points is order-2 higher
  MDS, unconditionally.

Consequence: the genuine GM-MDS difficulty for explicit points (where `μ_n`-type domains can fail)
is an **order-`≥ 3`** phenomenon — order 2 never fails.  This sharpens exactly where the open δ\*
certificate lives: the first interleaved-list size that the trivial MDS structure cannot control
is `L = 2` (three candidate codewords), needing order-3 generic intersection of explicit spans.
Axiom-clean.
-/
open Finset Module ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Order-2 higher MDS is automatic from ordinary MDS.**  For any MDS frame, every pair of
disjoint `≤ k`-column spans is in generic intersection position: their sum has `≥ k` columns hence
is everything (any `k` MDS columns are a basis), so `dim(W₀ ∩ W₁) = |J₀|+|J₁|−k` exactly by
Grassmann.  Thus the genuine higher-order-MDS content (where explicit points such as `μ_n` can
fail) begins only at order `3`. -/
theorem isHigherMDS_two_of_isMDSFrame {v : ι → V} (hv : IsMDSFrame K v) :
    IsHigherMDS K 2 v := by
  classical
  intro J hcard hdisj
  have hd0 : (J 0).card ≤ finrank K V := hcard 0
  have hd1 : (J 1).card ≤ finrank K V := hcard 1
  have hdisj01 : Disjoint (J 0) (J 1) := hdisj 0 1 (by decide)
  have hsup : frameSpan K v (J 0) ⊔ frameSpan K v (J 1) = frameSpan K v (J 0 ∪ J 1) := by
    simp only [frameSpan]
    rw [← Submodule.span_union, ← Set.image_union, ← Finset.coe_union]
  have hcardU : (J 0 ∪ J 1).card = (J 0).card + (J 1).card :=
    Finset.card_union_of_disjoint hdisj01
  have hiinf : (⨅ i : Fin 2, frameSpan K v (J i))
      = frameSpan K v (J 0) ⊓ frameSpan K v (J 1) := by
    apply le_antisymm
    · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
    · refine le_iInf (fun i => ?_)
      fin_cases i
      · exact inf_le_left
      · exact inf_le_right
  have hgr := Submodule.finrank_sup_add_finrank_inf_eq
    (frameSpan K v (J 0)) (frameSpan K v (J 1))
  rw [hsup, finrank_frameSpan hv hd0, finrank_frameSpan hv hd1] at hgr
  rw [IsGenericInter, hiinf, Fin.sum_univ_two, codim_frameSpan hv hd0, codim_frameSpan hv hd1,
    codim]
  rcases Nat.lt_or_ge (finrank K V) ((J 0).card + (J 1).card) with hgt | hle
  · rw [frameSpan_eq_top_of_card_ge hv (by rw [hcardU]; exact le_of_lt hgt), finrank_top] at hgr
    omega
  · rw [finrank_frameSpan hv (by rw [hcardU]; exact hle)] at hgr
    omega

/-- The explicit Reed–Solomon frame is higher-order MDS of order `2` (unconditionally, for
distinct evaluation points): the genuine GM-MDS difficulty for explicit points is an order-`≥3`
phenomenon. -/
theorem reedSolomonFrame_isHigherMDS_two {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {D : ι → K} (hD : Function.Injective D) {k : ℕ} (hk : 2 ≤ k) :
    IsHigherMDS K 2 (reedSolomonFrame D k) :=
  isHigherMDS_two_of_isMDSFrame (reedSolomonFrame_isMDS hD hk)

end ArkLib.HigherOrderMDS
