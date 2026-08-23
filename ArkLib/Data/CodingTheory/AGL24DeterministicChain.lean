/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24SubfamilyTransport
import ArkLib.Data.CodingTheory.AGL24KernelVector

/-!
# [AGL24] the deterministic chain, composed (issue #346, brick 6)

The single end-to-end statement of the deterministic layer: **every bad average-radius list
configuration of Reed–Solomon codewords forces a weakly-partition-connected hypergraph whose
evaluated reduced intersection matrix has a rank deficit** — the exact event the Theorem 1.1
union bound (brick 4) prices via the named Lemma 3.1 interface.

`bad_list_gives_wpc_rank_deficit` composes, in order: Lemma 2.3
(`exists_wpc_subset_of_bad_list`, brick 1) → the `orderEmbOfFin` enumeration of the vertex
subset `J` → the weak-partition-connectivity transport (`weaklyPartitionConnected_preimage`,
brick 5) → the agreement-edge correspondence (`agreementEdge_comp`, brick 5a) → the
not-all-equal supply (`subfamily_not_all_equal`, Remark 2.10) → Lemma 2.8
(`RIM_eval_not_injective`, brick 3).

After this brick, the campaign's remaining items are exactly: the distribution bridge
(distinct-tuple sampling ↔ `uniformSizeSubsetOfLe`) and the §3 certificate proof of the
`RIMFullRankFailureProbResidual` interface.
-/

open Finset

namespace AGL24

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι']
variable {F : Type*} [Field F] [DecidableEq F]

/-- **The composed deterministic chain of [AGL24]**: a bad average-radius list configuration
(`∑ⱼ d(y, c⁽ʲ⁾) ≤ L(n−k)`, pairwise-distinct coefficient vectors) yields a vertex count
`t + 1 ≤ L + 1`, a subfamily `g` of the coefficient vectors, such that the agreement
hypergraph of `g` is `k`-weakly-partition-connected on its full vertex set **and** its
evaluated reduced intersection matrix has a nonzero kernel vector. -/
theorem bad_list_gives_wpc_rank_deficit {L k : ℕ} (hL : 1 ≤ L)
    (α : ι' → F) (f : Fin (L + 1) → Fin k → F) (y : ι' → F)
    (hdistinct : Function.Injective f)
    (hk : k ≤ Fintype.card ι')
    (hdist : ∑ j, hammingDist y (rsEval α f j) ≤ L * (Fintype.card ι' - k)) :
    ∃ t : ℕ, t + 1 ≤ L + 1 ∧ 1 ≤ t ∧ ∃ g : Fin (t + 1) → Fin k → F,
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1)))
        (agreementEdge y (rsEval α g)) ∧
      ∃ v : Fin t × Fin k → F, v ≠ 0 ∧
        ((RIM F (agreementEdge y (rsEval α g))).map (MvPolynomial.eval α)).mulVec v = 0 := by
  classical
  -- Lemma 2.3: the WPC vertex subset.
  obtain ⟨J, hJ2, hJwpc⟩ := exists_wpc_subset_of_bad_list hL y (rsEval α f) hk hdist
  -- Enumerate J.
  set t := J.card - 1 with ht
  have hJcard : J.card = t + 1 := by omega
  have ht1 : 1 ≤ t := by omega
  have htL : t + 1 ≤ L + 1 := by
    have := Finset.card_le_card (Finset.subset_univ J)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  set σ : Fin (t + 1) → Fin (L + 1) := ⇑(J.orderEmbOfFin hJcard) with hσdef
  have hσinj : Function.Injective σ := (J.orderEmbOfFin hJcard).injective
  have himg : Finset.univ.image σ = J := by
    rw [hσdef]
    exact Finset.image_orderEmbOfFin_univ J hJcard
  -- The subfamily.
  refine ⟨t, htL, ht1, fun j' => f (σ j'), ?_, ?_⟩
  · -- WPC: transport, then rewrite the preimage family to the subfamily's agreement edges.
    have htrans := weaklyPartitionConnected_preimage
      (agreementEdge y (rsEval α f)) σ hσinj himg hJwpc
    have hedges : (fun i => (agreementEdge y (rsEval α f) i).preimage σ hσinj.injOn)
        = agreementEdge y (rsEval α (fun j' => f (σ j'))) := by
      funext i
      rw [show agreementEdge y (rsEval α (fun j' => f (σ j')))
          = agreementEdge y (fun j' => rsEval α f (σ j')) from rfl]
      rw [agreementEdge_comp y (rsEval α f) σ hσinj i]
    rw [← hedges]
    exact htrans
  · -- The kernel witness: Lemma 2.8 at the not-all-equal subfamily.
    exact RIM_eval_not_injective α (fun j' => f (σ j')) y
      (subfamily_not_all_equal f hdistinct σ hσinj ht1)

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.bad_list_gives_wpc_rank_deficit
