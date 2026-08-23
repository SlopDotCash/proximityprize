/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24RSInstance

/-!
# [AGL24] the front-door bridge: `Lambda` ↔ `listDecodable` and the pointwise implication
# (issue #346, brick 9)

The in-tree front door (`randomRSListDecodingFirstMomentResidual`) states list-decoding
failure through the list-size functional `Λ` (`Lambda C δ ≤ listBound`); the AGL24 chain
speaks `listDecodable`. This brick supplies the dictionary and the per-sample implication:

* `lambda_le_iff_listDecodable` — `Λ(C, δ) ≤ L ↔ listDecodable C δ L` (the `⨆`-over-centres
  functional against the pointwise definition);
* `lambda_gt_gives_wpc_rank_deficit` — **the pointwise front-door implication**: a violation
  of the front-door list bound (`¬ Λ ≤ L`) at any fixed evaluation embedding forces the
  weakly-partition-connected rank-deficit event of the composed chain. This is the
  deterministic kernel of the probability-space wiring: the random-subset front door is a
  `PMF`-average of exactly this statement over `φ := L.toEmbedding`.
-/

open Finset ListDecodable

namespace AGL24

variable {ι F : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F]
  [DecidableEq F]

/-- **The `Λ`/`listDecodable` dictionary**: the list-size functional is at most `L` exactly
when the code is `(δ, L)`-list-decodable. -/
theorem lambda_le_iff_listDecodable (C : Set (ι → F)) (δ : ℝ) (L : ℕ) :
    Lambda C δ ≤ (L : ℕ∞) ↔ listDecodable C δ (L : ℝ) := by
  unfold Lambda listDecodable
  rw [iSup_le_iff]
  constructor
  · intro h y
    have := h y
    have hle : (closeCodewordsRel C y δ).ncard ≤ L := by exact_mod_cast this
    exact_mod_cast hle
  · intro h y
    have := h y
    have hle : (closeCodewordsRel C y δ).ncard ≤ L := by exact_mod_cast this
    exact_mod_cast hle

/-- **The pointwise front-door implication**: a violation of the `Λ ≤ L` list bound for the
Reed–Solomon code at a fixed evaluation embedding (with the [AGL24] radius arithmetic) forces
the weakly-partition-connected rank-deficit event. The random-domain front door is the
`PMF`-average of this statement. -/
theorem lambda_gt_gives_wpc_rank_deficit
    {k L : ℕ} (hL : 1 ≤ L) (φ : ι ↪ F) {r : ℝ} (hr : 0 ≤ r)
    (hk : k ≤ Fintype.card ι)
    (hrad : (L + 1 : ℝ) * r * (Fintype.card ι : ℝ)
      ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ))
    (h : ¬ Lambda (ReedSolomon.code φ k : Set (ι → F)) r ≤ (L : ℕ∞)) :
    ∃ t : ℕ, t + 1 ≤ L + 1 ∧ 1 ≤ t ∧ ∃ g : Fin (t + 1) → Fin k → F,
      ∃ y : ι → F,
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1)))
        (agreementEdge y (rsEval (fun i => φ i) g)) ∧
      ∃ v : Fin t × Fin k → F, v ≠ 0 ∧
        ((RIM F (agreementEdge y (rsEval (fun i => φ i) g))).map
          (MvPolynomial.eval (fun i => φ i))).mulVec v = 0 := by
  rw [lambda_le_iff_listDecodable] at h
  exact not_listDecodable_RS_gives_wpc_rank_deficit hL φ hr hk hrad h

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.lambda_le_iff_listDecodable
#print axioms AGL24.lambda_gt_gives_wpc_rank_deficit
