/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.ToMathlib.BKR06Agreement
import ArkLib.ToMathlib.BKR06Close
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# BKR06 Lemma 3.5: closeness from a subspace (agreement-count discharged)

This file fuses the two already-proven halves of the BKR06 `hclose` residual:

* the **geometric** half — `BKR06.evalOnPoints_agreement_card_ge`
  (`ArkLib.ToMathlib.BKR06Agreement`): the evaluation vectors of `pivot` and
  `pivot − s_W` agree on `≥ Fintype.card W` points;
* the **arithmetic** half — `BKR06Close.mem_closeCodewordsRel_of_agreement`
  (`ArkLib.ToMathlib.BKR06Close`): an agreement count `≥ a` plus the closeness
  parameter inequality `q^(β−1) ≤ a/N` gives membership in `closeCodewordsRel`.

The fusion, `evalOnPoints_mem_closeCodewordsRel_of_param`, says: for a finite
𝔽-subspace `W ⊆ K` with `domain` surjective, the word
`evalOnPoints domain (pivot − s_W)` lies in `closeCodewordsRel C w δ`
(with `w = evalOnPoints domain pivot`, `δ = 1 − q^(β−1)`, `q = |𝔽|`) **provided**:

* `hc` — it is a codeword of `C` (the low-degree interpolant membership — a separate,
  geometric BKR06 input, kept as a named hypothesis), and
* `hparam` — the closeness parameter inequality `q^(β−1) ≤ |W|/|K|` (the honest
  *dimension-threshold* residual `β ≤ v`, exactly as BKR06 derives it — kept named, not
  fabricated).

**What this brick removes:** the agreement-count gap is now fully discharged from `hclose`.
The remaining residual surface for the per-subspace `hclose` of
`rs_lambda_superpoly_extension_bkr06_of_family` is *exactly* `(hc)` codeword membership and
`(hparam)` the dimension inequality — no agreement-count obligation remains.  No real
quantity is bounded by fiat: every external input is an explicit, named hypothesis.

All declarations compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

open Polynomial BigOperators Finset ListDecodable

namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [Module F K]

/-- **BKR06 Lemma 3.5 closeness from a subspace (agreement-count discharged).**  For a
finite 𝔽-subspace `W ⊆ K` with `domain` surjective, the word
`evalOnPoints domain (pivot − s_W)` (`s_W = subspacePoly (subFinset W)`) lies in the
`δ`-close-codeword set of `w = evalOnPoints domain pivot`, given that it is a codeword
(`hc`) and the closeness parameter inequality `q^(β−1) ≤ |W|/|K|` holds with
`δ = 1 − q^(β−1)`, `q = |𝔽|`.  The agreement count `≥ |W|` is supplied internally by
`evalOnPoints_agreement_card_ge`; only the codeword-membership and the dimension-threshold
inequality remain as (named, honest) hypotheses. -/
lemma evalOnPoints_mem_closeCodewordsRel_of_param
    (domain : K ↪ K) (hsurj : Function.Surjective domain)
    (pivot : K[X]) (k : ℕ) (W : Submodule F K) [Fintype W]
    (β δ : ℝ)
    (hc : (ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W)))
            ∈ (ReedSolomon.code domain k : Set (K → K)))
    (hδdef : δ = 1 - (Fintype.card F : ℝ) ^ (β - 1))
    (hparam : (Fintype.card F : ℝ) ^ (β - 1)
                ≤ (Fintype.card W : ℝ) / Fintype.card K) :
    (ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W)))
      ∈ closeCodewordsRel ((ReedSolomon.code domain k : Set (K → K)))
          (ReedSolomon.evalOnPoints domain pivot) δ := by
  classical
  refine BKR06Close.mem_closeCodewordsRel_of_agreement
    ((ReedSolomon.code domain k : Set (K → K)))
    (ReedSolomon.evalOnPoints domain pivot)
    (ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W)))
    (Fintype.card W) (Fintype.card F) β δ hc ?_ ?_ hδdef ?_
  · -- agreement count `≥ |W|`
    exact evalOnPoints_agreement_card_ge domain hsurj pivot W
  · -- `|W| ≤ |K|`
    exact Fintype.card_le_of_injective (fun w : W => (w : K)) Subtype.val_injective
  · -- parameter inequality, with `Fintype.card ι = Fintype.card K`
    exact hparam

end BKR06
