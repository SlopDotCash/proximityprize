/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Inv

/-!
# MCA first-moment arithmetic bricks

Self-contained, mathlib-only arithmetic lemmas extracted from the GKL24/MCA first-moment
proximity work (issue #67). Each lemma below mirrors an inline cast/inequality argument that
recurs in the proximity-gap files
`ArkLib/Data/CodingTheory/Connections/GKL24FirstMoment.lean` and
`ArkLib/Data/CodingTheory/Connections/EpsMCABadGlue.lean`, where the first-moment count
`|mcaBadWitness|` is bounded and the per-stack `mcaEvent` probability is repackaged as an
`ENNReal.ofReal` ratio.

The three bricks are pure `Finset`/`NNReal`/`ENNReal` facts with no ArkLib dependency:

* `Finset.card_add_card_le_card_univ_add_card_inter` — the real-valued inclusion-exclusion
  consequence used in `secondSupport_card_le_two_delta_of_two_witnesses` (the `hincl` block):
  two witness supports overlap at least as much as inclusion-exclusion forces inside a finite
  universe.
* `NNReal.coe_one_sub_mul_le` — the lower bound for the real coercion of an `ℝ≥0` truncated
  subtraction `(1 - δ)` times a nonnegative scalar, used in the `hSlb`/`hS'lb` blocks of the
  same theorem.
* `ENNReal.coe_natCast_div_eq_ofReal_div` — rewriting an `ℝ≥0` count/`q` ratio coerced to
  `ℝ≥0∞` as `ENNReal.ofReal ((m:ℝ)/q)`, used in `mcaEvent_prob_le_of_mcaBad_card_le`.

These isolate the reusable arithmetic plumbing; the deep first-moment core
(the GCXK25/GKL24 `|Bad¹| ≤ δ·n` bound) is not addressed here and remains external.
-/

open scoped NNReal ENNReal

namespace Finset

/-- **Real-valued inclusion-exclusion bound over a `Fintype`.** For two finite subsets `s t`
of a finite type `α`, the sum of their cardinalities (as reals) is at most the size of the
universe plus the size of their intersection. This is `card_union_add_card_inter` combined with
`(s ∪ t).card ≤ Fintype.card α`. Used in the `hincl` block of
`secondSupport_card_le_two_delta_of_two_witnesses` (GKL24 first moment). -/
theorem card_add_card_le_card_univ_add_card_inter
    {α : Type*} [Fintype α] [DecidableEq α] (s t : Finset α) :
    (s.card : ℝ) + (t.card : ℝ) ≤ (Fintype.card α : ℝ) + ((s ∩ t).card : ℝ) := by
  have h := Finset.card_union_add_card_inter s t
  have hunion : (s ∪ t).card ≤ Fintype.card α := by
    calc (s ∪ t).card ≤ (Finset.univ : Finset α).card :=
          Finset.card_le_card (fun x _ => Finset.mem_univ _)
      _ = Fintype.card α := Finset.card_univ
  have hcast : ((s ∪ t).card : ℝ) + ((s ∩ t).card : ℝ) =
      (s.card : ℝ) + (t.card : ℝ) := by exact_mod_cast h
  have hu : ((s ∪ t).card : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hunion
  linarith

end Finset

namespace NNReal

/-- **Lower bound for the coercion of a truncated `ℝ≥0` subtraction times a nonneg scalar.**
For `δ : ℝ≥0` and `0 ≤ c`, the real product `(1 - (δ:ℝ)) * c` (which may go negative when
`δ > 1`) is at most the truncated `((1 - δ : ℝ≥0):ℝ) * c`. Proven via `NNReal.coe_sub_def`,
which expresses the coercion of `1 - δ` as `max (1 - (δ:ℝ)) 0`. Used in the `hSlb`/`hS'lb`
blocks of `secondSupport_card_le_two_delta_of_two_witnesses` (GKL24 first moment). -/
theorem coe_one_sub_mul_le (δ : ℝ≥0) {c : ℝ} (hc : 0 ≤ c) :
    (1 - (δ : ℝ)) * c ≤ ((1 - δ : ℝ≥0) : ℝ) * c := by
  refine mul_le_mul_of_nonneg_right ?_ hc
  rw [show ((1 - δ : ℝ≥0) : ℝ) = max (1 - (δ : ℝ)) 0 by rw [NNReal.coe_sub_def]; simp]
  exact le_max_left _ _

end NNReal

namespace ENNReal

/-- **Count/`q` ratio as `ENNReal.ofReal`.** For naturals `m` and a positive denominator `q`,
the `ℝ≥0` ratio `m / q` coerced into `ℝ≥0∞` equals `ENNReal.ofReal ((m:ℝ)/q)`. This is the
cast bridge in `mcaEvent_prob_le_of_mcaBad_card_le` (EpsMCA glue), turning the `ℝ≥0`-valued
probability `|mcaBad| / |F|` into an `ENNReal.ofReal` real ratio so monotonicity of `ofReal`
applies. -/
theorem coe_natCast_div_eq_ofReal_div (m q : ℕ) (hq : 0 < q) :
    (((m : ℝ≥0) / (q : ℝ≥0) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((m : ℝ) / q) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [ENNReal.coe_nnreal_eq]
  norm_num [ENNReal.ofReal_div_of_pos hqpos]

end ENNReal

#print axioms Finset.card_add_card_le_card_univ_add_card_inter
#print axioms NNReal.coe_one_sub_mul_le
#print axioms ENNReal.coe_natCast_div_eq_ofReal_div
