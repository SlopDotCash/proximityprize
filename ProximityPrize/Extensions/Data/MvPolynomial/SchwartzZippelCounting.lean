/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, Aristotle
-/

import ArkLib.Data.Probability.Notation
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Rat.Star
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.SimpleRing.Principal

/-! ## Schwartz-Zippel derived bound

We state and prove a counting version of the Schwartz-Zippel lemma for multivariate polynomials with
finitely many variables over a (possibly inifinite) field `F`.

The lemma is derived from mathlib's version `MvPolynomial.schwartz_zippel_sup_sum`.
-/

open NNReal ENNReal unitInterval
open scoped ProbabilityTheory ENNReal NNReal BigOperators


/-- The uniform probability of a decidable event equals the ratio of favorable outcomes
to total outcomes, expressed in `ℝ≥0∞`. -/
lemma uniform_prob_eq_card_div {α : Type} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] :
    Pr_{let x ←$ᵖ α}[P x] = ↑((Finset.univ.filter (fun x => P x)).card) / ↑(Fintype.card α) := by
  erw [PMF.map_apply]
  simp [div_eq_mul_inv, Finset.sum_ite]

lemma pmf_prob_le_one {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) :
    Pr_{let x ←$ᵖ α}[P x] ≤ 1 := by
  erw [PMF.bind_apply, tsum_fintype]
  refine le_trans (Finset.sum_le_sum fun _ _ => mul_le_of_le_one_right ( by positivity ) ?_) ?_
  · exact PMF.coe_le_one _ True
  · norm_num
