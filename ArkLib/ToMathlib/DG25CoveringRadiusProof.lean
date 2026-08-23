/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# DG25 covering-radius sampling — single-stack sup-dominance (issue #77)

The DG25 Theorem 2.5 / ABF26 Lemma 4.19 covering-radius sampling lower bound for `ε_ca`
proceeds by:

1. choosing a word `w` beyond the covering radius, so that for *every* base word `u₀` the pair
   `(u₀, w)` is never jointly `δ`-close to `C` (the joint distance dominates the row distance,
   which exceeds the covering radius);
2. **dominating the `u₀`-averaged line event by the `ε_ca` supremum**: the stack `![u₀, w]`
   is one term of the `ε_ca` supremum over word-pairs, and since `(u₀, w)` is not jointly close,
   that term *equals* the bare line probability `Pr_{γ}[δᵣ(u₀ + γ•w, C) ≤ δ]`; hence the sup
   dominates it;
3. re-uniformizing the `u₀`-average into `Pr_u[δᵣ(u, C) ≤ δ]` (the translation-averaging heart
   `ArkLib.sum_uniform_line_indicator_eq`) and folding in the `(q-1)/q` nonzero-shift factor.

This module supplies the **step (2)** mechanic as a reusable feeder:
`ProximityGap.epsCA_ge_line_prob_of_not_jointProximity`.  It isolates the supremum-dominance
content (a single `le_iSup` term, the same mechanic used in `one_le_epsCA_of_line_covered`,
but kept as a general lower bound rather than specialized to the line-covered `= 1` case).

It does **not** by itself close the DG25 assembly: the probability bridge from the
`Finset/ENNReal` heart to the `Pr_{...}` notation, the covering-radius far-point existence, and
the `(q-1)/q` averaging remain.
-/

open NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **DG25 L4.19 sup-dominance (single stack).**

For any word-pair stack `u : WordStack A (Fin 2) ι` that is **not** jointly `δ_int`-close to the
interleaved code `C^⋈ (Fin 2)`, the bare line probability `Pr_{γ}[δᵣ(u 0 + γ • u 1, C) ≤ δ_fld]`
is dominated by the correlated-agreement error `ε_ca(C, δ_fld, δ_int)`.

This is the `u`-term of the `epsCA` supremum: when the pair is not jointly close the `if`-branch
of `epsCA`'s body is exactly that line probability, and a single term of a supremum is `≤` the
supremum.  It is the supremum-dominance step (DG25 step 2) of the covering-radius sampling lower
bound: once `w := u 1` is chosen beyond the covering radius so that `(u 0, w)` is never jointly
close, the `ε_ca` supremum dominates the line event for each base word `u 0`. -/
theorem epsCA_ge_line_prob_of_not_jointProximity
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (hu : ¬ jointProximity (C := C) (u := u) δ_int) :
    Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ_fld]
      ≤ epsCA (F := F) C δ_fld δ_int := by
  unfold epsCA
  refine le_trans ?_ (le_iSup _ u)
  rw [if_neg hu]

#print axioms epsCA_ge_line_prob_of_not_jointProximity

end ProximityGap
