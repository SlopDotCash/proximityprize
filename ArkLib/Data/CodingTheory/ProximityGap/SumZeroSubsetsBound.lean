/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PowerWordListBound
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListBound

/-!
# A combinatorial bound on sum-zero subsets, via Reed–Solomon list decoding (#389)

Composing the power-word list identity `powerWord_list_eq_sumZero` (the agreement-`(k+1)` list of
`x^(k+1)` is exactly the zero-sum `(k+1)`-subset fibre) with the Deza–Frankl sub-Johnson list
bound `rsCode_subJohnson_list_card_le_div` yields a purely combinatorial inequality, proven
through coding theory:

> **`sumZero_subsets_card_le_choose`** — for any injective `dom : Fin n ↪ F` (`F` a field) and
> `1 ≤ k`, the number of `(k+1)`-subsets of the domain whose values sum to zero is
> ```
> #{T : |T| = k+1, ∑_{i∈T} dom i = 0}  ≤  C(n,k) / C(k+1,k)  =  C(n,k)/(k+1).
> ```

This is exactly the tightness witness for the sub-Johnson list bound at the base agreement
`a = k+1`: the power word `x^(k+1)` *attains* `C(n,k)/(k+1)` whenever the domain carries that many
sum-zero `(k+1)`-subsets (e.g. an additive domain, where the count is `Θ(n^k)`), so the
Deza–Frankl bound is sharp there.  It also gives a clean number-theoretic corollary: a field
subset's sum-zero `(k+1)`-subsets are limited by the Reed–Solomon list size.
-/

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **Sum-zero `(k+1)`-subsets are bounded by the RS list size.** A coding-theoretic proof of a
purely combinatorial inequality: `#{sum-zero (k+1)-subsets} ≤ C(n,k)/C(k+1,k)`. -/
theorem sumZero_subsets_card_le_choose (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).filter
        (fun T => ∑ i ∈ T, dom i = 0)).card
      ≤ n.choose k / (k + 1).choose k := by
  rw [← ProximityGap.PowerWord.powerWord_list_eq_sumZero dom k]
  exact rsCode_subJohnson_list_card_le_div dom hk (Nat.le_succ k)
    (ProximityGap.PowerWord.powerWord dom k)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.sumZero_subsets_card_le_choose
