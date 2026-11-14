/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic

/-!
# Double-counting balance for a negation-closed carrier (#444, AvY)

For a finite negation-closed `Finset S ⊆ ℂ` (`x ∈ S ↔ -x ∈ S`) with `0 ∉ S`, the pairing
`x ↦ -x` is a **fixed-point-free involution** on `S`. Consequently:

* `|S|` is **even** (`negationClosed_card_even`), and
* `∑_{x ∈ S} x = 0` (`negationClosed_sum_eq_zero`), since each antipodal pair `{x, -x}`
  contributes `x + (-x) = 0`.

The headline `negationClosed_double_count_balance` bundles fixed-point-freeness, even
cardinality, and the zero sum together: the antipodal involution partitions `S` into
`|S| / 2` negation pairs, all summing to zero.

This is the elementary double-counting / zero-sum form underpinning the antipodal-balance
bookkeeping (LENS item 3). It specializes the in-tree `_AvX_AntipodalTransversalEvenCardLe`
even-card result to the `ℂ` double-count setting and additionally records the automatic zero
sum. Reusable plumbing for the Wick-matching argument and the No-Excess ladder.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Pure plumbing — it does not
touch the open prize wall.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Frontier.NegationClosedDoubleCount

/-- For negation-closed `S ⊆ ℂ` avoiding `0`, no element is its own negation:
`x = -x ⟹ 2x = 0 ⟹ x = 0`, contradicting `0 ∉ S`. -/
theorem neg_fixedPointFree (S : Finset ℂ) (h0 : (0 : ℂ) ∉ S) :
    ∀ x ∈ S, x ≠ -x := by
  intro x hx hcontra
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
  have h2a : (2 : ℂ) * x = 0 := by linear_combination hcontra
  rcases mul_eq_zero.mp h2a with h' | h'
  · norm_num at h'
  · exact hx0 h'

/-- **`|S|` is even** for negation-closed `S ⊆ ℂ` avoiding `0`: `x ↦ -x` is a
fixed-point-free involution on `S`. -/
theorem negationClosed_card_even (S : Finset ℂ) (h0 : (0 : ℂ) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) : Even S.card := by
  classical
  have hsum : ∑ _x ∈ S, (1 : ZMod 2) = 0 := by
    apply Finset.sum_involution (fun x _ => -x)
    · intro a _; decide
    · intro a ha _ hcontra
      exact neg_fixedPointFree S h0 a ha hcontra.symm
    · intro a _; exact neg_neg a
    · intro a ha; exact hneg a ha
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hdvd : (2 : ℕ) ∣ S.card :=
    (CharP.cast_eq_zero_iff (ZMod 2) 2 S.card).mp (by exact_mod_cast hsum)
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨c, by omega⟩

/-- **Zero sum.** For negation-closed `S ⊆ ℂ` avoiding `0`, `∑_{x ∈ S} x = 0`: each
antipodal pair `{x, -x}` contributes `x + (-x) = 0`. -/
theorem negationClosed_sum_eq_zero (S : Finset ℂ) (h0 : (0 : ℂ) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) : ∑ x ∈ S, x = 0 := by
  classical
  apply Finset.sum_involution (fun x _ => -x)
  · intro a _; exact add_neg_cancel a
  · intro a ha _ hcontra; exact neg_fixedPointFree S h0 a ha hcontra.symm
  · intro a _; exact neg_neg a
  · intro a ha; exact hneg a ha

/-- **Double-count balance (bundled).** For a finite negation-closed `S ⊆ ℂ` with `0 ∉ S`:
the pairing `x ↦ -x` is a fixed-point-free involution, hence `|S|` is even and `∑_{x∈S} x = 0`;
moreover `|S| = 2 · (|S| / 2)` records the partition into `|S|/2` negation pairs. -/
theorem negationClosed_double_count_balance (S : Finset ℂ) (h0 : (0 : ℂ) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) :
    (∀ x ∈ S, x ≠ -x) ∧ Even S.card ∧ (∑ x ∈ S, x = 0) ∧ S.card = 2 * (S.card / 2) := by
  refine ⟨neg_fixedPointFree S h0, negationClosed_card_even S h0 hneg,
    negationClosed_sum_eq_zero S h0 hneg, ?_⟩
  obtain ⟨c, hc⟩ := negationClosed_card_even S h0 hneg
  omega

end ArkLib.ProximityGap.Frontier.NegationClosedDoubleCount

#print axioms ArkLib.ProximityGap.Frontier.NegationClosedDoubleCount.neg_fixedPointFree
#print axioms ArkLib.ProximityGap.Frontier.NegationClosedDoubleCount.negationClosed_card_even
#print axioms ArkLib.ProximityGap.Frontier.NegationClosedDoubleCount.negationClosed_sum_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.NegationClosedDoubleCount.negationClosed_double_count_balance
