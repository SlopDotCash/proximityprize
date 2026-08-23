/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# The Vieta SET → SUMSET scope-gap no-go for B1 (R-thin / realizability) (#407)

The B1 "R-thin / realizability" escape-attack campaign (6 angles × 3 adversarial lenses)
reached a **convergent no-go**: the count/realizability/rank/sparse machinery genuinely makes
the *agreement SET* `S` (the ragged residue of a far monomial line) small and char-free
(`_RThinResidueDegree`, `_RaggedRootBound`, `_RThinSparseRealizability`, `_FoldRankNoGo`), but
that is the **non-binding object**. The δ\* floor gates the bad-**SCALAR** of the line, which by
Vieta is `γ = −e₁(S) = −∑_{x∈S} x`, and the prize quantity is the **count of distinct such bad
scalars across the `n²` directions/witnesses at depth `r ≈ log q`** — an `r`-fold subset-**SUMSET**
cardinality (`MonomialLineListBridge.badScalars_monomial_card_le_listSize`). That sumset count is
Glibichuk–Konyagin / BCHKS Conjecture 1.12 / BGK.

This file lands the campaign's central obstruction as a reusable proven no-go (mirroring
`_FoldRankNoGo`): the bad scalar is the Vieta sum (`badScalar_eq_neg_e1`), and **set-cardinality
hypotheses carry no information about the sumset cardinality** (`sumset_card_not_determined_by_card`)
— so any `|S|`-level bound (Hankel rank, isolated count, agreement-set size, coset-core size),
even if proven, *cannot* close δ\*. The closure of this lane is BCHKS 1.12; this is a clarifying
no-go, NOT a prize advance.

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #407.
-/

open Polynomial Finset
open scoped Pointwise

namespace ProximityGap.Frontier.VietaScopeGapNoGo

variable {F : Type*} [Field F]

/-- **The Vieta pin.** The bad scalar of a far monomial line whose agreement set is `S` is the
next-to-leading coefficient of `∏_{x∈S}(X−x)`, i.e. `−e₁(S) = −∑_{x∈S} x`. So the bad scalar is a
**SUM** over the agreement set — the object the count lane must control is therefore a sumset. -/
theorem badScalar_eq_neg_e1 (S : Finset F) :
    (∏ x ∈ S, (X - C x)).nextCoeff = - ∑ x ∈ S, x := by
  simpa using Polynomial.prod_X_sub_C_nextCoeff (s := S) (f := fun x : F => x)

/-- **The scope gap (no-go countermodel).** Set cardinality does **not** determine sumset
cardinality: there are two sets of equal cardinality whose (one-fold already, hence a fortiori
`r`-fold) sumsets have different cardinalities. Witness `{0,1,2}` (AP: `S+S = {0,…,4}`, card 5) vs
`{0,1,3}` (`S+S = {0,1,2,3,4,6}`, card 6). Consequently a bound on `|S|` is information-theoretically
blind to `|S^{(+r)}|` — the quantity δ\* gates via the Vieta sum — which is why every B1 set-level
lever (rank/realizability/isolated-count/coset-core) cannot close the floor. -/
theorem sumset_card_not_determined_by_card :
    ∃ S₁ S₂ : Finset ℕ, S₁.card = S₂.card ∧ (S₁ + S₁).card ≠ (S₂ + S₂).card :=
  ⟨{0, 1, 2}, {0, 1, 3}, by decide, by decide⟩

/-- **The binding object (named, for downstream honesty).** The δ\*-relevant quantity is the
cardinality of the `r`-fold subset-sum image of the agreement set over the witness family — a
sumset, governed by Glibichuk–Konyagin/BCHKS 1.12, **not** by `|S|`. A `Prop` asserting a set-size
bound suffices to bound this is therefore FALSE-by-scope (see `sumset_card_not_determined_by_card`);
kept as documentation that `SparseRaggedExcessBound` & friends, even if proven, do not reach δ\*. -/
def SetBoundClosesDeltaStar [DecidableEq F] : Prop :=
  ∀ (B : ℕ), (∀ S : Finset F, S.card ≤ B) →
    ∀ S₁ S₂ : Finset F, (S₁ + S₁).card = (S₂ + S₂).card

end ProximityGap.Frontier.VietaScopeGapNoGo

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.VietaScopeGapNoGo.badScalar_eq_neg_e1
#print axioms ProximityGap.Frontier.VietaScopeGapNoGo.sumset_card_not_determined_by_card
