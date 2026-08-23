/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TowerResidualFloorMuTwo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AntipodalAgreementScope
import Mathlib.Tactic.LinearCombination

/-!
# The `mu_2` base-rung list is a SMALL CONSTANT in the tower's scope (#444 / #407)

`_TowerResidualFloorMuTwo` pinned the off-BGK antipodal-tower residual to the base rung
`mu_2 = {1, -1}` and proved the trivial `rootCount(Q, mu_2) <= 2`, leaving the *actual base-rung
list upper bound* as the open content: "whether the off-BGK route's residual list is small".

This file lands that bound, POSITIVELY. The descent only applies to even/odd agreement polynomials
(`_AntipodalAgreementScope`: `P.comp(-X) = P` or `= -P` is exactly the antipodally-closed-root-set
condition the squaring recursion needs). Restricting to *that scope*, the `mu_2` root count is
**quantized**:

> for an even or odd polynomial `P` over a field of characteristic `!= 2`,
> `rootCount(P, mu_2) in {0, 2}` -- it is NEVER `1`.

This is the genuine, `p`-independent, `n`-independent finite structural fact at the base rung. Its
consequence is the list bound:

* `evenOrOdd_rootCount_mu2_ne_one` : an even/odd `P` has `rootCount(P, mu_2) != 1`.
* `evenOrOdd_rootCount_mu2_zero_or_two` : an even/odd `P` has `rootCount(P, mu_2) = 0 OR = 2`
  (all-or-nothing on the antipodal pair).
* `evenOrOdd_saturating_pattern_unique` : the only *saturating* (rootCount `= 2`) root pattern an
  even/odd `P` can have on `mu_2` is the FULL pair `{1, -1}` -- so the base-rung saturating list
  has size exactly `1`. (Unrestricted polynomials admit `4` patterns `{}, {1}, {-1}, {1,-1}`; the
  tower scope cuts this to `2` achievable patterns, and exactly `1` saturating one.)

## Why this is the POSITIVE answer to the open residual

`_TowerResidualFloorMuTwo` showed `mu_2` is the genuine residual FLOOR (the saving condition there is
`Q`-dependent, not degree-forced). The open question it left was the SIZE of that residual list. The
quantization above answers it: WITHIN THE TOWER'S SCOPE (the even/odd agreement polynomials the
antipodal descent actually applies to) the base-rung agreement-pattern list is a constant `<= 2`,
with a UNIQUE saturating pattern `{1, -1}`. So the off-BGK route's base-rung list is provably small
and independent of both `n` and `p`. Combined with the saving dichotomy
`towerDescent_saving_iff` and the telescope, this says: the antipodal tower, on its symmetric
sub-family, bottoms out at a base rung whose list is a fixed constant -- the descent introduces no
unbounded base list. (This does NOT touch the NON-symmetric worst case, which remains the open BGK
core: the quantization is exactly what the even/odd hypothesis buys, and the non-symmetric word
escapes it -- `_AntipodalAgreementScope`.)

## The mechanism (one line)

Even: `P(-1) = P(1)`. Odd: `P(-1) = -P(1)`. Either way `P(1) = 0 <-> P(-1) = 0`, so the two
evaluation points are roots *together or not at all*. The forbidden middle value `rootCount = 1`
(exactly one of `+-1` a root) is precisely the asymmetry the even/odd hypothesis rules out.

## Honest scope (rules 1, 3, 4, 6)

POSITIVE result inside a refutation-with-mechanism scope: it proves the off-BGK tower's base-rung
residual list is a small constant ON THE EVEN/ODD SUB-FAMILY the descent applies to. Char-free
(needs only `char != 2`, so `-1 != 1`), `n`-independent, `p`-independent finite combinatorics about
the fixed `2`-element group `{1, -1}`. It does NOT close CORE and is NOT thinness-essential: the
general non-symmetric agreement polynomial is outside the even/odd scope and is the open BGK core.
CORE `M(mu_n) <= C * sqrt(n * log(p/n))` stays OPEN.

Probe `scripts/probes/probe_mu2_residual.py` (and the in-file enumeration this brick was derived
from): even/odd polys of every degree `<= 4` over `F_p`, `p in {3,5,7,11,13,17}`, show root counts
on `mu_2` taking values ONLY in `{0, 2}` (zero instances of `1`); the achievable root patterns are
exactly `{}` and `{1,-1}` (2 of the 4 possible), with `{1,-1}` the unique saturating one.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issues #444, #407.
-/

open Polynomial

namespace ProximityGap.Frontier.TowerBaseRungListMuTwo

open ProximityGap.Frontier.AntipodalAgreementScope

variable {F : Type*} [Field F]

/-! ## The two evaluation points of `mu_2` are distinct (char `!= 2`) -/

/-- Over a field of characteristic `!= 2`, the two base points `1` and `-1` are distinct. -/
theorem one_ne_neg_one {p : ℕ} [CharP F p] (hp : p ≠ 2) : (1 : F) ≠ -1 := by
  -- `IsPrimitiveRoot (-1) 2` (from `_TowerResidualFloorMuTwo`'s machinery) makes `-1` a primitive
  -- second root, in particular `-1 != 1`; we use `neg_one_eq_one_iff` + `CharP -> ringChar`.
  have hchar : ringChar F = p := (ringChar.eq F p)
  intro h
  have : (-1 : F) = 1 := h.symm
  rw [neg_one_eq_one_iff] at this
  rw [hchar] at this
  exact hp this

/-! ## The all-or-nothing quantization (the core fact) -/

/-- **`1` is a root iff `-1` is a root, for even/odd `P`.** Even: `P(-1) = P(1)`. Odd:
`P(-1) = -P(1)`. In both cases `P(1) = 0 <-> P(-1) = 0`, so the two base points of `mu_2` are roots
*together or not at all*. -/
theorem isRoot_one_iff_isRoot_neg_one {P : F[X]} (hP : P.comp (-X) = P ∨ P.comp (-X) = -P) :
    P.IsRoot (1 : F) ↔ P.IsRoot (-1 : F) := by
  have h := isRoot_neg_iff_of_even_or_odd hP (1 : F)
  -- `h : P.IsRoot (-1) <-> P.IsRoot 1`
  exact h.symm

/-- **Every element of `mu_2` is `1` or `-1`.** From `β^2 = 1` we get `(β-1)(β+1) = 0`. -/
theorem mem_mu2_eq_one_or_neg_one {β : F} (hβ : β ∈ nthRootsFinset 2 (1 : F)) :
    β = 1 ∨ β = -1 := by
  rw [mem_nthRootsFinset (by norm_num)] at hβ
  have hfac : (β - 1) * (β + 1) = 0 := by linear_combination hβ
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by linear_combination h)

/-- **Root-ness is constant on `mu_2` for even/odd `P`.** For `β ∈ mu_2 = {1,-1}` and an even/odd
`P`, `P.IsRoot β ↔ P.IsRoot 1` (the value `P(1)` and `P(-1)` vanish together). This is the bridge
that makes the `mu_2` filter all-or-nothing. -/
theorem isRoot_mu2_iff_isRoot_one {P : F[X]} (hP : P.comp (-X) = P ∨ P.comp (-X) = -P)
    {β : F} (hβ : β ∈ nthRootsFinset 2 (1 : F)) :
    P.IsRoot β ↔ P.IsRoot (1 : F) := by
  rcases mem_mu2_eq_one_or_neg_one hβ with h | h
  · rw [h]
  · rw [h]; exact (isRoot_one_iff_isRoot_neg_one hP).symm

open Classical in
/-- **All-or-nothing quantization.** For an even/odd polynomial `P` over a field of characteristic
`!= 2`, the root count on the base group `mu_2 = {1, -1}` is either `0` (neither base point a root)
or `2` (both base points roots) -- it is NEVER `1`. This is the genuine `p`-independent,
`n`-independent finite structural fact the tower scope buys at the base rung. The filter is
all-or-nothing because root-ness is constant on `mu_2` (`isRoot_mu2_iff_isRoot_one`). -/
theorem evenOrOdd_rootCount_mu2_zero_or_two {p : ℕ} [CharP F p] (hp : p ≠ 2) {P : F[X]}
    (hP : P.comp (-X) = P ∨ P.comp (-X) = -P) :
    ((nthRootsFinset 2 (1 : F)).filter (fun β => P.IsRoot β)).card = 0
      ∨ ((nthRootsFinset 2 (1 : F)).filter (fun β => P.IsRoot β)).card = 2 := by
  by_cases h1 : P.IsRoot (1 : F)
  · -- every element of `mu_2` is a root: the filter is all of `mu_2`, card 2.
    right
    have hall : (nthRootsFinset 2 (1 : F)).filter (fun β => P.IsRoot β)
        = nthRootsFinset 2 (1 : F) := by
      apply Finset.filter_true_of_mem
      intro β hβ
      exact (isRoot_mu2_iff_isRoot_one hP hβ).mpr h1
    rw [hall, TowerResidualFloorMuTwo.card_nthRootsFinset_two hp]
  · -- no element of `mu_2` is a root: the filter is empty, card 0.
    left
    have hnone : (nthRootsFinset 2 (1 : F)).filter (fun β => P.IsRoot β) = ∅ := by
      apply Finset.filter_false_of_mem
      intro β hβ hroot
      exact h1 ((isRoot_mu2_iff_isRoot_one hP hβ).mp hroot)
    rw [hnone, Finset.card_empty]

open Classical in
/-- **The forbidden middle value.** An even/odd polynomial NEVER has exactly one base point of
`mu_2` as a root: `rootCount(P, mu_2) != 1`. This is the precise asymmetry the even/odd hypothesis
rules out -- the source of the list bound. -/
theorem evenOrOdd_rootCount_mu2_ne_one {p : ℕ} [CharP F p] (hp : p ≠ 2) {P : F[X]}
    (hP : P.comp (-X) = P ∨ P.comp (-X) = -P) :
    ((nthRootsFinset 2 (1 : F)).filter (fun β => P.IsRoot β)).card ≠ 1 := by
  rcases evenOrOdd_rootCount_mu2_zero_or_two hp hP with h | h <;> omega

open Classical in
/-- **The saturating pattern is unique (the list bound).** If an even/odd polynomial `P` saturates
the trivial bound on `mu_2` (root count `= 2`), then BOTH base points are roots -- so the saturating
root pattern is the single full pair `{1, -1}`. Equivalently: the base-rung *saturating* list within
the tower's even/odd scope has size exactly `1`. (Contrast: unrestricted polynomials realize all `4`
patterns of subsets of `{1,-1}`, and `mu_1` is informationless; the even/odd scope cuts the
achievable patterns to `2` and the saturating ones to `1`, the genuine small-constant base list.) -/
theorem evenOrOdd_saturating_pattern_unique {p : ℕ} [CharP F p] (hp : p ≠ 2) {P : F[X]}
    (hP : P.comp (-X) = P ∨ P.comp (-X) = -P)
    (hsat : ((nthRootsFinset 2 (1 : F)).filter (fun β => P.IsRoot β)).card = 2) :
    P.IsRoot (1 : F) ∧ P.IsRoot (-1 : F) := by
  classical
  have hiff : P.IsRoot (1 : F) ↔ P.IsRoot (-1 : F) := isRoot_one_iff_isRoot_neg_one hP
  -- if `1` is not a root then (by the constancy bridge) NO element of `mu_2` is a root, so the
  -- filtered set is empty (card `0 != 2`), contradicting saturation.
  by_cases h1 : P.IsRoot (1 : F)
  · exact ⟨h1, hiff.mp h1⟩
  · exfalso
    have hnone : (nthRootsFinset 2 (1 : F)).filter (fun β => P.IsRoot β) = ∅ := by
      apply Finset.filter_false_of_mem
      intro β hβ hroot
      exact h1 ((isRoot_mu2_iff_isRoot_one hP hβ).mp hroot)
    rw [hnone, Finset.card_empty] at hsat
    exact absurd hsat (by norm_num)

/-! ## The list-size consequence: at most two achievable patterns -/

open Classical in
/-- **The achievable-pattern list is `<= 2`.** Within the tower's even/odd scope, the root count on
`mu_2` lands in the two-element set `{0, 2}` -- so there are at most two distinct *root-count
classes* (equivalently the empty pattern `{}` and the full pattern `{1,-1}`), versus the four subset
patterns an unrestricted polynomial can realize. This is the base-rung list upper bound: a small,
`n`-independent, `p`-independent constant. -/
theorem evenOrOdd_rootCount_mu2_mem_pair {p : ℕ} [CharP F p] (hp : p ≠ 2) {P : F[X]}
    (hP : P.comp (-X) = P ∨ P.comp (-X) = -P) :
    ((nthRootsFinset 2 (1 : F)).filter (fun β => P.IsRoot β)).card ∈ ({0, 2} : Finset ℕ) := by
  rcases evenOrOdd_rootCount_mu2_zero_or_two hp hP with h | h <;> rw [h] <;> decide

end ProximityGap.Frontier.TowerBaseRungListMuTwo

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.TowerBaseRungListMuTwo.one_ne_neg_one
#print axioms ProximityGap.Frontier.TowerBaseRungListMuTwo.mem_mu2_eq_one_or_neg_one
#print axioms ProximityGap.Frontier.TowerBaseRungListMuTwo.isRoot_one_iff_isRoot_neg_one
#print axioms ProximityGap.Frontier.TowerBaseRungListMuTwo.isRoot_mu2_iff_isRoot_one
#print axioms ProximityGap.Frontier.TowerBaseRungListMuTwo.evenOrOdd_rootCount_mu2_zero_or_two
#print axioms ProximityGap.Frontier.TowerBaseRungListMuTwo.evenOrOdd_rootCount_mu2_ne_one
#print axioms ProximityGap.Frontier.TowerBaseRungListMuTwo.evenOrOdd_saturating_pattern_unique
#print axioms ProximityGap.Frontier.TowerBaseRungListMuTwo.evenOrOdd_rootCount_mu2_mem_pair
