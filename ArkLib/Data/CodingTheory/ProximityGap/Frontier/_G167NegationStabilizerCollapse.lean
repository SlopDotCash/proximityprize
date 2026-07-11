/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# G167: the negation stabilizer collapses every minimal zero-sum support to a `{x, -x}` pair

The G165 / scaling-ladder arc reduces the primitive census residue mod `2^k` to an action of the
cyclic 2-Sylow `H ≤ F_p^*` on the *minimal zero-sum supports*.  The Fable referee sketch claimed a
coset-stabilizer classification in which dyadic sizes `s ∈ {2,4,8,…}` could carry nontrivial
stabilizers.  An exact enumeration (`p = 17, 41, 97`; see `oc_coset_stabilizer_probe.out`) shows the
truth is *sharper and simpler*:

> the only minimal zero-sum support with any nontrivial `2`-power stabilizer is a `{x, -x}` pair,
> and it is stabilized only by the order-two element `-1`.

The reason is a **subcoset obstruction** the coset sketch missed.  Any nontrivial `2`-power scaling
`u` (order `d ≥ 2`) has `u^{d/2} = -1` in a field (the unique element of multiplicative order two), so
if `u · S = S` then already `-1 · S = S`, i.e. `S = -S`.  A negation-symmetric set of nonzero field
elements (characteristic `≠ 2`) is a disjoint union of two-element antipodal pairs `{x, -x}`, each of
which is *itself* a zero-sum subset.  Minimality forbids a proper nonempty zero-sum subset, so `S`
consists of exactly one pair and `S.card = 2`.

This file formalizes the clean invariant with **no `axiom`, no `sorry`**, over an arbitrary field of
characteristic `≠ 2`:

```text
  S ≠ ∅, 0 ∉ S, S = -S, and S is a minimal zero-sum support  ⟹  S.card = 2.
```

Consequences for the census (see `DISPROOF_LOG.md`):

* the accident sector of the primitive residue is **exactly** the size-two supports;
* for every support size `s ≠ 2` the `2`-Sylow `H` acts *freely*, so `2^k ∣ N_s`;
* the residue arc is a congruence, not a magnitude bound — it cannot by itself move the production
  census scale, which is where BGK/Paley still binds.

**Honest scope.**  This is a structural finite-field group-action theorem: it exactly classifies the
fixed-point sector of negation on minimal zero-sum supports.  It does not bound `N_s` in magnitude and
does not touch the BGK barrier.  CORE remains **open**.  Issue #466 (G167).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G167NegationStabilizerCollapse

open Finset

variable {K : Type*} [Field K] [DecidableEq K]

/-- A finite set `S` of field elements is a **zero-sum support** if it is nonempty, avoids `0`, and
its elements sum to `0`. -/
structure IsZeroSumSupport (S : Finset K) : Prop where
  nonempty : S.Nonempty
  zero_not_mem : (0 : K) ∉ S
  sum_zero : ∑ x ∈ S, x = 0

/-- A zero-sum support is **minimal** if no proper nonempty subset is itself a zero-sum support;
concretely, every nonempty `T ⊆ S` with `∑ T = 0` is all of `S`. -/
structure IsMinimalZeroSumSupport (S : Finset K) : Prop extends IsZeroSumSupport S where
  minimal : ∀ T : Finset K, T ⊆ S → T.Nonempty → (∑ x ∈ T, x = 0) → T = S

/-- **Antipodal pairs are zero-sum.**  The two-element set `{x, -x}` sums to `0`
(in any characteristic; the pair is genuinely two-element only when `char ≠ 2`, hypothesis `hx2`). -/
theorem sum_antipodal_pair (x : K) (hx2 : x ≠ -x) :
    ∑ y ∈ ({x, -x} : Finset K), y = 0 := by
  rw [Finset.sum_pair hx2]
  ring

/-- The two-element antipodal pair `{x, -x}` really has two elements when `x ≠ -x`. -/
theorem card_antipodal_pair (x : K) (hx2 : x ≠ -x) :
    ({x, -x} : Finset K).card = 2 := by
  rw [Finset.card_pair hx2]

section CharNeTwo

omit [DecidableEq K] in
/-- In characteristic `≠ 2`, a nonzero element is not its own negation. -/
theorem ne_neg_self_of_ne_zero (hchar : (2 : K) ≠ 0) {x : K} (hx : x ≠ 0) : x ≠ -x := by
  intro h
  apply hx
  -- `x = -x` gives `2 * x = 0`, and `2 ≠ 0` forces `x = 0`.
  have hsum : x + x = 0 := by
    calc x + x = x + (-x) := by rw [← h]
    _ = 0 := by ring
  have h2 : (2 : K) * x = 0 := by rw [two_mul]; exact hsum
  rcases mul_eq_zero.mp h2 with hc | hx0
  · exact absurd hc hchar
  · exact hx0

/-- If `x ∈ S` and `S = -S` (negation-invariant), then `-x ∈ S`. -/
theorem neg_mem_of_neg_invariant {S : Finset K} (hsymm : S.image (fun y => -y) = S)
    {x : K} (hx : x ∈ S) : -x ∈ S := by
  rw [← hsymm]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- **The negation-stabilizer collapse.**

Let `K` be a field of characteristic `≠ 2`.  If `S` is a minimal zero-sum support that is invariant
under negation (`S = -S`), then `S.card = 2`; in fact `S = {x, -x}` for any `x ∈ S`.

This is the exact fixed-point classification: the only minimal zero-sum supports with a nontrivial
`2`-power scaling stabilizer are the antipodal pairs. -/
theorem card_eq_two_of_neg_invariant (hchar : (2 : K) ≠ 0) {S : Finset K}
    (hS : IsMinimalZeroSumSupport S) (hsymm : S.image (fun y => -y) = S) :
    S.card = 2 := by
  obtain ⟨x, hx⟩ := hS.toIsZeroSumSupport.nonempty
  have hx0 : x ≠ 0 := fun h => hS.toIsZeroSumSupport.zero_not_mem (h ▸ hx)
  have hxne : x ≠ -x := ne_neg_self_of_ne_zero hchar hx0
  have hnegx : -x ∈ S := neg_mem_of_neg_invariant hsymm hx
  -- The antipodal pair {x, -x} is a nonempty zero-sum subset of S.
  have hsub : ({x, -x} : Finset K) ⊆ S := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hx
    · exact hnegx
  have hpne : ({x, -x} : Finset K).Nonempty := ⟨x, by simp⟩
  have hpsum : ∑ y ∈ ({x, -x} : Finset K), y = 0 := sum_antipodal_pair x hxne
  -- Minimality forces the pair to be all of S.
  have hpair : ({x, -x} : Finset K) = S := hS.minimal _ hsub hpne hpsum
  rw [← hpair, card_antipodal_pair x hxne]

/-- **Free-action corollary (fixed-point-free form).**

For any support size `s ≠ 2`, a negation-invariant minimal zero-sum support of that size cannot
exist.  Equivalently, negation has no fixed points on minimal zero-sum supports of size `≠ 2`, so on
the size-`s` supports (`s ≠ 2`) the group `{1, -1}` — and hence any cyclic `2`-power group containing
it — acts freely. -/
theorem no_neg_invariant_support_of_card_ne_two (hchar : (2 : K) ≠ 0) {S : Finset K}
    (hS : IsMinimalZeroSumSupport S) (hcard : S.card ≠ 2)
    (hsymm : S.image (fun y => -y) = S) : False :=
  hcard (card_eq_two_of_neg_invariant hchar hS hsymm)

end CharNeTwo

/-! ## Axiom audit -/
#print axioms card_eq_two_of_neg_invariant
#print axioms no_neg_invariant_support_of_card_ne_two
#print axioms sum_antipodal_pair

end ArkLib.ProximityGap.Frontier.G167NegationStabilizerCollapse
