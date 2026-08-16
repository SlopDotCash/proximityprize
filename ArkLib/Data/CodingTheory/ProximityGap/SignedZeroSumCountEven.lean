/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyParity

/-!
# The zero-sum count of a negation-closed `0`-free set is EVEN — at ALL orders, incl. ODD (#444)

`NegationClosedWalk.zeroSumCount G m` is the campaign's `m`-tuple zero-sum count, the object the
located thinness-essential SIGNED period-power sum equals (`SignedPeriodZeroSumBridge`):
`∑_ψ η_ψ^r = q · zeroSumCount S r`, and `∑_{ψ≠0} η_ψ^r = q · zeroSumCount S r − |S|^r`.

This file proves a clean **parity** structural fact on that count, holding at **every** order `m`
— including the ODD orders the always-`2r` additive-energy framework cannot see:

>   over a field of characteristic `≠ 2`, if `G` is negation-closed (`∀ g ∈ G, −g ∈ G`) and
>   `0 ∉ G`, then `2 ∣ zeroSumCount G m` for every `m ≥ 1`.

## The mechanism (the new content)

The **global negation** involution `c ↦ −c` (negate every coordinate, `Fin m → F`) acts on the
zero-sum tuples: it maps `G`-tuples to `G`-tuples (negation-closedness) and preserves the zero-sum
constraint (`∑_i (−c i) = −∑_i c i = 0`). It is **fixed-point free** on the zero-sum set: a fixed tuple
of length `m ≥ 1` would need `−c i = c i` at coordinate `i`, i.e. `2 · c i = 0`; in characteristic
`≠ 2` this forces `c i = 0`, impossible since `c i ∈ G` and `0 ∉ G`. A fixed-point-free involution on a
finite set forces **even** cardinality (reusing `AdditiveEnergyParity.card_filter_fixed_modEq_card_of_involutive`,
the same involution-parity engine that handles the inversion involution `u ↦ u⁻¹` for the BGK kernel —
here applied to the *global negation* `c ↦ −c`, a different involution on a different object). Hence
`2 ∣ zeroSumCount G m`.

(For `m = 0` the single empty tuple has empty sum `0`, so `zeroSumCount G 0 = 1` is ODD — the
hypothesis `m ≠ 0` is needed and present. The interesting regime is `m ≥ 1`, where the result holds
unconditionally, in particular at the ODD `m` the energy ladder's `2r`-fold sum-of-squares cannot
reach. The char `≠ 2` hypothesis is harmless in the prize regime: `q = p^k` with `p ≡ 1 mod n` odd.)

## Why this is prize-relevant (honest scope)

The parity `2 ∣ zeroSumCount S r` is a genuine *structural* constraint on the SIGNED prize object
`∑_{ψ≠0} η_ψ^r = q · zeroSumCount S r − |S|^r` at general `r` — it pins `q·zeroSumCount` to an even
multiple of `q`, the kind of rigidity the sign-blind `|·|`/moment route discards. It is **NON-MOMENT**
(pure additive-tuple counting, no `|·|`), **field-universal** in char `≠ 2` (any `0 ∉ G` negation-closed
`G`, any `m ≥ 1`), and **EXTEND-proven** (reuses the in-tree involution-parity lemma + sits directly on
`zeroSumCount`). It is NOT a CORE bound: bounding `∑_{ψ≠0} η_ψ^r` *quantitatively* at `r ≈ log q`
remains the open BGK wall. `CORE  M(μ_n) ≤ C·√(n·log(q/n))  OPEN.`

Probe: `scripts/probes/probe_odd_zerosumcount.py` (EXACT, thin `μ_n` `n ∈ {4,8}`, `p ≡ 1 mod n`,
`(p−1)/n ≥ 2`, NEVER `n = q−1`): `zeroSumCount(μ_n, r)` is EVEN for every `r ∈ {1,2,3,4,5}` and every
probed prime, and `q·W_r − n^r` is `< 0` for ODD `r`, `> 0` for EVEN `r` (the genuine signed structure).

Issue #444.
-/
set_option linter.unusedSectionVars false


open scoped BigOperators

namespace ArkLib.ProximityGap.NegationClosedWalk

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- The **global negation** map on tuples: `negTuple c = fun i => -(c i)`. -/
def negTuple {m : ℕ} (c : Fin m → F) : Fin m → F := fun i => -(c i)

@[simp] theorem negTuple_apply {m : ℕ} (c : Fin m → F) (i : Fin m) :
    negTuple c i = -(c i) := rfl

theorem negTuple_involutive {m : ℕ} :
    Function.Involutive (negTuple (F := F) (m := m)) := by
  intro c
  funext i
  simp [negTuple]

/-- **The zero-sum count of a negation-closed `0`-free set is EVEN, at every order `m ≥ 1`** (char
`≠ 2`). The global negation `c ↦ −c` is a fixed-point-free involution on the zero-sum `m`-tuples of
`G` (fixed-point-free because a fixed coordinate forces `2·c i = 0`, hence `c i = 0 ∉ G` in char
`≠ 2`), so the count is even. Holds at ODD `m` too — the regime the `2r`-fold additive-energy ladder
cannot express. -/
theorem two_dvd_zeroSumCount {m : ℕ} (hm : m ≠ 0) (h2 : (2 : F) ≠ 0) (G : Finset F)
    (hneg : ∀ g ∈ G, -g ∈ G) (h0 : (0 : F) ∉ G) :
    2 ∣ zeroSumCount G m := by
  classical
  -- The filtered zero-sum set.
  set s : Finset (Fin m → F) :=
    (Fintype.piFinset (fun _ : Fin m => G)).filter (fun c => ∑ i, c i = 0) with hs
  -- `negTuple` maps `s` into itself.
  have hmaps : ∀ c ∈ s, negTuple c ∈ s := by
    intro c hc
    rw [hs, mem_filter, Fintype.mem_piFinset] at hc ⊢
    refine ⟨fun i => hneg _ (hc.1 i), ?_⟩
    have hsum : ∑ i, negTuple c i = -(∑ i, c i) := by
      simp only [negTuple_apply, Finset.sum_neg_distrib]
    rw [hsum, hc.2, neg_zero]
  -- the involution-parity engine: #fixed ≡ #s [MOD 2]
  have hpar := ArkLib.ProximityGap.AdditiveEnergyKernel.card_filter_fixed_modEq_card_of_involutive
    (negTuple (F := F) (m := m)) negTuple_involutive s hmaps
  -- there are NO fixed points: `negTuple c = c` forces a coordinate `c i = 0 ∈ G`, contradiction.
  have hnofix : (s.filter fun c => negTuple c = c) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro c hc hfix
    -- membership of `c` in `s`: each coordinate lies in `G`.
    rw [hs, mem_filter, Fintype.mem_piFinset] at hc
    -- evaluate the fixed-point equation at coordinate `i0 := ⟨0, _⟩`.
    set i0 : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩ with hi0
    have hcoord : negTuple c i0 = c i0 := congrFun hfix i0
    rw [negTuple_apply] at hcoord
    -- `-(c i0) = c i0` ⟹ `2 * (c i0) = 0` ⟹ (char ≠ 2) `c i0 = 0`.
    have h2c : (2 : F) * c i0 = 0 := by
      linear_combination -hcoord
    have hcz : c i0 = 0 := by
      rcases mul_eq_zero.mp h2c with h | h
      · exact absurd h h2
      · exact h
    exact h0 (hcz ▸ hc.1 i0)
  -- conclude: #fixed = 0, so `0 ≡ #s [MOD 2]`, i.e. `2 ∣ #s = zeroSumCount G m`.
  rw [hnofix, Finset.card_empty] at hpar
  have : zeroSumCount G m = s.card := rfl
  rw [this]
  exact (Nat.modEq_zero_iff_dvd.mp hpar.symm)

end ArkLib.ProximityGap.NegationClosedWalk

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.NegationClosedWalk.two_dvd_zeroSumCount
