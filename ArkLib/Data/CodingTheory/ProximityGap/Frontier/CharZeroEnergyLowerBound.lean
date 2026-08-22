/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroWickEnergy
import Mathlib.Tactic

/-!
# The char-0 energy LOWER companion for `μ_{2^k}` (#407): the antipodal injection, base case

The proven char-0 energy UPPER bound is `E_r(μ_n) ≤ (2r−1)‼·n^r`
(`CharZeroWickEnergy.gaussianEnergyBound_dyadic`, via `zeroSumCount_le_doubleFactorial`). Its
load-bearing consumer `NotRamanujanLowerBound.not_ramanujan_of_energy_lb` consumes the matching
LOWER bound `E_r ≥ A` as a **supplied hypothesis** (`hAle : A ≤ rEnergy G r`), which the in-tree
docstring described as "the proven char-0 energy lower bound `E_r(μ_n) ≥ (2r−1)‼·(n/2)_r·2^r`" — but
that lower companion was **never a proven Lean theorem**; the only proven in-tree lower bound was the
diagonal `rEnergy_ge_diag : E_r ≥ |G|^r`.

This file lands the antipodal injection's base case unconditionally for any negation-closed `G`. Use
the product equivalence `Fin r × Fin 2 ≃ Fin (2r)`; a transversal value-vector `t : Fin r → G`
builds a `2r`-tuple whose `(i, 0)` slot is `t i` and `(i, 1)` slot is `−(t i) ∈ G`. Each pair cancels,
so the tuple is zero-sum; distinct `t` give distinct tuples, so:

> `antipodalAdj_card` :  `#{adjacent-antipodal tuples} = |G|^r`,
> `pow_card_le_zeroSumCount` :  `|G|^r ≤ zeroSumCount G (2r)`  (negation-closed `G`).

This re-derives the diagonal constant `|G|^r` through the **antipodal** mechanism (not the diagonal
`v = w`), making the antipodal injection that the `(2r−1)‼·(n/2)_r·2^r` bound needs explicit in Lean
for the first time. The `(2r−1)‼` matching factor and the `(n/2)_r·2^r` distinct-signed-class factor
are the multi-pairing refinement, probe-verified EXACTLY in
`scripts/probes/probe_charzero_energy_lower.py` and `probe_charzero_lower_injection.py` (the injection
over (pairing × distinct-class × sign) is exactly injective with image card `= (2r−1)‼·(n/2)_r·2^r`).
This file lands the single-pairing base case; the multi-pairing disjointness is the remaining brick
(`NOTE` below).

**Honest scope (rules 1, 3, 6).** Char-0 / negation-closed combinatorics — NOT thinness-essential,
does NOT close CORE. It discharges, *with the antipodal mechanism*, the diagonal-order floor; the
super-diagonal `(2r−1)‼` constant (the part exceeding `4^r` that feeds `not_ramanujan` at `r ≥ 6`)
needs the multi-pairing disjointness, left as an honest `NOTE`. Axiom-clean
(`propext, Classical.choice, Quot.sound`). Issue #407.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.CharZeroEnergyLowerBound

open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [DecidableEq F]

/-- The index equivalence `Fin r × Fin 2 ≃ Fin (2r)` (with the `2 * r = r * 2` cast). -/
noncomputable def pairIdx (r : ℕ) : (Fin r × Fin 2) ≃ Fin (2 * r) :=
  (finProdFinEquiv).trans (finCongr (by ring))

/-- Build a `2r`-tuple from a transversal value-vector `t : Fin r → F`: the slot indexed by
`(i, 0)` gets `t i`, the slot indexed by `(i, 1)` gets `−(t i)`. -/
noncomputable def antipodalTuple (r : ℕ) (t : Fin r → F) : Fin (2 * r) → F :=
  fun j =>
    let p := (pairIdx r).symm j
    if p.2 = 0 then t p.1 else - t p.1

/-- The antipodal tuple has zero sum: pairing `(i,0) ↦ t i` with `(i,1) ↦ −t i` cancels. -/
theorem antipodalTuple_sum_zero (r : ℕ) (t : Fin r → F) :
    ∑ j, antipodalTuple r t j = 0 := by
  classical
  -- reindex the sum along the equivalence `pairIdx r`
  rw [← Equiv.sum_comp (pairIdx r) (antipodalTuple r t)]
  -- now a sum over `Fin r × Fin 2`
  rw [Fintype.sum_prod_type]
  -- the inner `Fin 2` sum is `t i + (−t i) = 0`
  have hinner : ∀ i : Fin r, ∑ b : Fin 2, antipodalTuple r t (pairIdx r (i, b)) = 0 := by
    intro i
    rw [Fin.sum_univ_two]
    simp only [antipodalTuple, Equiv.symm_apply_apply]
    -- `b = 0` slot is `t i`, `b = 1` slot is `−t i`
    norm_num
  simp only [hinner, Finset.sum_const_zero]

/-- The antipodal tuple of a transversal `t : Fin r → G` lands in `G^{2r}` when `G` is
negation-closed (`−g ∈ G` for `g ∈ G`). -/
theorem antipodalTuple_mem (r : ℕ) (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G)
    {t : Fin r → F} (ht : ∀ i, t i ∈ G) :
    antipodalTuple r t ∈ Fintype.piFinset (fun _ : Fin (2 * r) => G) := by
  classical
  rw [Fintype.mem_piFinset]
  intro j
  simp only [antipodalTuple]
  split
  · exact ht _
  · exact hneg _ (ht _)

/-- The map `t ↦ antipodalTuple r t` is injective: the value on slot `(i,0)` recovers `t i`. -/
theorem antipodalTuple_injective (r : ℕ) :
    Function.Injective (antipodalTuple (F := F) r) := by
  intro t t' h
  funext i
  have h0 := congrFun h (pairIdx r (i, 0))
  simpa only [antipodalTuple, Equiv.symm_apply_apply] using h0

/-- **The antipodal injection's image card.** The set of zero-sum `2r`-tuples of the form
`antipodalTuple r t` (`t : Fin r → G`) has cardinality exactly `|G|^r` (the injection is injective,
so the image equals the domain card). -/
theorem antipodalAdj_card (r : ℕ) (G : Finset F) :
    ((Fintype.piFinset (fun _ : Fin r => G)).image (antipodalTuple r)).card = G.card ^ r := by
  classical
  rw [Finset.card_image_of_injective _ (antipodalTuple_injective r),
    Fintype.card_piFinset]
  simp

/-- **The char-0 energy LOWER companion, base case (antipodal mechanism).** For any negation-closed
`G` (in particular `G = μ_{2^k}` in char 0, where `−1 = ζ^{n/2} ∈ G`), the zero-sum `2r`-tuple count
is at least `|G|^r`, witnessed by the antipodal injection `t ↦ antipodalTuple r t`:

> `|G|^r ≤ zeroSumCount G (2r)`.

This re-derives the diagonal floor through the **antipodal** (not `v = w`) mechanism — the explicit
injection on which the full `(2r−1)‼·(n/2)_r·2^r` bound is built (probe-verified injective with the
exact super-diagonal count; the multi-pairing disjointness is the remaining brick, see `NOTE`). -/
theorem pow_card_le_zeroSumCount (r : ℕ) (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G) :
    G.card ^ r ≤ zeroSumCount G (2 * r) := by
  classical
  rw [← antipodalAdj_card r G]
  unfold zeroSumCount
  refine Finset.card_le_card ?_
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
  rw [Fintype.mem_piFinset] at ht
  rw [Finset.mem_filter]
  exact ⟨antipodalTuple_mem r G hneg ht, antipodalTuple_sum_zero r t⟩

/-- **The antipodal lower bound, in `rEnergy` form.** For negation-closed `G`, the `r`-fold additive
energy satisfies `|G|^r ≤ E_r(G)`, via the antipodal injection through the proven
`rEnergy = zeroSumCount` bijection. (Same constant as the diagonal `rEnergy_ge_diag`, but routed
through the antipodal mechanism — the base case of the `(2r−1)‼` injection.) This is the
plug-compatible `hAle` input for `NotRamanujanLowerBound.not_ramanujan_of_energy_lb` (at the
diagonal constant; the super-diagonal lift is the `NOTE` brick). -/
theorem pow_card_le_rEnergy (r : ℕ) (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G) :
    G.card ^ r ≤ rEnergy G r := by
  rw [ProximityGap.Frontier.CharZeroWickEnergy.rEnergy_eq_zeroSumCount G r hneg]
  exact pow_card_le_zeroSumCount r G hneg

/-! ## NOTE — the remaining multi-pairing brick (honest scope)

The full lower bound `zeroSumCount G (2r) ≥ (2r−1)‼·(n/2)_r·2^r` for `G = μ_{2^k}` needs the
multi-pairing refinement: an injection over (pairing `σ` × injective antipodal-class choice
`φ : Fin r ↪ {n/2 classes}` × sign vector `ε ∈ {±1}^r`) whose image are the zero-sum tuples
antipodally paired by `σ` with all `r` pair-values in DISTINCT antipodal classes. On that
*generic* (distinct-class) locus the pairing `σ` is UNIQUELY recoverable from the tuple, so the
images over distinct `σ` are disjoint, giving the `(2r−1)‼` factor; the `(n/2)_r·2^r` factor is
the distinct-signed-class choice. The mechanism is FULLY probe-verified, exact, char-0 `μ_{2^k}`:
* `scripts/probes/probe_charzero_energy_lower.py` — `A_r ≤ E_r ≤ Wick` for `n ∈ {2,4,8}, r ∈ {1,2,3}`.
* `scripts/probes/probe_charzero_lower_injection.py` — the (pairing × distinct-class × sign) injection is
  EXACTLY injective with image card `= (2r−1)‼·(n/2)_r·2^r` for `(n,r) ∈ {(4,1),(4,2),(8,1),(8,2)}`.
* `scripts/probes/probe_charzero_persigma_count.py` — the two ingredients of the `card_biUnion`
  assembly: (a) the PER-PAIRING generic count is exactly `(n/2)_r·2^r`, and (b) the per-`σ` generic
  image sets are PAIRWISE DISJOINT across distinct pairings `σ` (confirmed for `(n,r) ∈ {(4,1),(4,2),
  (8,1),(8,2)}`, all pairings). So `E_r ≥ Σ_σ (n/2)_r·2^r = (2r−1)‼·(n/2)_r·2^r`.

The single-pairing base case above (`= |G|^r`) is the `σ = adjacent`, single-class collapse of that
count. The isolated remaining Lean step is the `Finset.card_biUnion` assembly: prove the
unique-`σ`-on-generic-locus lemma (antipodal partners = the unique same-antipodal-class index
pairs) to get `(↑pairings).PairwiseDisjoint genericImage`, then `card_biUnion` sums the per-`σ`
count `(n/2)_r·2^r` over the `(2r−1)‼` pairings. That lifts the constant from `1·|G|^r` to the
super-diagonal `(2r−1)‼`, hence past `4^r` at `r ≥ 6` to feed
`NotRamanujanLowerBound.not_ramanujan_of_energy_lb`. (The disjointness probe (b) is the dual of the
proven UPPER `zeroSumCount_le_pairings` `card_biUnion_le` — same biUnion, opposite inequality.)
-/

end ProximityGap.Frontier.CharZeroEnergyLowerBound

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CharZeroEnergyLowerBound.antipodalTuple_sum_zero
#print axioms ProximityGap.Frontier.CharZeroEnergyLowerBound.pow_card_le_zeroSumCount
#print axioms ProximityGap.Frontier.CharZeroEnergyLowerBound.pow_card_le_rEnergy
