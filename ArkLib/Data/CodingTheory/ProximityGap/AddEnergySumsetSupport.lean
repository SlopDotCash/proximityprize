/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AddEnergyGcdDegreeBound
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# The sumset-support restriction of the additive-energy / gcd-degree sum (#444, #357)

The committed `addEnergy_le_sum_gcd_degree_sq` (`AddEnergyGcdDegreeBound`) bounds the additive
energy of the root-of-unity subgroup `G = {z : zⁿ = 1}` by a sum **over all of `F`**:

  `E(G) ≤ Σ_{c ∈ F} (deg gcd(Xⁿ−1, (C c−X)ⁿ−1))²`.

That file's prose observes — without proof — that the summand is nontrivial *only* when
`c ∈ G + G` (a common root `ω + ω'` must exist). This file lands that **support restriction** as a
theorem, on the representation-count form (the exact quantity `addEnergy_eq_sum_repFilter_sq` sums):

* `representationSet_empty_of_not_mem_sumset` : `c ∉ G + G ⟹ {z ∈ G : c − z ∈ G} = ∅`.
* `repFilter_card_eq_zero_of_not_mem_sumset`  : hence the representation count `r(c) = 0` off `G+G`.
* `addEnergy_eq_sum_sumset_repFilter_sq` (HEADLINE) : the energy identity, summed **only over the
  sumset** — `E(G) = Σ_{c ∈ G+G} r(c)²`. The index set shrinks from `|F|` to `|G+G| ≤ |G|²` terms.
* `addEnergy_le_sum_sumset_gcd_degree_sq` : the corresponding **sharpened gcd-degree bound**, the
  same `≤ Σ (deg gcd_c)²` but with the index set restricted to the sumset.

**Why this is structural, not a moment bound.** The content is a *sumset-support* fact (the
representation count vanishes off `G+G`), proved purely from the definition of `r(c)` and the
pointwise-sum membership `Finset.mem_add` — no additive-energy *estimate* is asserted. It sharpens
the open Stepanov/resultant target (`Σ_c (deg gcd_c)²`) by replacing the `|F|`-indexed sum with a
`(G+G)`-indexed one, which is the quantity any Stepanov count actually has to control.

Probe `scripts/probes/probe_addenergy_sumset_support.py` (EXACT mod-`p`, thin `μ_n = G`, primes
incl. `p > n³` (12289), NEVER `n = q−1`) confirms `r(c) = 0` AND `deg gcd_c = 0` for every
`c ∉ G+G`, with `|G+G|` an order of magnitude below `|F|` (e.g. `129/12289`).

**Honest scope:** a support/structural restriction, not a CORE closure and not a bound on
`Σ_{c ∈ G+G} (deg gcd_c)²` (that is still the open Stepanov input). Does not pin `δ*`. Thinness
is carried by `G`; no thickness-monotone step is used.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial
open ArkLib.ProximityGap.SubgroupRepresentationRoots
open scoped Pointwise

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

set_option linter.unusedSectionVars false in
/-- **Support restriction (set form).** If `c` is not in the sumset `G + G`, then there is no
`z ∈ G` with `c − z ∈ G`: the representation set `{z ∈ G : c − z ∈ G}` is empty. Indeed any such
`z` would give `c = z + (c − z)` with both summands in `G`, i.e. `c ∈ G + G`. -/
theorem representationSet_empty_of_not_mem_sumset (G : Finset F) {c : F} (hc : c ∉ G + G) :
    G.filter (fun z => c - z ∈ G) = ∅ := by
  classical
  rw [Finset.filter_eq_empty_iff]
  intro z hz hcz
  exact hc (by
    rw [Finset.mem_add]
    exact ⟨z, hz, c - z, hcz, by ring⟩)

/-- **Support restriction (count form).** The representation count `r(c) = #{z ∈ G : c − z ∈ G}`
vanishes for every `c` outside the sumset `G + G`. -/
theorem repFilter_card_eq_zero_of_not_mem_sumset (G : Finset F) {c : F} (hc : c ∉ G + G) :
    (G.filter (fun z => c - z ∈ G)).card = 0 := by
  rw [representationSet_empty_of_not_mem_sumset G hc, Finset.card_empty]

/-- **The additive-energy identity, restricted to the sumset (HEADLINE).** Since the representation
count vanishes off `G + G`, the energy sum `E(G) = Σ_{c ∈ F} r(c)²` is supported on the sumset:

  `E(G) = Σ_{c ∈ G+G} r(c)²`,

so the index set drops from `|F|` to `|G+G| ≤ |G|²`. -/
theorem addEnergy_eq_sum_sumset_repFilter_sq (G : Finset F) :
    addEnergy G
      = ∑ c ∈ (G + G), ((G ×ˢ G).filter (fun xy => xy.1 + xy.2 = c)).card ^ 2 := by
  classical
  rw [addEnergy_eq_sum_repFilter_sq]
  -- The full-`F` sum restricts to `G+G`: the summand vanishes for `c ∉ G+G`.
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro c _ hc
  -- `c ∈ univ` but `c ∉ G+G` ⟹ `r(c) = 0` ⟹ the squared summand is `0`.
  rw [repFilter_card_eq, repFilter_card_eq_zero_of_not_mem_sumset G hc, pow_two, mul_zero]

/-- **Additive energy bounded by the gcd-degree sum, restricted to the sumset.** Combines the
sumset-support restriction with the committed gcd-degree bound: the energy is bounded by
`Σ (deg gcd_c)²` summed **only over `c ∈ G+G`** (not all of `F`). This is the sharpened form of
`addEnergy_le_sum_gcd_degree_sq`; it identifies the Stepanov/resultant target as a sum over the
sumset rather than the whole field. -/
theorem addEnergy_le_sum_sumset_gcd_degree_sq (G : Finset F) {n : ℕ} (hn : 0 < n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) :
    addEnergy G
      ≤ ∑ c ∈ (G + G), ((gcd (Polynomial.X ^ n - 1 : F[X]) (reprPoly c n)).natDegree) ^ 2 := by
  rw [addEnergy_eq_sum_sumset_repFilter_sq]
  refine Finset.sum_le_sum (fun c _ => ?_)
  rw [repFilter_card_eq]
  exact Nat.pow_le_pow_left (representationCount_le_gcd_degree G hn hGmem c) 2

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

/-! ## Axiom audit — kernel-clean. -/
#print axioms
  ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy_eq_sum_sumset_repFilter_sq
#print axioms
  ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy_le_sum_sumset_gcd_degree_sq
