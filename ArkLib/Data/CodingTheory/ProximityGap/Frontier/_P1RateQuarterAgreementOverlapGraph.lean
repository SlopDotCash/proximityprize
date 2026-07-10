/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound

/-!
# P1 rate-quarter predecessor: the agreement-overlap graph has independence at most five

At the immediate predecessor of the saturated rate-quarter construction, every explanation
agrees on at least

```text
t = 592794966
```

of the `N = 2^30` coordinates.  Put an edge between two explanations when their agreement sets
overlap on at least `k = 2^28` coordinates.  This file proves that every six vertices contain an
edge.  Equivalently, the large-overlap graph has independence number at most five.

The proof trims six agreement sets to constant weight `t` and applies the exact-diagonal Plotkin
bound with `lambda = k-1`.  Its divided bound is exactly five:

```text
N * (t - (k-1)) / (t^2 - N*(k-1)) = 5.
```

For Reed--Solomon explanations, an overlap of at least `k` coordinates uniquely determines the
polynomial source pencil through the two decoded points.  Thus this is a global forcing input for
the four-pencil extraction programme: a counterexample cannot have six mutually ordinary
explanations whose pairwise agreement overlaps all stay below interpolation dimension.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000

open Finset

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph

open ConstantWeightPlotkinBound

attribute [local instance] Classical.propDecidable

/-- Prize length. -/
abbrev N : Nat := 2 ^ 30

/-- Rate-quarter Reed--Solomon dimension. -/
abbrev K : Nat := 2 ^ 28

/-- Agreement threshold at the lattice predecessor of the saturated common-factor endpoint. -/
abbrev T : Nat := 592794966

/-- The exact Plotkin quotient controlling an independent family of predecessor agreement sets. -/
theorem plotkin_quotient_eq_five :
    (N * (T - (K - 1))) / (T ^ 2 - N * (K - 1)) = 5 := by
  norm_num [N, K, T]

/-- The Plotkin denominator is positive at the P1 rate-quarter predecessor. -/
theorem plotkin_gap_pos : N * (K - 1) < T ^ 2 := by
  norm_num [N, K, T]

/-- **Six-set overlap forcing.**  Among any six subsets of the P1 coordinate set, each of
cardinality at least the predecessor agreement threshold, two distinct sets overlap in at least
the Reed--Solomon dimension `K`.

In the decoded-point geometry this says that every six explanations contain a pair determining a
source pencil on at least `K` common coordinates. -/
theorem exists_pair_inter_card_ge_K_of_six
    (S : Fin 6 → Finset (Fin N))
    (hsize : ∀ i, T ≤ (S i).card) :
    ∃ i j : Fin 6, i ≠ j ∧ K ≤ (S i ∩ S j).card := by
  classical
  by_contra hnot
  push Not at hnot
  let S' : Fin 6 → Finset (Fin N) := fun i =>
    Classical.choose (Finset.exists_subset_card_eq (hsize i))
  have hS'sub : ∀ i, S' i ⊆ S i := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).1
  have hS'card : ∀ i, (S' i).card = T := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).2
  have hpair : ∀ i j, i ≠ j → (S' i ∩ S' j).card ≤ K - 1 := by
    intro i j hij
    have hsmall : (S i ∩ S j).card < K := hnot i j hij
    have hsub : S' i ∩ S' j ⊆ S i ∩ S j :=
      Finset.inter_subset_inter (hS'sub i) (hS'sub j)
    have hle := Finset.card_le_card hsub
    omega
  have hplot := constantWeight_plotkin S' T (K - 1) hS'card hpair
  rw [Fintype.card_fin, Fintype.card_fin] at hplot
  norm_num [N, K, T] at hplot

end ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.plotkin_quotient_eq_five
#print axioms
  ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph.exists_pair_inter_card_ge_K_of_six
