/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R383GeneratorAveragingDoubleCount

/-!
# R384: the centered primitive-generator average

R383 double-counts positive kernel mass over primitive generators.  The prize object is centered,
so this file performs the signed double count.  If `Z(d)` is the number of generators at which an
endpoint vanishes, then averaging the coefficient `q * 1[vanishes] - 1` gives exactly

```text
q * Z(d) - card(generators).
```

Consequently generator averaging closes only if the doubled-walk endpoint measure equidistributes
against primitive-root incidence at density `card(generators) / q`.  The identity precisely states
the cross-generator residual without discarding its negative mass.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R384CenteredGeneratorAverage

open ArkLib.ProximityGap.Frontier.R383GeneratorAveragingDoubleCount

variable {A D : Type*} [DecidableEq A] [DecidableEq D]

/-- Centered signed endpoint load at one generator. -/
noncomputable def centeredGeneratorLoad
    (q : ℝ) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] (a : A) : ℝ :=
  ∑ d ∈ S, (w d : ℝ) * (q * (if rel a d then 1 else 0) - 1)

/-- The centered coefficient obtained after summing over generators. -/
noncomputable def centeredEndpointIncidence
    (q : ℝ) (T : Finset A) (rel : A → D → Prop)
    [DecidableRel rel] (d : D) : ℝ :=
  q * endpointIncidence T rel d - T.card

/-- For one endpoint, summing centered indicators over generators gives `q*Z(d)-card(T)`. -/
theorem sum_centeredIndicator
    (q : ℝ) (T : Finset A) (rel : A → D → Prop) [DecidableRel rel] (d : D) :
    ∑ a ∈ T, (q * (if rel a d then 1 else 0) - 1) =
      q * endpointIncidence T rel d - T.card := by
  classical
  have hindicator :
      ∑ a ∈ T, (if rel a d then (1 : ℝ) else 0) =
        (endpointIncidence T rel d : ℝ) := by
    unfold endpointIncidence
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hindicator]
  simp

/-- **Exact centered generator/endpoint double count.** -/
theorem sum_centeredGeneratorLoad_eq_sum_centeredEndpointIncidence
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] :
    ∑ a ∈ T, centeredGeneratorLoad q S w rel a =
      ∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d := by
  classical
  unfold centeredGeneratorLoad centeredEndpointIncidence
  calc
    (∑ a ∈ T, ∑ d ∈ S, (w d : ℝ) * (q * (if rel a d then 1 else 0) - 1)) =
        ∑ d ∈ S, ∑ a ∈ T,
          (w d : ℝ) * (q * (if rel a d then 1 else 0) - 1) := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ S, (w d : ℝ) *
          (∑ a ∈ T, (q * (if rel a d then 1 else 0) - 1)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
    _ = ∑ d ∈ S, (w d : ℝ) *
          (q * endpointIncidence T rel d - T.card) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [sum_centeredIndicator]

/-- **Uniform centered-load form.** If every generator represents the same subgroup and hence has
the same centered load `L`, the weighted primitive-root discrepancy is exactly `card(T) * L`. -/
theorem card_mul_centeredLoad_eq
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] (L : ℝ)
    (huniform : ∀ a ∈ T, centeredGeneratorLoad q S w rel a = L) :
    (T.card : ℝ) * L =
      ∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d := by
  rw [← sum_centeredGeneratorLoad_eq_sum_centeredEndpointIncidence]
  calc
    (T.card : ℝ) * L = ∑ _a ∈ T, L := by simp
    _ = ∑ a ∈ T, centeredGeneratorLoad q S w rel a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (huniform a ha).symm

/-- **No-gain audit.** For a nonempty generator family with uniform centered load, bounding the
averaged primitive-root discrepancy is equivalent to bounding the original load, with exactly the
cardinality factor and no quantitative slack. -/
theorem centeredLoad_le_iff_average_le
    (q : ℝ) (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] (L W : ℝ) (hT : T.Nonempty)
    (huniform : ∀ a ∈ T, centeredGeneratorLoad q S w rel a = L) :
    L ≤ W ↔
      (∑ d ∈ S, (w d : ℝ) * centeredEndpointIncidence q T rel d) ≤
        (T.card : ℝ) * W := by
  rw [← card_mul_centeredLoad_eq q T S w rel L huniform]
  have hcard : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  constructor
  · exact fun h => mul_le_mul_of_nonneg_left h hcard.le
  · exact fun h => le_of_mul_le_mul_left h hcard

end ArkLib.ProximityGap.Frontier.R384CenteredGeneratorAverage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R384CenteredGeneratorAverage.card_mul_centeredLoad_eq
#print axioms
  ArkLib.ProximityGap.Frontier.R384CenteredGeneratorAverage.centeredLoad_le_iff_average_le
