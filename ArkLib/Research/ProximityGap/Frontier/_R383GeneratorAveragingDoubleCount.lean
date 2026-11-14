/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# R383: primitive-generator averaging as an incidence double count

R377 shows that an odd exponent multiplier need not preserve the kernel at one fixed generator.
The correct replacement is to average over all primitive generators.  The subgroup, hence its
collision load, is unchanged when the generator changes; after swapping sums, each characteristic-
zero endpoint is weighted by the number of primitive generators at which it vanishes.

This file proves the finite double-counting engine independently of the cyclotomic packaging.  If
every generator has load `L` and every endpoint is incident to at most `B` generators, then

```text
card(A) * L <= B * totalEndpointMass.
```

Thus a nontrivial primitive-root multiplicity bound is a genuine cross-orbit input, unlike the
cosmetic fixed-generator rotation compression audited in R382.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R383GeneratorAveragingDoubleCount

variable {A D : Type*} [DecidableEq A] [DecidableEq D]

/-- Total endpoint mass incident to one generator. -/
def generatorLoad (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] (a : A) : ℕ :=
  ∑ d ∈ S.filter (rel a), w d

/-- Number of generators at which one endpoint vanishes. -/
def endpointIncidence (T : Finset A) (rel : A → D → Prop)
    [DecidableRel rel] (d : D) : ℕ :=
  (T.filter (fun a => rel a d)).card

/-- **Exact generator/endpoint incidence double count.** -/
theorem sum_generatorLoad_eq_sum_endpointIncidence
    (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] :
    ∑ a ∈ T, generatorLoad S w rel a =
      ∑ d ∈ S, w d * endpointIncidence T rel d := by
  classical
  unfold generatorLoad endpointIncidence
  calc
    (∑ a ∈ T, ∑ d ∈ S.filter (rel a), w d) =
        ∑ a ∈ T, ∑ d ∈ S, if rel a d then w d else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_filter]
    _ = ∑ d ∈ S, ∑ a ∈ T, if rel a d then w d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ S, w d * (T.filter fun a => rel a d).card := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp [Nat.mul_comm]

/-- A pointwise incidence cap bounds the averaged generator load. -/
theorem sum_generatorLoad_le_of_endpointIncidence_le
    (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] (B : ℕ)
    (hB : ∀ d ∈ S, endpointIncidence T rel d ≤ B) :
    ∑ a ∈ T, generatorLoad S w rel a ≤ B * ∑ d ∈ S, w d := by
  rw [sum_generatorLoad_eq_sum_endpointIncidence]
  calc
    (∑ d ∈ S, w d * endpointIncidence T rel d) ≤
        ∑ d ∈ S, w d * B := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.mul_le_mul_left (w d) (hB d hd)
    _ = B * ∑ d ∈ S, w d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      exact Nat.mul_comm (w d) B

/-- **Uniform-load consumer.** If changing primitive generator leaves the kernel load equal to
`L`, an endpoint root-multiplicity cap `B` yields `card(T) * L <= B * total mass`. -/
theorem card_mul_load_le_of_uniform_of_endpointIncidence_le
    (T : Finset A) (S : Finset D) (w : D → ℕ) (rel : A → D → Prop)
    [DecidableRel rel] (L B : ℕ)
    (huniform : ∀ a ∈ T, generatorLoad S w rel a = L)
    (hB : ∀ d ∈ S, endpointIncidence T rel d ≤ B) :
    T.card * L ≤ B * ∑ d ∈ S, w d := by
  have havg := sum_generatorLoad_le_of_endpointIncidence_le T S w rel B hB
  calc
    T.card * L = ∑ _a ∈ T, L := by simp
    _ = ∑ a ∈ T, generatorLoad S w rel a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (huniform a ha).symm
    _ ≤ B * ∑ d ∈ S, w d := havg

end ArkLib.ProximityGap.Frontier.R383GeneratorAveragingDoubleCount

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R383GeneratorAveragingDoubleCount.card_mul_load_le_of_uniform_of_endpointIncidence_le
