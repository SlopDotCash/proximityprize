/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Protocol counting / rational-identity bricks (LogUp #13, FRI #14)

Mathlib-only algebra underlying two proof systems:

* `Finset.sum_div_mul_prod_eq_sum_mul_prod_erase` — LogUp's clear-denominators / partial-fractions
  core (LogUp eq. 16/18): `(∑ num/den)·(∏ den) = ∑ num·∏_{erase} den`.
* `Finset.fiber_sum_one_div_const_add_eq_card_div` — LogUp's fiber rational identity: summing
  `1/(c + g u)` over the fiber `{u | g u = a}` gives `(fiber card)/(c + a)`.
* `card_someQueryOut_eq` — the FRI/Batched-FRI query-round counting complement: the number of
  length-`t` query tuples that miss the good set `G` in some coordinate is `|ι|^t - |G|^t`.
-/

open Finset

namespace Finset

variable {K : Type*} [Field K]

/-- **LogUp clear-denominators core.** `(∑ num/den)·(∏ den) = ∑ num·∏_{erase} den`. -/
theorem sum_div_mul_prod_eq_sum_mul_prod_erase {α : Type*} [DecidableEq α]
    (s : Finset α) (num den : α → K) (hden : ∀ i ∈ s, den i ≠ 0) :
    (∑ i ∈ s, num i / den i) * (∏ i ∈ s, den i) = ∑ i ∈ s, num i * ∏ j ∈ s.erase i, den j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_prod_erase s den hi]
  field_simp [hden i hi]

/-- **LogUp fiber rational identity.** `∑_{u : g u = a} 1/(c + g u) = (#{u : g u = a})/(c + a)`. -/
theorem fiber_sum_one_div_const_add_eq_card_div {β : Type*} [Fintype β] [DecidableEq K]
    (g : β → K) (a c : K) :
    (∑ u ∈ (univ.filter fun u => g u = a), (1 : K) / (c + g u))
      = (((univ.filter fun u => g u = a).card : K)) / (c + a) := by
  rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

end Finset

/-- **FRI query-round counting complement.** The number of length-`t` query tuples missing the good
set `G` in at least one coordinate is `|ι|^t - |G|^t`. -/
theorem card_someQueryOut_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Finset ι) (t : ℕ) :
    (univ.filter (fun q : Fin t → ι => ¬ ∀ j, q j ∈ G)).card
      = Fintype.card ι ^ t - G.card ^ t := by
  have hall : (univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card = G.card ^ t := by
    have hpi : (univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G))
        = Fintype.piFinset (fun _ : Fin t => G) := by
      ext q; simp [Fintype.mem_piFinset]
    rw [hpi, Fintype.card_piFinset]; simp
  have htot : (univ : Finset (Fin t → ι)).card = Fintype.card ι ^ t := by
    rw [Finset.card_univ, Fintype.card_pi]; simp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin t → ι))) (fun q : Fin t → ι => ∀ j, q j ∈ G)
  rw [hall, htot] at hsplit
  omega

/-- `Finset`-namespaced alias for `card_someQueryOut_eq`. PR #291's salvaged Batched-FRI counting
wrapper (`ProximityGap.Issue14.query_tuple_someQueryOut_card_eq`) references this lemma under the
`Finset.` qualifier even though the brick lives at the root namespace; expose the alias so that
reference resolves robustly across namespace/import drift. -/
theorem Finset.card_someQueryOut_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Finset ι) (t : ℕ) :
    (univ.filter (fun q : Fin t → ι => ¬ ∀ j, q j ∈ G)).card
      = Fintype.card ι ^ t - G.card ^ t :=
  _root_.card_someQueryOut_eq G t

#print axioms Finset.sum_div_mul_prod_eq_sum_mul_prod_erase
#print axioms Finset.fiber_sum_one_div_const_add_eq_card_div
#print axioms card_someQueryOut_eq
