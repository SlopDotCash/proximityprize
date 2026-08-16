/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._REnergyThreeScratch
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3NegSymConverse

set_option autoImplicit false

/-!
# The relation energy `rEnergy G 3` equals the count-balanced census in characteristic 0 (#444)

The `r`-fold relation energy `rEnergy G 3 = #{(v,w) ∈ (G³)² : Σv = Σw}` is the object the r=2
cross-step rung consumes. This file identifies it, in characteristic 0, with the **antipodal
count-balanced census** of 6-tuples over `G` — the combinatorial object whose value the strata
producer (`negSymCount_six_closed`, in finite fields) computes to be `15n³ − 45n² + 40n`.

For a negation-closed set `G` of `2^k`-th roots of unity in a characteristic-0 field:

* `rEnergy_three_eq_balancedCensus` — `rEnergy G 3 = #{c : Fin 6 → G | ∀ z, #{c=z} = #{c=−z}}`.
  Two links, both axiom-clean: the bijection `rEnergy G 3 = #{c : Σc = 0}`
  (`rEnergy_three_eq_zeroSumCount`) and the equivalence `Σc = 0 ⟺ count-balanced` (forward
  `fiber_balanced_of_sum_eq_zero` = char-0 Lam–Leung, converse `sum_eq_zero_of_fiber_balanced`).

## Honest scope

* The forward direction needs `[CharZero L]` (it IS the char-0 Lam–Leung structure theorem). The
  census *value* `15n³−45n²+40n` is the finite-field strata producer `E3StrataCharZero` — combining
  the two across the `Fintype`/`CharZero` divide needs the strata machinery generalized off
  `[Fintype F]` (its sole real use is the transversal's order), which is left as a separate step.
* For the proximity prize the relevant `μ_n ⊂ F_p` lives in characteristic `p`, where the forward
  direction is *false at depth* — the BGK/Burgess `√`-cancellation wall, the open core of #444.
  This file does not cross that wall.
-/

open scoped Classical
attribute [local instance] Classical.propDecidable

open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open REnergyThreeScratch (fiber_balanced_of_sum_eq_zero rEnergy_three_eq_zeroSumCount)
open ArkLib.ProximityGap.Frontier.E3NegSymConverse (sum_eq_zero_of_fiber_balanced)

namespace ArkLib.ProximityGap.Frontier.REnergyThreeCharZero

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L]

/-- **`rEnergy G 3` = the antipodal count-balanced census of 6-tuples** for a negation-closed set
`G` of `2^k`-th roots of unity in characteristic 0. The equal-sum relation census equals the
count-balanced census: a tuple over `G` is zero-sum iff antipodally count-balanced (forward =
char-0 Lam–Leung `fiber_balanced_of_sum_eq_zero`, converse = pairing `sum_eq_zero_of_fiber_balanced`). -/
theorem rEnergy_three_eq_balancedCensus {k : ℕ} (G : Finset L) (h0 : (0 : L) ∉ G)
    (hneg : ∀ z ∈ G, -z ∈ G) (hroot : ∀ z ∈ G, z ^ (2 ^ k) = 1) :
    rEnergy G 3
      = ((Fintype.piFinset (fun _ : Fin 6 => G)).filter
          (fun c => ∀ z : L, (Finset.univ.filter (fun i => c i = z)).card
                           = (Finset.univ.filter (fun i => c i = -z)).card)).card := by
  classical
  rw [rEnergy_three_eq_zeroSumCount G hneg]
  refine congrArg Finset.card (Finset.ext fun c => ?_)
  simp only [Finset.mem_filter]
  refine and_congr_right fun hc => ?_
  rw [Fintype.mem_piFinset] at hc
  constructor
  · intro hsum z
    exact fiber_balanced_of_sum_eq_zero (k := k) c (fun i => hroot (c i) (hc i)) hsum z
  · intro hbal
    exact sum_eq_zero_of_fiber_balanced two_ne_zero c (fun i hi => h0 (hi ▸ hc i)) hbal

end ArkLib.ProximityGap.Frontier.REnergyThreeCharZero

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.REnergyThreeCharZero.rEnergy_three_eq_balancedCensus
