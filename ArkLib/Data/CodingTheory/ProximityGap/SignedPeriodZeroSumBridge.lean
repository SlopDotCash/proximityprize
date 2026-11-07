/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SignedPeriodPowerCount
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound

/-!
# The signed period-power sum, in the canonical `zeroSumCount` vocabulary (#444, #407)

`SignedPeriodPowerCount.signedPeriodPow_eq_zeroSumCount` proved the signed period-power sum identity
`∑_ψ η_ψ^r = q · #{ t : Fin r → S : ∑_i t i = 0 }`. The count on the right is, definitionally, the
campaign's in-tree `NegationClosedWalk.zeroSumCount S r` (the `r`-tuple zero-sum count that the entire
K1 / energy ladder is phrased in). This file states the identity in that canonical vocabulary, so the
signed period-power sum plugs directly into the `zeroSumCount`-based machinery:

>   `∑_ψ η_ψ^r = q · zeroSumCount S r`     (`signedPeriodPow_eq_q_mul_zeroSumCount`)

and, in particular, at general (incl. ODD) order `r` — the regime the additive-energy framework
(always `2r`-fold, sum-of-squares) cannot express. The FULL sum over all characters is always the
nonnegative real number `q·zeroSumCount S r`, also for odd `r` (audit PG-046): it is never
negative. The sign information lives only in the DC-subtracted, nonzero-character sum
`∑_{ψ≠0} η_ψ^r = q·zeroSumCount S r − |S|^r` (`nonzeroSignedPeriodPow_eq_zeroSumCount`): for odd
`r` its individual terms `η_ψ^r` are not squares and it can be negative (e.g. `S = {1}`, `r = 1`
gives `q·0 − 1 = −1`), whereas every `|·|`/energy packaging is `2r`-fold and non-negative.
This is the sense in which the SIGNED nonzero-character sum can carry information the moment
route's `|·|` discards (`DISPROOF_LOG`).

Honest scope: a definitional bridge (`zeroSumCount` unfolds to exactly the headline's filter-count), so
the signed identity now lives in the canonical vocabulary. NON-MOMENT, EXTEND of the just-landed
`signedPeriodPow_eq_zeroSumCount`. NOT a CORE bound — bounding `∑_{ψ≠0} η_ψ^r` (= `q·zeroSumCount − |S|^r`)
at `r ≈ log q` is the open BGK wall. `CORE  M(μ_n) ≤ C·√(n·log(q/n))  OPEN.`

Issues #444, #407.
-/
set_option linter.unusedSectionVars false


open scoped BigOperators

namespace ArkLib.ProximityGap.SignedPeriodPowerCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The signed period-power sum, in canonical `zeroSumCount` form.**
`∑_ψ (∑_{x∈S} ψ x)^r = q · zeroSumCount S r`. The count `zeroSumCount S r` (the in-tree
`r`-tuple zero-sum count of the K1 / energy ladder) is definitionally the headline's filter-count,
so the signed period-power sum plugs directly into the campaign's `zeroSumCount`-based machinery at
general — including ODD — order `r`, the regime the always-`2r` additive-energy framework cannot see. -/
theorem signedPeriodPow_eq_q_mul_zeroSumCount (S : Finset F) (r : ℕ) :
    (∑ ψ : AddChar F ℂ, (∑ x ∈ S, ψ x) ^ r)
      = (Fintype.card F : ℂ)
          * (ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount S r : ℂ) := by
  rw [signedPeriodPow_eq_zeroSumCount S r]
  rfl

/-- **The nonzero-character (prize) form in canonical `zeroSumCount` vocabulary.**
`∑_{ψ≠0} η_ψ^r = q · zeroSumCount S r − |S|^r`. This is the object `∑_{b≠0} η_b^r` the
thinness-discriminator search located (`DISPROOF_LOG`): for odd `r` it is `q·zeroSumCount` of an
odd-length walk minus the diagonal — genuinely signed (not a sum of squares), unlike every
`2r`-fold energy/moment packaging. Bounding it at `r ≈ log q` is the open BGK wall. -/
theorem nonzeroSignedPeriodPow_eq_zeroSumCount (S : Finset F) (r : ℕ) :
    (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r)
      = (Fintype.card F : ℂ)
          * (ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount S r : ℂ)
        - (S.card : ℂ) ^ r := by
  rw [nonzeroSignedPeriodPow_eq S r]
  rfl

end ArkLib.ProximityGap.SignedPeriodPowerCount

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SignedPeriodPowerCount.signedPeriodPow_eq_q_mul_zeroSumCount
#print axioms ArkLib.ProximityGap.SignedPeriodPowerCount.nonzeroSignedPeriodPow_eq_zeroSumCount
