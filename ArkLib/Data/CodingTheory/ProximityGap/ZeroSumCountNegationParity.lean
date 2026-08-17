/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SignedZeroSumCountEven
import ArkLib.Data.CodingTheory.ProximityGap.SignedPeriodZeroSumBridge

/-!
# The SIGNED prize object, with the zero-sum-count parity made explicit (#444, #407)

`SignedZeroSumCountEven.two_dvd_zeroSumCount` proved that on a negation-closed `0`-free `G` (char
`≠ 2`) the zero-sum count `zeroSumCount G m` is EVEN at every order `m ≥ 1` (the global negation
`c ↦ −c` is a fixed-point-free involution on the zero-sum `m`-tuples). That file states the
*consequence* for the SIGNED prize object only in prose:

>   `∑_{ψ≠0} η_ψ^r = q · zeroSumCount S r − |S|^r`  has `q·zeroSumCount` pinned to an even multiple.

This file makes that consequence an actual **theorem**: combining `two_dvd_zeroSumCount` with the
signed period-power identity `SignedPeriodZeroSumBridge.nonzeroSignedPeriodPow_eq_zeroSumCount`, the
located thinness-essential prize object is

>   `∑_{ψ≠0} η_ψ^r = q · (2·m) − |S|^r`   for some `m : ℕ`,

at every order `r ≥ 1` — including ODD `r`, the regime the always-`2r` energy framework cannot
express. So the signed sum's deviation from `−|S|^r` is exactly `q` times an even integer: a clean
parity constraint on the signed object itself, in the `AddChar F ℂ` vocabulary the prize sum lives
in (the upstream file's statement is over the `ℕ`-valued count, not the `ℂ`-valued character sum).

Honest scope: NON-MOMENT (parity on the additive-tuple count; no `|·|`), an EXTEND that sits directly
on the just-landed `two_dvd_zeroSumCount` + the signed-period-power identity, lifting the `ℕ`-parity
to the `ℂ`-valued signed prize object. NOT a CORE bound — bounding `∑_{ψ≠0} η_ψ^r` *quantitatively* at
`r ≈ log q` (the deep signed cancellation `q·zeroSumCount − n^r` being *small*) is the open BGK wall.
`CORE  M(μ_n) ≤ C·√(n·log(q/n))  OPEN.`

Issues #444, #407.
-/

set_option linter.unusedDecidableInType false


open scoped BigOperators

namespace ArkLib.ProximityGap.NegationClosedWalk

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The signed prize object's deviation from `−|S|^r` is `q` times an EVEN integer.**
The located thinness-essential prize object is `∑_{ψ≠0} η_ψ^r = q·zeroSumCount S r − |S|^r`
(`nonzeroSignedPeriodPow_eq_zeroSumCount`). Since `zeroSumCount S r` is even on a `0`-free
negation-closed `S` in char `≠ 2` (`two_dvd_zeroSumCount`), there is `m` with the signed sum equal to
`q·(2·m) − |S|^r`. This lifts the upstream `ℕ`-valued parity to the `ℂ`-valued character sum the prize
is phrased in, at every order `r ≥ 1` (incl. odd). A parity constraint on the signed object — NOT a
quantitative cancellation bound; the deep signed cancellation at `r ≈ log q` is the open BGK wall.
-/
theorem nonzeroSignedPeriodPow_eq_q_mul_two_mul_sub
    (S : Finset F) (r : ℕ) (hr : r ≠ 0)
    (h2 : (2 : F) ≠ 0) (hneg : ∀ g ∈ S, -g ∈ S) (h0 : (0 : F) ∉ S) :
    ∃ m : ℕ,
      (∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r)
        = (Fintype.card F : ℂ) * (2 * m : ℕ) - (S.card : ℂ) ^ r := by
  obtain ⟨m, hm⟩ := two_dvd_zeroSumCount hr h2 S hneg h0
  refine ⟨m, ?_⟩
  rw [ArkLib.ProximityGap.SignedPeriodPowerCount.nonzeroSignedPeriodPow_eq_zeroSumCount S r, hm]

end ArkLib.ProximityGap.NegationClosedWalk

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.NegationClosedWalk.nonzeroSignedPeriodPow_eq_q_mul_two_mul_sub
