/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicWeightRefutation
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicWeightExplicit

/-!
# The named kernel `DivWeightLe` is refuted in the MONIC regime too (#302, #138)

`AlphaWeight.DivWeightLe` (the carved A.4 clearing-divisibility-with-weight kernel,
`AlphaWeight.lean`) was already refuted for non-monic `H` with non-unit leading coefficient
(`AlphaWeightClearedObstruction.not_DivWeightLe`, via the base case `t = 0`).  The monic case
escapes that refutation — `lc = 1` divides everything — and the base case is provable there, so
the named kernel survived at monic `H` and the successor cases were the advertised open target
for the #302 beyond-window chain.

This file closes that escape hatch: **the full named kernel `DivWeightLe` is false at monic `H`
as well**, under the current two-field `ClaimA2.Hypotheses`.  The valid separable monic witness
of `P1MonicWeightRefutation` (`H = Y² − 2`, `R = Y² − 2 + u·s` over `ZMod 3`) kills the `t = 1`
instance: for monic `H` the `W𝒪`-power is `1`, so the `t = 1` clause collapses to exactly the
shape `weight_refuted` negates.

Consequences recorded here, both axiom-clean:

* `not_divWeightLe_monic_witness` — `¬ DivWeightLe myH 0 myR myHyp hH 2`: the named kernel
  itself, not just a pointwise shape, fails on a valid monic instance.
* `not_henselQuotient_weight_le` — through `succDivWeightLe_iff_henselQuotient_weight`, the
  isolated explicit core (`∀ t, Λ_𝒪(henselQuotient t) ≤ 1`) is likewise false for the witness.

Together with the non-monic refutation, the named kernel `DivWeightLe` is now refuted in BOTH
regimes from `ClaimA2.Hypotheses` alone.  The actionable content for #302: attacking
`DivWeightLe_succ` directly from the current hypotheses cannot succeed; the kernel needs a
strengthened hypothesis pack first (a `deg R` bound relative to `D` — the exact boundary is
pinned by `weight_refuted` vs `P1MonicWeightHolds.weight_holds`).
-/

noncomputable section
open scoped Polynomial.Bivariate
open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.WeightWitness

/-- **The named kernel `DivWeightLe` is false at monic `H`** under the current two-field
`ClaimA2.Hypotheses`: the valid separable monic witness kills its `t = 1` instance (where the
monic `W𝒪`-power is `1` and the clause collapses to the `weight_refuted` shape).  Combined with
`AlphaWeightClearedObstruction.not_DivWeightLe` (non-monic, via `t = 0`), the carved kernel is
refuted in both regimes; a `deg R`-bounded hypothesis strengthening is required before any
successor-step attack can be a theorem. -/
theorem not_divWeightLe_monic_witness (hH : 0 < myH.natDegree) :
    ¬ AlphaWeight.DivWeightLe myH 0 myR myHyp hH 2 := by
  intro hdiv
  obtain ⟨a, hEq, hwt⟩ := hdiv 1
  refine weight_refuted hH ⟨a, ?_, hwt⟩
  have hW : W𝒪 myH = 1 := by
    rw [W𝒪, myH_leadingCoeff, map_one, map_one]
  rw [hEq, hW, one_pow, mul_one]
  norm_num

/-- **The isolated explicit core is false for the witness**: the all-orders weight bound on the
explicit quotient `henselQuotient` (the form `succDivWeightLe_iff_henselQuotient_weight` isolates
as the entire remaining monic content of #138) fails on the valid separable instance with
unbounded lift-direction degree. -/
theorem not_henselQuotient_weight_le (hH : 0 < myH.natDegree) :
    ¬ ∀ t : ℕ,
        weight_Λ_over_𝒪 hH (henselQuotient myH 0 myR myHyp myH_leadingCoeff t) 2
          ≤ WithBot.some 1 := by
  intro hq
  have hall := (succDivWeightLe_iff_henselQuotient_weight myH 0 myR myHyp
    myH_leadingCoeff 2 hH).mpr hq
  obtain ⟨a, hEq, hwt⟩ := hall 0
  refine weight_refuted hH ⟨a, ?_, hwt⟩
  rw [hEq]
  norm_num

end BCIKS20.HenselNumerator.WeightWitness

#print axioms BCIKS20.HenselNumerator.WeightWitness.not_divWeightLe_monic_witness
#print axioms BCIKS20.HenselNumerator.WeightWitness.not_henselQuotient_weight_le
