/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteMomentAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteParsevalLower

/-!
# The CONCRETE two-sided bracket on the worst period `M(μ_n)` (#444)

`_ExpanderMixingBound.two_sided_bound` states the two-sided bracket
`√(n(p−n)/(p−1)) ≤ M ≤ B` but over an ABSTRACT `M` with both ends as carried hypotheses. This file
bundles the two CONCRETE ends — both discharged on the real periods `η_b = ∑_{y∈G} ψ(by)` in the two
companion files — into one named statement over `worstPeriod ψ G = max_{b≠0}‖η_b‖`:

> `worstPeriod_two_sided_bracket` :
>   `√(n(q−n)/(q−1)) ≤ M(μ_n)  ∧  M(μ_n) ≤ √e·√(2rn)`,
>   given (lower) only `1 < q` [PROVEN, unconditional], and (upper) the named no-wraparound residual
>   `hNoWrap : E_r = E0`, char-0 envelope `E0 ≤ (2rn)^r`, and depth `q ≤ exp r`.

* LOWER (`worstPeriod_ge_sqrt_parseval`, `ConcreteParsevalLower`): PROVEN, Parseval-only, `≈ √n`.
* UPPER (`concrete_prize_floor_of_noWraparound`, `ConcreteMomentAssembly`): the moment pillar is now a
  theorem; the only open input is `hNoWrap` (the BGK/Paley wraparound onset = the prize).

The bracket is the exact spectral picture for `Cay(F_q, μ_n)` over the real periods. The **gap between
the two ends** — `√(n(q−n)/(q−1)) ≈ √n` vs `√e·√(2rn) ≈ √(2en·log q)` at `r ≈ log q` — is PRECISELY
the prize: closing the upper side to the lower `√n` scale up to the `√(log q)` factor.

## Honesty (scope)

Consolidation only. The LOWER side is the unconditional √n floor (Parseval). The UPPER side still rests
on the named residual `hNoWrap` (= `OnsetExceedsSaddle` / `NonprincipalWickBound` at `r ≈ log p`, the
BGK wall). CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN; this packages the two proven-modulo-the-residual
ends into one in-tree bracket over the concrete worst period.
-/

set_option linter.style.longLine false


open Finset
open ProximityGap.Frontier.ConcreteMomentAssembly
open ProximityGap.Frontier.ConcreteParsevalLower
open ArkLib.ProximityGap.I031DilationOrbitReduction

namespace ProximityGap.Frontier.ConcreteTwoSidedBracket

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **★ The concrete two-sided bracket on the worst period.** For the real Gauss periods
`η_b = ∑_{y∈G} ψ(by)`, with `M(μ_n) = max_{b≠0}‖η_b‖`:

* LOWER (PROVEN, unconditional / Parseval): `√(n(q−n)/(q−1)) ≤ M(μ_n)`.
* UPPER (under the named no-wraparound residual + proven char-0 envelope + depth): `M(μ_n) ≤ √e·√(2rn)`.

The gap `√n` vs `√(2en·log q)` (at `r ≈ log q`) is the prize. Both ends are discharged on the concrete
`worstPeriod` in the companion files; this bundles them. -/
theorem worstPeriod_two_sided_bracket {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {r : ℕ} (hr : 0 < r) (hne : (nonzeroFreqs F).Nonempty)
    (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    {E0 : ℝ}
    (hNoWrap : (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ) = E0)
    (hChar0 : E0 ≤ (2 * r * (G.card : ℝ)) ^ r)
    (hdepth : (Fintype.card F : ℝ) ≤ Real.exp r) :
    Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1))
        ≤ worstPeriod ψ G hne
      ∧ worstPeriod ψ G hne ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * (G.card : ℝ)) :=
  ⟨worstPeriod_ge_sqrt_parseval hψ G hne hq1,
   concrete_prize_floor_of_noWraparound hψ G hr hne hNoWrap hChar0 hdepth⟩

end ProximityGap.Frontier.ConcreteTwoSidedBracket

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteTwoSidedBracket.worstPeriod_two_sided_bracket
