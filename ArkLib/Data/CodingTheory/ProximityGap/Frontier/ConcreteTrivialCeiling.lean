/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteParsevalLower
import ArkLib.Data.CodingTheory.ProximityGap.IncidenceDeviationCharSum

/-!
# The CONCRETE trivial ceiling `M(μ_n) ≤ n` and the citable two-sided prize bracket (#444)

The prize CORE asks for `M(μ_n) = max_{b≠0} ‖η_b‖ ≤ C·√(n·log(p/n))`. Two unconditional bounds
bracket this worst period over the REAL periods `η_b = ∑_{y∈G} ψ(b·y)`:

* the **Parseval floor** `√(n(q−n)/(q−1)) ≤ M(μ_n)` (`≈ √n`), already discharged in
  `ConcreteParsevalLower.worstPeriod_ge_sqrt_parseval`;
* the **trivial ceiling** `M(μ_n) ≤ n`, supplied HERE.

The trivial ceiling is the elementary triangle-inequality bound on the period itself: each summand
`ψ(b·y)` is a root of unity (`‖ψ(b·y)‖ = 1`, `norm_addChar_apply`), so
`‖η_b‖ = ‖∑_{y∈G} ψ(b·y)‖ ≤ ∑_{y∈G} ‖ψ(b·y)‖ = |G|` for EVERY `b`, hence the sup over nonzero `b`
is also `≤ |G| = n`. This is the named "M ≤ n trivial ceiling" rung of the Lane-2 reduction capstone
(Shaw-value essay, #444 2026-06-18).

> `norm_eta_le_card`        : `‖η_b‖ ≤ |G|` for every `b` (triangle inequality + unit summands),
> `worstPeriod_le_card`     : `M(μ_n) ≤ |G|` (the trivial ceiling),
> `worstPeriod_bracket`     : `√(n(q−n)/(q−1)) ≤ M(μ_n) ≤ |G|` (the citable two-sided bracket).

## Honesty (the prize is the GAP, untouched)

The ceiling `M ≤ n` is the trivial triangle-inequality bound (`√q`-completion already beats it on
torsion subgroups, `SubgroupGaussSumWorstCase.norm_eta_torsion_le`); CORE asks for `M ≤ C·√(n·log(p/n))`,
which is exponentially below `n` in the thin prize regime (`n = 2^a`, `q = n^β`). The GAP between the
proven floor `√n` and the proven ceiling `n` is `√n .. n`; the prize lives at `√(n·log p)` strictly
inside that gap. This file supplies the SAFE, citable upper rung of the bracket (Lane 2), pure
consolidation over the real `eta`. CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN — no cancellation,
moment, completion, or capacity claim is made.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.IncidenceDeviationCharSum
open ProximityGap.Frontier.ConcreteMomentAssembly
open ProximityGap.Frontier.ConcreteParsevalLower

namespace ProximityGap.Frontier.ConcreteTrivialCeiling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The pointwise trivial ceiling.** `‖η_b‖ ≤ |G|` for EVERY frequency `b`. The period
`η_b = ∑_{y∈G} ψ(b·y)` is a sum of `|G|` unit-modulus summands (`‖ψ(b·y)‖ = 1`), so the triangle
inequality gives `‖η_b‖ ≤ ∑_{y∈G} ‖ψ(b·y)‖ = ∑_{y∈G} 1 = |G|`. -/
theorem norm_eta_le_card (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    ‖eta ψ G b‖ ≤ (G.card : ℝ) := by
  calc ‖eta ψ G b‖ = ‖∑ y ∈ G, ψ (b * y)‖ := by rw [eta]
    _ ≤ ∑ y ∈ G, ‖ψ (b * y)‖ := norm_sum_le _ _
    _ = ∑ y ∈ G, (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro y _
        exact norm_addChar_apply ψ (b * y)
    _ = (G.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The trivial ceiling `M(μ_n) ≤ n`.** The worst nonzero period is a sup' of the pointwise norms
`‖η_b‖`, each `≤ |G|` by `norm_eta_le_card`, so the sup' is `≤ |G| = n`. The named upper rung of the
Lane-2 reduction capstone bracket. -/
theorem worstPeriod_le_card (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) :
    worstPeriod ψ G hne ≤ (G.card : ℝ) := by
  unfold worstPeriod
  refine Finset.sup'_le hne _ ?_
  intro b _
  exact norm_eta_le_card ψ G b

/-- **The citable two-sided prize bracket.** `√(n(q−n)/(q−1)) ≤ M(μ_n) ≤ |G|`. The unconditional
Parseval floor (`ConcreteParsevalLower.worstPeriod_ge_sqrt_parseval`, `≈ √n`) and the trivial ceiling
(`worstPeriod_le_card`, `= n`) bracket the worst period. CORE `M ≤ C·√(n·log(p/n))` lives strictly
INSIDE this `√n .. n` gap — the prize IS the gap. -/
theorem worstPeriod_bracket {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1))
        ≤ worstPeriod ψ G hne
      ∧ worstPeriod ψ G hne ≤ (G.card : ℝ) :=
  ⟨worstPeriod_ge_sqrt_parseval hψ G hne hq1, worstPeriod_le_card ψ G hne⟩

/-- **Concrete SHARP two-sided corridor in the prize regime.** Combining the new quadratic-regime
sharp floor (`worstPeriod_ge_sqrt_card_pred_of_sq_le`) with the trivial ceiling, under `n² ≤ q`
(`q = n^β, β ≥ 2`) the real worst period is sandwiched
`√(n−1) ≤ M(μ_n) ≤ n` — the tightest unconditional corridor available, with the floor at its true
`√n` value rather than a constant fraction. The prize bound `M ≤ C·√(n·log(q/n))` lives strictly
inside this corridor; tightening the upper endpoint from `n` to `√(n·log(q/n))` is exactly the
open prize. -/
theorem worstPeriod_sharp_bracket {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hG1 : (1 : ℝ) < (G.card : ℝ))
    (hsq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) - 1) ≤ worstPeriod ψ G hne
      ∧ worstPeriod ψ G hne ≤ (G.card : ℝ) :=
  ⟨worstPeriod_ge_sqrt_card_pred_of_sq_le hψ G hne hq1 hG1 hsq, worstPeriod_le_card ψ G hne⟩

/-- **Concrete corridor width is `√n` (up to `√(n/(n−1)) → 1`).** The ratio of the proven endpoints
of the sharp corridor `[√(n−1), n]` has the closed form `n / √(n−1) = √n · √(n/(n−1))`. The factor
`√(n/(n−1)) → 1`, so the unconditional proven gap on the real worst period is exactly `√n`-wide in
the prize regime — the concrete companion of the abstract `ShawValueCapstone.bracket_width_eq_sqrt`.
Closing this `√n` gap to `O(√(log(q/n)))` is the open prize. (Probe: `n/√(n−1)/√n` =
1.155,1.033,1.008,1.002 at `n=4,16,64,256`.) -/
theorem sharp_bracket_width_eq {n : ℝ} (hn1 : (1 : ℝ) < n) :
    n / Real.sqrt (n - 1) = Real.sqrt n * Real.sqrt (n / (n - 1)) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hnm1 : (0 : ℝ) < n - 1 := by linarith
  -- √n · √(n/(n−1)) = √(n · n/(n−1)) = √(n²/(n−1)) = √(n²)/√(n−1) = n/√(n−1)
  rw [← Real.sqrt_mul (le_of_lt hn0)]
  have hmul : n * (n / (n - 1)) = n ^ 2 / (n - 1) := by ring
  rw [hmul, Real.sqrt_div (by positivity) (n - 1), Real.sqrt_sq (le_of_lt hn0)]

end ProximityGap.Frontier.ConcreteTrivialCeiling

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteTrivialCeiling.worstPeriod_sharp_bracket
#print axioms ProximityGap.Frontier.ConcreteTrivialCeiling.sharp_bracket_width_eq
