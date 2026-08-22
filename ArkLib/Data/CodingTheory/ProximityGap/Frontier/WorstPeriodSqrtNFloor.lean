/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteParsevalLower

/-!
# The clean `Ω(√n)` floor on the worst period in the thin regime (#444)

`ConcreteParsevalLower.worstPeriod_ge_sqrt_parseval` gives the unconditional reverse-EML floor
`√(n(q−n)/(q−1)) ≤ M(μ_n)`. In the thin prize regime `q ≥ 2n` (`β > 1`, automatic at the prize
`q = n^β`) this simplifies to the clean denominator-free floor:

> `worstPeriod_ge_sqrt_half_n` :  `√(n/2) ≤ M(μ_n)`   (when `q ≥ 2n`),

i.e. the worst nonzero Gauss period is `Ω(√n)` unconditionally — there is NO sub-`√n` cancellation in
the worst case (the Johnson/Plancherel floor is essentially attained from below). Mechanism: for
`q ≥ 2n` we have `q − n ≥ q/2` and `q − 1 < q`, so `n(q−n)/(q−1) ≥ n·(q/2)/q = n/2`; monotonicity of
`√` then lifts `worstPeriod_ge_sqrt_parseval`.

## Honesty (scope)

This is the LOWER bound (`Ω(√n)`, unconditional, Parseval-only). It is the floor side of the prize
bracket — the prize is the UPPER bound `M(μ_n) ≤ C·√(n·log(p/n))`, and the gap `√n` vs `√(n·log p)`
is exactly what remains open. CORE stays OPEN; this is a clean closed-form restatement of the proven
floor.
-/

set_option linter.style.longLine false


open Finset
open ProximityGap.Frontier.ConcreteMomentAssembly
open ProximityGap.Frontier.ConcreteParsevalLower
open ArkLib.ProximityGap.I031DilationOrbitReduction

namespace ProximityGap.Frontier.WorstPeriodSqrtNFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The Parseval floor is `≥ n/2` in the thin regime.** For `q ≥ 2n` (and `n ≥ 1`),
`n/2 ≤ n(q−n)/(q−1)`. Elementary: `q−n ≥ q/2 ≥ (q−1)/2`, so `n(q−n) ≥ n(q−1)/2`. -/
theorem parseval_floor_ge_half_n {n q : ℝ} (hn : 1 ≤ n) (hq2n : 2 * n ≤ q) :
    n / 2 ≤ n * (q - n) / (q - 1) := by
  have hqpos : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) < q := by linarith
  have hqm1 : (0 : ℝ) < q - 1 := by linarith
  rw [le_div_iff₀ hqm1]
  -- n/2·(q−1) ≤ n(q−n)  ⟺  (q−1)/2 ≤ q−n  ⟺  q−1 ≤ 2q−2n  ⟺  2n−1 ≤ q  (true since q ≥ 2n)
  have hkey : (q - 1) / 2 ≤ q - n := by linarith
  nlinarith [hkey, hn, hqm1]

/-- **★ The clean `√(n/2)` floor on the worst period (thin regime).** When `q ≥ 2n`, the worst nonzero
Gauss period obeys `√(n/2) ≤ M(μ_n)` — unconditional, `Ω(√n)`. The denominator-free form of
`worstPeriod_ge_sqrt_parseval` in the prize regime: no sub-`√n` cancellation in the worst case. -/
theorem worstPeriod_ge_sqrt_half_n {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty)
    (hn1 : 1 ≤ (G.card : ℝ))
    (hq2n : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) / 2) ≤ worstPeriod ψ G hne := by
  have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hlow := worstPeriod_ge_sqrt_parseval hψ G hne hq1
  have hfloor : (G.card : ℝ) / 2
      ≤ (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) :=
    parseval_floor_ge_half_n hn1 hq2n
  exact le_trans (Real.sqrt_le_sqrt hfloor) hlow

end ProximityGap.Frontier.WorstPeriodSqrtNFloor

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.WorstPeriodSqrtNFloor.parseval_floor_ge_half_n
#print axioms ProximityGap.Frontier.WorstPeriodSqrtNFloor.worstPeriod_ge_sqrt_half_n
