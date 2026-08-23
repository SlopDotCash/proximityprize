/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CoshMGFIdentity

/-!
# The cosh-MGF saddle consumer — the single open inequality ⟹ the sup-norm floor (#407 / #444)

`CoshMGFIdentity` lands the root-free MGF bound `cosh(‖η_{b₀}‖·y) ≤ ∑_r (q·E_r/(2r)!) y^{2r}` but
explicitly leaves "optimising the free parameter `y`" as the open §5.0 step. This file lands that
consumer — #444 c.12:13's steps 3–4, funnelling the whole cosh-MGF route into the **single open
inequality** `Φ_p(y) ≤ exp(n y²/2)`:

> if the char-`p` energy MGF satisfies `∑_r (q·E_r/(2r)!) y^{2r} ≤ q·exp(n y²/2)` (the single open
> inequality), then **`‖η_{b₀}‖ ≤ (log(2q) + n y²/2)/y`** for every `y > 0`.

At the saddle `y* = √(2 log q / n)` this is `‖η_{b₀}‖ ≤ √(2 n log q)·(1+o(1))` — the prize floor
`C·√(n log(q/n))` (c.12:13's `C ≈ 1.03`). The reduction is root-free (no `arccosh`): it uses only the
elementary `exp t ≤ 2·cosh t`.

**Honest scope.** This is the cosh-MGF *consumer* (PROVEN): it discharges the prize sup-norm floor
**conditionally on the single open inequality** `Φ_p(y*) ≤ exp(n y*²/2)` (the char-`p` `A_r ≤ Wick`
saddle at depth `r ≈ log q`, the recognised open BGK core). It does NOT prove that inequality — that is
the named open core (`_WickMonotonicityReduction`, `_BGKSOTAInsufficiency`, #444 c.12:13). Axiom-clean.
Issues #407, #444.
-/

open scoped BigOperators

namespace ProximityGap.Frontier.CoshMGFSaddle

open Finset
open ProximityGap.Frontier.CoshMGFIdentity
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Elementary: `exp t ≤ 2·cosh t` (since `2·cosh t = exp t + exp(−t)` and `exp(−t) ≥ 0`). -/
theorem exp_le_two_mul_cosh (t : ℝ) : Real.exp t ≤ 2 * Real.cosh t := by
  rw [Real.cosh_eq]
  have h : (0 : ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
  have : 2 * ((Real.exp t + Real.exp (-t)) / 2) = Real.exp t + Real.exp (-t) := by ring
  rw [this]; linarith

/-- **The cosh-MGF saddle consumer (the single open inequality ⟹ the sup-norm floor).** For any
`y > 0` and any frequency `b₀`, if the char-`p` even-moment MGF is bounded by the Gaussian
`q·exp(n y²/2)` (the single open inequality of #444 c.12:13), then the Gauss period satisfies
`‖η_{b₀}‖ ≤ (log(2q) + n y²/2)/y`. Root-free; the only input beyond the in-tree MGF identity is the
open inequality. -/
theorem period_le_of_mgfBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (b₀ : F)
    (hMGF : (∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
              ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) :
    ‖eta ψ G b₀‖ ≤ (Real.log (2 * (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2))) / y := by
  set B : ℝ := (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2) with hB
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have := Fintype.card_pos (α := F); exact_mod_cast this
  have hBpos : 0 < B := by rw [hB]; positivity
  -- cosh(‖η‖y) ≤ MGF ≤ B
  have hcosh : Real.cosh (‖eta ψ G b₀‖ * y) ≤ B :=
    (cosh_period_le_evenMoment_tsum hψ G y b₀).trans hMGF
  -- exp(‖η‖y) ≤ 2·cosh(‖η‖y) ≤ 2B
  have hexp : Real.exp (‖eta ψ G b₀‖ * y) ≤ 2 * B :=
    (exp_le_two_mul_cosh _).trans (by linarith [hcosh])
  -- ‖η‖y ≤ log(2B)
  have hlog : ‖eta ψ G b₀‖ * y ≤ Real.log (2 * B) := by
    have h2B : (0 : ℝ) < 2 * B := by positivity
    calc ‖eta ψ G b₀‖ * y = Real.log (Real.exp (‖eta ψ G b₀‖ * y)) := (Real.log_exp _).symm
      _ ≤ Real.log (2 * B) := Real.log_le_log (Real.exp_pos _) hexp
  -- divide by y > 0
  rw [le_div_iff₀ hy]
  calc ‖eta ψ G b₀‖ * y ≤ Real.log (2 * B) := hlog
    _ = Real.log (2 * (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) := by
        rw [hB]; ring_nf

/-- **Saddle evaluation: `exp(n·y*²/2) = q` at `y* = √(2 log q / n)`.** The arithmetic fact pinning the
saddle: with `y*² = 2 log q / n` (and `n > 0`), `n·y*²/2 = log q`, so `exp(n y*²/2) = q`. Thus the
consumer's bound becomes `log(2q²)/y*`, i.e. `‖η_{b₀}‖ ≤ (log 2 + 2 log q)/y*` — the `√(2 n log q)`
floor up to the constant `C`. -/
theorem exp_saddle_eq_card {G : Finset F} (hn : 0 < (G.card : ℝ))
    {y : ℝ} (hy : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ)) :
    Real.exp ((G.card : ℝ) * y ^ 2 / 2) = (Fintype.card F : ℝ) := by
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have := Fintype.card_pos (α := F); exact_mod_cast this
  rw [hy]
  have hne : (G.card : ℝ) ≠ 0 := ne_of_gt hn
  have : (G.card : ℝ) * (2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ)) / 2
      = Real.log (Fintype.card F : ℝ) := by
    field_simp
  rw [this, Real.exp_log hqpos]

end ProximityGap.Frontier.CoshMGFSaddle

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CoshMGFSaddle.exp_le_two_mul_cosh
#print axioms ProximityGap.Frontier.CoshMGFSaddle.period_le_of_mgfBound
#print axioms ProximityGap.Frontier.CoshMGFSaddle.exp_saddle_eq_card
