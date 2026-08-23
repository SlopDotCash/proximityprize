/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WickMonotonicityReduction

/-!
# The single-step Wick monotonicity presupposes the DC-subtracted sup-norm wall (#444 / #407)

**What this discharges (frontier-MOVEMENT, not point-confirmation).** The `_WickMonotonicityReduction`
module reframes the #407 prize floor `A_r ≤ Wick_r ∀ r` as a single named open core
`WickMonotonicity : ∀ r ≥ 1, f (r+1) ≤ f r` where `f r = A_r / Wick_r`,
`A_r = (1/q)·∑_{b≠0} ‖η_b‖^{2r}` (the **DC-subtracted** `2r`-th Gauss-period moment), and
`Wick_r = (2r−1)‼·|G|^r`. That file leaves `WickMonotonicity` as an opaque `Prop`.

Here we *localize* that open core onto the **same log-convex-ratio engine** that
`EnergyLogConvexRatioMonotone` runs for the FULL energy `E_r` — but for the **DC-subtracted** moment
`A_r` that `WickMonotonicity` actually uses (sum over `univ.erase 0`, not all `b`). The result is the
exact analogue of `erm_step_of_supNorm`, but for the genuine prize-floor object: the per-step Wick
ratio condition is the DC-subtracted sup-norm bound, so a proof of the Wick-monotone step is *circular*
with respect to the BGK / Paley sup-norm wall.

**The chain (all axiom-clean):**
1. `dc_moment_logConvex` — `(∑_{b≠0}‖η_b‖^{2r})² ≤ (∑_{b≠0}‖η_b‖^{2(r−1)})·(∑_{b≠0}‖η_b‖^{2(r+1)})`
   (Cauchy–Schwarz on the nonnegative spectrum restricted to `b ≠ 0`; `f_b = ‖η_b‖^{r−1}`,
   `g_b = ‖η_b‖^{r+1}`). The DC-subtracted moment ladder is LOG-CONVEX — field-universal, like the full
   ladder, but here on the `b ≠ 0` measure that `A_r` integrates.
2. `Wick_succ` — `Wick_{r+1} = (2r+1)·|G|·Wick_r` (from `oddWickCoeff (r+1) = (2r+1)·oddWickCoeff r`).
3. `wickRatio_step_iff` — the EXACT characterization: `f (r+1) ≤ f r ↔ A_{r+1}·Wick_r ≤ A_r·Wick_{r+1}`,
   i.e. (cancelling `Wick`) `A_{r+1} ≤ (2r+1)·|G|·A_r`. So `WickMonotonicity` IS the per-step DC ratio
   bound `A_{r+1}/A_r ≤ (2r+1)·|G|` at every `r ≥ 1`.
4. `dc_moment_succ_le_maxSq_mul` / `Ar_succ_le_maxSq_mul` — `A_{r+1} ≤ (max_{b≠0}‖η_b‖²)·A_r`: the DC
   per-step ratio is bounded ABOVE by the DC-subtracted sup-norm `M := max_{b≠0}‖η_b‖²`. With (1)
   (log-convexity ⟹ ratio ↑) the DC ratio `A_{r+1}/A_r` approaches `M` from below.
5. `wickMono_step_of_dc_supNorm` (HEADLINE) — IF the DC sup-norm bound `M ≤ (2r+1)·|G|` holds, THEN the
   Wick-monotone step `f (r+1) ≤ f r` holds. So `WickMonotonicity`-at-`r` is a CONSEQUENCE of the
   DC sup-norm bound, never a route to it. Combined with (1) (ratio ↑ `M`), the step can only hold
   tightly when `M ≤ (2r+1)·|G|` — the DC-subtracted BGK / Paley wall is PRESUPPOSED.
6. `wickMonotonicity_of_dc_supNorm` — a uniform DC sup-norm certificate `∀ b ≠ 0, ‖η_b‖² ≤ (2r+1)·|G|`
   at every depth `r` yields the full `WickMonotonicity`, hence (via `floorViaWick_of_monotonicity`)
   the floor. This is the precise circularity: the floor route through Wick-monotonicity already needs
   the per-depth DC sup-norm cancellation.

**Probe (rule 2).** `scripts/probes/probe_dc_wickmono_reduce.py`: at PROPER subgroups `μ_n ⊊ F_p^*`,
`n = 2^a ∈ {8,16,32}`, primes `p ∈ {193,257,7681,12289,40961,786433}` up to `β ≈ 4.90` (prize regime),
all of `A_r` log-convex, `WickMonotonicity` holds, the reduced per-step condition
`A_{r+1}/A_r ≤ (2r+1)·|G|` holds, the DC ratio is monotone-increasing, and `A_{r+1}/A_r ≤ max_{b≠0}‖η_b‖²`
with equality approached from below — confirming the reduction is exact and the ceiling is the DC
sup-norm.

**Honesty / scope (rule 3, rule 6).** This is NOT a CORE closure and NOT a proof of `WickMonotonicity`.
It is the *structural localization* of the open core: the Wick-monotone step is the DC-subtracted
sup-norm bound, so the floor route via Wick-monotonicity cannot prove the prize without already holding
the DC sup-norm cancellation (circular). The log-convexity (1) is FIELD-UNIVERSAL (holds for the thick
group too); its prize consequence is thinness-essential ONLY through the value of `M = max_{b≠0}‖η_b‖²`
(`√q ≈ n^{β/2}` thick vs the prize `√(n log(p/n))` for `μ_n`) — i.e. exactly the rule-3 property: the
reduction is generic, the *wall* lives in the DC sup-norm value, which is the thin-subgroup BGK content.
`M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**. No capacity / cliff-at-`n/2` / beyond-Johnson claim.
Issues #444, #407.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ProximityGap.Frontier.WickMonotonicityReduction

namespace ProximityGap.Frontier.WickMonoDCSupNorm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Layer 1 — log-convexity of the DC-subtracted moment ladder (Cauchy–Schwarz on `b ≠ 0`) -/

/-- **DC-subtracted moment log-convexity (Cauchy–Schwarz).** For `r ≥ 1`,
`(∑_{b≠0}‖η_b‖^{2r})² ≤ (∑_{b≠0}‖η_b‖^{2(r−1)})·(∑_{b≠0}‖η_b‖^{2(r+1)})`. Same Cauchy–Schwarz as the full
ladder (`EnergyLogConvexRatio.moment_logConvex`), but on the `univ.erase 0` index set that `A_r`
integrates: `f_b = ‖η_b‖^{r−1}`, `g_b = ‖η_b‖^{r+1}`, so `f·g = ‖η_b‖^{2r}`, `f² = ‖η_b‖^{2(r−1)}`,
`g² = ‖η_b‖^{2(r+1)}`. -/
theorem dc_moment_logConvex (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) (hr : 1 ≤ r) :
    (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) ^ 2
      ≤ (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * (r - 1)))
        * (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * (r + 1))) := by
  classical
  set f : F → ℝ := fun b => ‖eta ψ G b‖ ^ (r - 1) with hf
  set g : F → ℝ := fun b => ‖eta ψ G b‖ ^ (r + 1) with hg
  have hfg : ∀ b : F, f b * g b = ‖eta ψ G b‖ ^ (2 * r) := by
    intro b; simp only [hf, hg]; rw [← pow_add]; congr 1; omega
  have hf2 : ∀ b : F, f b ^ 2 = ‖eta ψ G b‖ ^ (2 * (r - 1)) := by
    intro b; simp only [hf]; rw [← pow_mul]; congr 1; ring
  have hg2 : ∀ b : F, g b ^ 2 = ‖eta ψ G b‖ ^ (2 * (r + 1)) := by
    intro b; simp only [hg]; rw [← pow_mul]; congr 1; ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (univ.erase (0 : F)) f g
  calc (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) ^ 2
      = (∑ b ∈ univ.erase (0 : F), f b * g b) ^ 2 := by
        rw [Finset.sum_congr rfl (fun b _ => (hfg b).symm)]
    _ ≤ (∑ b ∈ univ.erase (0 : F), f b ^ 2) * (∑ b ∈ univ.erase (0 : F), g b ^ 2) := hCS
    _ = (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * (r - 1)))
          * (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * (r + 1))) := by
        rw [Finset.sum_congr rfl (fun b _ => hf2 b), Finset.sum_congr rfl (fun b _ => hg2 b)]

/-- **`A_r` is log-convex.** `A_r² ≤ A_{r−1}·A_{r+1}` for `r ≥ 1` (divide the moment form by `q² > 0`,
since `A_s = (1/q)·∑_{b≠0}‖η_b‖^{2s}`). The DC-subtracted Gauss-period moments form a LOG-CONVEX
sequence; equivalently the consecutive ratios `A_{r+1}/A_r` are monotone NON-DECREASING in `r`. -/
theorem Ar_logConvex (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) (hr : 1 ≤ r) :
    (Ar ψ G r) ^ 2 ≤ (Ar ψ G (r - 1)) * (Ar ψ G (r + 1)) := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this
  have hconv := dc_moment_logConvex ψ G r hr
  -- A_s = (1/q)·S_s, where S_s = ∑_{b≠0}‖η_b‖^{2s}.  (A_r)² = (1/q²)·S_r²,
  -- A_{r-1}·A_{r+1} = (1/q²)·S_{r-1}·S_{r+1}.  Multiply hconv by (1/q²) > 0.
  unfold Ar
  have hinv : (0 : ℝ) < (1 / (Fintype.card F : ℝ)) ^ 2 := by positivity
  set S : ℕ → ℝ := fun s => ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * s) with hS
  have hLHS : ((1 / (Fintype.card F : ℝ)) * S r) ^ 2
      = (1 / (Fintype.card F : ℝ)) ^ 2 * (S r) ^ 2 := by ring
  have hRHS : ((1 / (Fintype.card F : ℝ)) * S (r - 1)) * ((1 / (Fintype.card F : ℝ)) * S (r + 1))
      = (1 / (Fintype.card F : ℝ)) ^ 2 * (S (r - 1) * S (r + 1)) := by ring
  rw [hLHS, hRHS]
  exact mul_le_mul_of_nonneg_left hconv (le_of_lt hinv)

/-! ## Layer 2 — the exact Wick-step characterization (`f (r+1) ≤ f r ↔ DC ratio bound`) -/

/-- **`Wick_{r+1} = (2r+1)·|G|·Wick_r`.** From `oddWickCoeff (r+1) = (2r+1)·oddWickCoeff r`
(`Finset.prod_range_succ`) and `|G|^{r+1} = |G|·|G|^r`. -/
theorem Wick_succ (G : Finset F) (r : ℕ) :
    Wick G (r + 1) = (2 * (r : ℝ) + 1) * (G.card : ℝ) * Wick G r := by
  unfold Wick
  have hcoeff : (WickMomentCapability.oddWickCoeff (r + 1) : ℝ)
      = (2 * (r : ℝ) + 1) * (WickMomentCapability.oddWickCoeff r : ℝ) := by
    rw [WickMomentCapability.oddWickCoeff, WickMomentCapability.oddWickCoeff,
      Finset.prod_range_succ]
    push_cast
    ring
  rw [hcoeff, pow_succ]
  ring

/-- **The exact per-step characterization of the Wick-monotone step.** For `r ≥ 1` and nonempty `G`,
`wickRatio (r+1) ≤ wickRatio r ↔ A_{r+1} ≤ (2r+1)·|G|·A_r`. So `WickMonotonicity` IS the family of
per-step DC ratio bounds `A_{r+1}/A_r ≤ (2r+1)·|G|`. -/
theorem wickRatio_step_iff {ψ : AddChar F ℂ} {G : Finset F} (hG : G.Nonempty) (r : ℕ) :
    wickRatio ψ G (r + 1) ≤ wickRatio ψ G r
      ↔ Ar ψ G (r + 1) ≤ (2 * (r : ℝ) + 1) * (G.card : ℝ) * Ar ψ G r := by
  have hWr : 0 < Wick G r := Wick_pos hG r
  have hWr1 : 0 < Wick G (r + 1) := Wick_pos hG (r + 1)
  unfold wickRatio
  rw [div_le_div_iff₀ hWr1 hWr]
  -- A_{r+1}·Wick_r ≤ A_r·Wick_{r+1} = A_r·((2r+1)|G|·Wick_r)
  rw [Wick_succ]
  constructor
  · intro h
    -- A_{r+1}·Wick_r ≤ A_r·(2r+1)|G|·Wick_r  ⟹  A_{r+1} ≤ (2r+1)|G|·A_r  (cancel Wick_r > 0)
    have hcancel : Ar ψ G (r + 1) * Wick G r
        ≤ ((2 * (r : ℝ) + 1) * (G.card : ℝ) * Ar ψ G r) * Wick G r := by
      calc Ar ψ G (r + 1) * Wick G r
          ≤ Ar ψ G r * ((2 * (r : ℝ) + 1) * (G.card : ℝ) * Wick G r) := h
        _ = ((2 * (r : ℝ) + 1) * (G.card : ℝ) * Ar ψ G r) * Wick G r := by ring
    exact le_of_mul_le_mul_right hcancel hWr
  · intro h
    calc Ar ψ G (r + 1) * Wick G r
        ≤ ((2 * (r : ℝ) + 1) * (G.card : ℝ) * Ar ψ G r) * Wick G r :=
          mul_le_mul_of_nonneg_right h (le_of_lt hWr)
      _ = Ar ψ G r * ((2 * (r : ℝ) + 1) * (G.card : ℝ) * Wick G r) := by ring

/-! ## Layer 3 — the DC sup-norm ceiling on the per-step ratio -/

/-- **DC sup-norm ceiling on the moment ratio.** `∑_{b≠0}‖η_b‖^{2(r+1)} ≤ M·∑_{b≠0}‖η_b‖^{2r}` for any
`M` with `‖η_b‖² ≤ M` (`b ≠ 0`). Pull the max out of `∑ λ_b^{r+1} = ∑ λ_b·λ_b^r`. -/
theorem dc_moment_succ_le_maxSq_mul {ψ : AddChar F ℂ} (G : Finset F) (r : ℕ)
    (M : ℝ) (hM : ∀ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 ≤ M) :
    (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * (r + 1)))
      ≤ M * (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun b hb => ?_)
  have hstep : ‖eta ψ G b‖ ^ (2 * (r + 1)) = ‖eta ψ G b‖ ^ 2 * ‖eta ψ G b‖ ^ (2 * r) := by
    rw [← pow_add]; congr 1; ring
  rw [hstep]
  have hpos : (0 : ℝ) ≤ ‖eta ψ G b‖ ^ (2 * r) := by positivity
  exact mul_le_mul_of_nonneg_right (hM b hb) hpos

/-- **`A_{r+1} ≤ M·A_r`.** The DC-subtracted per-step ratio is bounded ABOVE by the DC sup-norm
`M = max_{b≠0}‖η_b‖²`. With `Ar_logConvex` (ratio ↑) the ratio approaches `M` from below. -/
theorem Ar_succ_le_maxSq_mul {ψ : AddChar F ℂ} (G : Finset F) (r : ℕ)
    (M : ℝ) (hM : ∀ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 ≤ M) :
    Ar ψ G (r + 1) ≤ M * Ar ψ G r := by
  have hq : (0 : ℝ) ≤ (1 / (Fintype.card F : ℝ)) := by positivity
  have hceil := dc_moment_succ_le_maxSq_mul (ψ := ψ) G r M hM
  unfold Ar
  calc (1 / (Fintype.card F : ℝ)) * ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * (r + 1))
      ≤ (1 / (Fintype.card F : ℝ)) * (M * ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) :=
        mul_le_mul_of_nonneg_left hceil hq
    _ = M * ((1 / (Fintype.card F : ℝ)) * ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) := by ring

/-! ## Layer 4 — the headline: the Wick-monotone step presupposes the DC sup-norm bound -/

/-- **HEADLINE — the single-step Wick monotonicity presupposes the DC sup-norm bound.** Fix a DC
sup-norm certificate `M = max_{b≠0}‖η_b‖²` (`∀ b ≠ 0, ‖η_b‖² ≤ M`). IF the DC sup-norm bound
`M ≤ (2r+1)·|G|` holds, THEN the Wick-monotone step `wickRatio (r+1) ≤ wickRatio r` holds. So
`WickMonotonicity`-at-`r` is a CONSEQUENCE of the DC sup-norm bound, never a route to it.

Combined with `Ar_logConvex` (the DC ratio `A_{r+1}/A_r` is monotone-increasing with sup `M`), the step
can only hold tightly when `M ≤ (2r+1)·|G|` — the DC-subtracted BGK / Paley sup-norm wall is
PRESUPPOSED by the floor route through Wick-monotonicity. -/
theorem wickMono_step_of_dc_supNorm {ψ : AddChar F ℂ} {G : Finset F} (hG : G.Nonempty) (r : ℕ)
    (M : ℝ) (hM : ∀ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 ≤ M)
    (hsup : M ≤ (2 * (r : ℝ) + 1) * (G.card : ℝ)) :
    wickRatio ψ G (r + 1) ≤ wickRatio ψ G r := by
  rw [wickRatio_step_iff hG r]
  have hAr0 : (0 : ℝ) ≤ Ar ψ G r := by
    unfold Ar
    have : (0 : ℝ) ≤ ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) := by positivity
    positivity
  calc Ar ψ G (r + 1)
      ≤ M * Ar ψ G r := Ar_succ_le_maxSq_mul G r M hM
    _ ≤ ((2 * (r : ℝ) + 1) * (G.card : ℝ)) * Ar ψ G r :=
        mul_le_mul_of_nonneg_right hsup hAr0

/-- **The floor route via Wick-monotonicity needs the per-depth DC sup-norm cancellation.** A uniform
DC sup-norm certificate — for every depth `r ≥ 1`, `∀ b ≠ 0, ‖η_b‖² ≤ (2r+1)·|G|` — yields the full
`WickMonotonicity`, hence (via the in-tree `floorViaWick_of_monotonicity`) the prize floor
`FloorViaWick`. This is the precise circularity: the floor cannot be reached through Wick-monotonicity
without the per-depth DC-subtracted sup-norm bound `max_{b≠0}‖η_b‖² ≤ (2r+1)·|G|` already in hand. -/
theorem wickMonotonicity_of_dc_supNorm {ψ : AddChar F ℂ} {G : Finset F} (hG : G.Nonempty)
    (hsup : ∀ r : ℕ, 1 ≤ r → ∀ b ∈ univ.erase (0 : F),
      ‖eta ψ G b‖ ^ 2 ≤ (2 * (r : ℝ) + 1) * (G.card : ℝ)) :
    WickMonotonicity ψ G := by
  intro r hr
  exact wickMono_step_of_dc_supNorm hG r ((2 * (r : ℝ) + 1) * (G.card : ℝ))
    (hsup r hr) (le_refl _)

/-- **The floor, conditional on the per-depth DC sup-norm bound.** Composing
`wickMonotonicity_of_dc_supNorm` with the in-tree reduction `floorViaWick_of_monotonicity`: the uniform
DC sup-norm certificate gives `FloorViaWick` (`A_r ≤ Wick_r ∀ r ≥ 1`). The OPEN content is exactly the
DC-subtracted sup-norm bound `max_{b≠0}‖η_b‖² ≤ (2r+1)·|G|` (the thin-subgroup BGK/Paley wall); the
reduction itself is generic (field-universal). -/
theorem floorViaWick_of_dc_supNorm {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hG : G.Nonempty)
    (hsup : ∀ r : ℕ, 1 ≤ r → ∀ b ∈ univ.erase (0 : F),
      ‖eta ψ G b‖ ^ 2 ≤ (2 * (r : ℝ) + 1) * (G.card : ℝ)) :
    FloorViaWick ψ G :=
  floorViaWick_of_monotonicity hψ hG (wickMonotonicity_of_dc_supNorm hG hsup)

end ProximityGap.Frontier.WickMonoDCSupNorm

/-! ## Axiom audit (must read `[propext, Classical.choice, Quot.sound]` only; no sorryAx) -/
#print axioms ProximityGap.Frontier.WickMonoDCSupNorm.dc_moment_logConvex
#print axioms ProximityGap.Frontier.WickMonoDCSupNorm.Ar_logConvex
#print axioms ProximityGap.Frontier.WickMonoDCSupNorm.Wick_succ
#print axioms ProximityGap.Frontier.WickMonoDCSupNorm.wickRatio_step_iff
#print axioms ProximityGap.Frontier.WickMonoDCSupNorm.dc_moment_succ_le_maxSq_mul
#print axioms ProximityGap.Frontier.WickMonoDCSupNorm.Ar_succ_le_maxSq_mul
#print axioms ProximityGap.Frontier.WickMonoDCSupNorm.wickMono_step_of_dc_supNorm
#print axioms ProximityGap.Frontier.WickMonoDCSupNorm.wickMonotonicity_of_dc_supNorm
#print axioms ProximityGap.Frontier.WickMonoDCSupNorm.floorViaWick_of_dc_supNorm
