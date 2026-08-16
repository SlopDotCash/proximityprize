/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.style.longLine false

/-!
# Two-sided moment localization: the reverse-Markov lower companion (#389, #371)

The Shaw operator (`ProximityGap.ShawOperator`) reduces δ\* to the worst-case subgroup Gauss period
`max_{b≠0}‖η_b‖` (the incomplete character sum over `μ_n`). The proven moment identity
`∑_b ‖η_b‖^{2r} = q·E_r(G)` (`subgroup_gaussSum_moment`, all `r`, axiom-clean) has so far been read
only as an UPPER feeder (Markov: `max^{2r} ≤ q·E_r`). This file supplies the missing LOWER half — the
**reverse-Markov / consecutive-moment-ratio** companion, generalizing `exists_period_sq_ge` (the
`r=2` case in `WorstPeriodLowerBound`) to every `r ≥ 1`:

> `exists_period_sq_ge_moment_ratio` :  `∃ b ≠ 0,
>     q·E_r − |G|^{2r}  ≤  ‖η_b‖² · (q·E_{r−1} − |G|^{2(r−1)})`,

i.e. `max_{b≠0}‖η_b‖² ≥ (q·E_r − |G|^{2r}) / (q·E_{r−1} − |G|^{2(r−1)})`.

It is proven from the same moment identity, with **no Weil bound and no open input**: peel `η_0 = |G|`
from both the `2r`-th and `(2r−2)`-th moments, then bound
`‖η_b‖^{2r} = ‖η_b‖²·‖η_b‖^{2(r−1)} ≤ max·‖η_b‖^{2(r−1)}` over the nonzero frequencies.

**Why it matters (the two-sided localization).** Pairing this lower companion with the upper Markov
brackets the worst period as `(q·E_r/s)^{1/2r} ≲ max‖η_b‖² ≲ (q·E_r)^{1/r}` (here the consecutive
ratio plays the role of `q·E_r/s`). At the optimizing exponent `r ≈ log(q/n)` the two sides meet at
the prize scale `Θ(√(n·log(q/n)))` — *conditional on* the single named two-sided growth law on the
energy ratio `E_r(μ_n)/E_{r−1}(μ_n)`. This converts the worst-case Shaw bound from an unstructured
sup-norm (upper-only) into an **exactness-ready two-sided** target. It does NOT close the prize: the
residual energy-ratio growth at variable `r` is still wall W4 (sub-`√q` cancellation over `μ_n`),
now in its most falsifiable, two-sided form. This is honest progress toward — not a closure of — δ\*.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- `η_0 = |G|`, so `‖η_0‖^m = |G|^m` for every exponent `m`. -/
private theorem eta_zero_pow (ψ : AddChar F ℂ) (G : Finset F) (m : ℕ) :
    ‖eta ψ G (0 : F)‖ ^ m = (G.card : ℝ) ^ m := by
  have h0 : eta ψ G (0 : F) = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  rw [h0, Complex.norm_natCast]

/-- **Consecutive-moment-ratio lower bound on the worst period (all `r`).**
Generalizes `exists_period_sq_ge` (the `r=2` case) to every `r ≥ 1`: there is a nontrivial
frequency `b ≠ 0` with the cross-multiplied bound
`q·E_r − |G|^{2r} ≤ ‖η_b‖²·(q·E_{r−1} − |G|^{2(r−1)})`, equivalently
`max_{b≠0}‖η_b‖² ≥ (q·E_r − |G|^{2r})/(q·E_{r−1} − |G|^{2(r−1)})`.
Reverse-Markov against the proven moment identity `∑_b ‖η_b‖^{2r} = q·E_r`: peel `η_0 = |G|` and
use `‖η_b‖^{2r} = ‖η_b‖²·‖η_b‖^{2(r−1)} ≤ max·‖η_b‖^{2(r−1)}`. The LOWER companion that upgrades the
moment ladder from upper-only to two-sided; no Weil, no open input. -/
theorem exists_period_sq_ge_moment_ratio {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hr : 1 ≤ r) :
    ∃ b : F, b ≠ 0 ∧
      (Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r)
        ≤ ‖eta ψ G b‖ ^ 2 *
            ((Fintype.card F : ℝ) * rEnergy G (r - 1) - (G.card : ℝ) ^ (2 * (r - 1))) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set S : Finset F := Finset.univ.erase (0 : F) with hS
  have hmemS : ∀ b : F, b ∈ S ↔ b ≠ 0 := by
    intro b; rw [hS, Finset.mem_erase]; simp
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : F)
    exact ⟨x, (hmemS x).mpr hx⟩
  -- the `2r`-th and `(2r−2)`-th moments restricted to the nonzero frequencies
  have hsumr : ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r) = q * rEnergy G r - (G.card : ℝ) ^ (2 * r) := by
    have hsplit := (Finset.add_sum_erase Finset.univ
      (fun b => ‖eta ψ G b‖ ^ (2 * r)) (Finset.mem_univ (0 : F))).symm
    rw [subgroup_gaussSum_moment hψ G r] at hsplit
    rw [← hS, eta_zero_pow ψ G (2 * r)] at hsplit
    linarith
  have hsumr1 : ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * (r - 1))
      = q * rEnergy G (r - 1) - (G.card : ℝ) ^ (2 * (r - 1)) := by
    have hsplit := (Finset.add_sum_erase Finset.univ
      (fun b => ‖eta ψ G b‖ ^ (2 * (r - 1))) (Finset.mem_univ (0 : F))).symm
    rw [subgroup_gaussSum_moment hψ G (r - 1)] at hsplit
    rw [← hS, eta_zero_pow ψ G (2 * (r - 1))] at hsplit
    linarith
  obtain ⟨b₀, hb₀S, hb₀max⟩ := S.exists_max_image (fun b => ‖eta ψ G b‖ ^ 2) hSne
  refine ⟨b₀, (hmemS b₀).mp hb₀S, ?_⟩
  -- key reverse-Markov step: `∑ ‖η_b‖^{2r} ≤ max‖η‖² · ∑ ‖η_b‖^{2(r−1)}`
  have hexp : 2 * r = 2 + 2 * (r - 1) := by omega
  have hkey : ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r)
      ≤ ‖eta ψ G b₀‖ ^ 2 * ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * (r - 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun b hb => ?_)
    have hpow : ‖eta ψ G b‖ ^ (2 * r)
        = ‖eta ψ G b‖ ^ 2 * ‖eta ψ G b‖ ^ (2 * (r - 1)) := by rw [hexp, pow_add]
    rw [hpow]
    exact mul_le_mul_of_nonneg_right (hb₀max b hb) (by positivity)
  rw [hsumr, hsumr1] at hkey
  exact hkey

end ArkLib.ProximityGap.SubgroupGaussSumMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.exists_period_sq_ge_moment_ratio
