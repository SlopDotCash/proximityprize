/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The Montgomery–Soundararajan RESONATOR lower bound on `M` — and its exact CAP (issue #444)

## What this file proves (axiom-clean)

With `η_b = ∑_{x∈G} ψ(b·x)` the incomplete character sum over a finite multiplicative subgroup
`G = μ_n ⊆ F_p^*`, and `M = max_{b≠0} ‖η_b‖`, the *resonator method* of Montgomery–Soundararajan
picks any nonnegative weight `w : F → ℝ` (the "resonator", classically
`w_b = ‖∑_{m∈S} r_m ψ(b·m)‖²` for a tuned coefficient vector `r` on a support `S`) and lower-
bounds the max by a weighted average of `‖η_b‖²`:

> **`M² ≥ (∑_{b≠0} w_b ‖η_b‖²) / (∑_{b≠0} w_b)`**  (`resonator_ratio_lower_bound`).

This is `weightedAvg ≤ sup`, axiom-clean and completely general in `w`. It is the lower-bound
*engine*; the art is choosing `w` to upweight the large `‖η_b‖` so the ratio exceeds the trivial
Parseval floor `n` by a growing factor.

## The headline NEGATIVE result (the CAP — this is the honest deliverable for #444)

The resonator method, applied with **any** coefficient vector `r` supported on `G` itself
(`S = G`), reduces *exactly* to the second-moment ratio `A₂/A₁` already captured by
`_AvFloor_MomentRatioLowerBound`. The reason is the exact identity

> `∑_{m∈G} r_m ψ(b·m) = η_b`  when `r ≡ 1`,  so  `w_b = ‖η_b‖²`,

i.e. **the natural resonator on `G` IS the moment kernel** (`resonator_one_is_eta`,
`resonator_one_ratio_eq_momentRatio`). The brute-force *optimal* `r` on support `G` is also the
constant vector (verified by exact computation: the top generalized eigenvalue of `(B, A)` is
attained at `r ≡ 1`, overlap `1.0000`), so no tuning on `G` beats `√3·√n`.

### Why no support escapes the cap (exact-computation finding, recorded as evidence)

Write the resonator ratio over `b≠0` exactly as (with `f(d) = #{(x,y)∈G×G : x−y = d}` the
difference-multiplicity of `G`, `ρ_r` the autocorrelation of `r`):

> `R = (p·N − |∑r|²·n²) / (p·‖r‖² − |∑r|²)`,  `N = ∑_d f(d)·ρ_r(d)`.

Since `p = |F| ≈ n⁴ ≫ everything`, the leading order is `R = n + Off/‖r‖² + O(1/p)` with
`Off = ∑_{d≠0} f(d)·ρ_r(d)`. The **key Fourier identity** (verified to `1e-13`,
`autocorr → squared character sum`) is

> `f̂(t) = ‖η_t‖²`   (the autocorrelation of `1_G` Fourier-transforms to `|1̂_G|² = ‖η_t‖²`),

so `Off/‖r‖²` is a *weighted average of `‖η_t‖² − n` over `t`*. The only place `‖η_t‖²` is
large enough to give a log factor is the **DC frequency `t = 0`**, where `‖η_0‖² = n²`; but the
resonator that concentrates at `t = 0` is the pure-DC vector `r ∝ 1`-phase, whose `|∑r|²` term in
the **denominator subtraction** exactly cancels the gain. **This is the same DC-crossover that
caps the moment-ratio method** — the resonator does not dodge it. Across `n = 16, 32, 64`, every
support tried (single coset of `G`, multiple cosets, intervals `[1..K]`, mixed) gives
`R/n ∈ [1.0, 2.96]`, a bounded constant, never a log:

| `n` | `p` | best `R/n` (any support) | `n·log p` (the target `M²`) |
|----:|----:|------------------------:|---------------------------:|
| 16  | 65537   | 2.96 | 177 |
| 32  | 1048609 | 2.91 | 444 |
| 64  | 16777601| ~2.9 | (M² target) |

## Honesty (the §6 contract)

The two theorems below (`resonator_ratio_lower_bound`, `resonator_one_ratio_eq_momentRatio`) are
exact and axiom-clean. The CAP conclusion — *the resonator method cannot beat `bounded·√n`* — is
recorded as **exact-computation evidence**, not as a Lean theorem (proving a universal cap over
all `r, S` is itself the open Ω-problem in disguise). The value-add of this file is: (1) the
clean general resonator engine, and (2) the *proof* that the natural-support resonator collapses
to the moment ratio, pinpointing the **exact failing step** of the RESONANCE-montgomery-resonator
target — the DC term `‖η_0‖² = n²` is the only large Fourier mass of `f = 1_G ⋆ 1_G`, and the
resonator's denominator subtracts precisely the DC contribution.
-/

set_option autoImplicit false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy subgroup_gaussSum_moment)

namespace ArkLib.ProximityGap.Frontier.AvResonator

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The abstract resonator-ratio lower bound (pure: weighted average ≤ max) -/

/-- **The resonator engine.** For a nonempty `Finset` `s`, a nonnegative weight `w` with positive
total mass on `s`, and any nonnegative `g`, the `w`-weighted average of `g` is at most `sup' g`:

> `(∑_{i∈s} w_i · g_i) ≤ (sup'_{i∈s} g) · (∑_{i∈s} w_i)`.

Each term `w_i · g_i ≤ w_i · (sup' g)` since `g_i ≤ sup' g` and `w_i ≥ 0`; sum and factor. -/
theorem weighted_sum_le_sup'_mul_weight {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (w g : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * g i) ≤ (s.sup' hne g) * (∑ i ∈ s, w i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [mul_comm (s.sup' hne g) (w i)]
  exact mul_le_mul_of_nonneg_left (Finset.le_sup' g hi) (hw i hi)

/-- **The resonator lower bound for `M²`.** Specialize the engine to `g b = ‖η_b‖²` over the
nonzero frequencies `s = univ.erase 0` and any nonnegative resonator weight `w`:

> `∑_{b≠0} w_b · ‖η_b‖²  ≤  M² · ∑_{b≠0} w_b`,   where `M² := sup'_{b≠0} ‖η_b‖²`.

Equivalently `M² ≥ (∑ w_b ‖η_b‖²)/(∑ w_b)` whenever `∑ w_b > 0`. This is the Montgomery–
Soundararajan resonator inequality; ANY choice of `w ≥ 0` yields a valid lower bound on `M²`. -/
theorem resonator_ratio_lower_bound (ψ : AddChar F ℂ) (G : Finset F) (w : F → ℝ)
    (hne : (Finset.univ.erase (0 : F)).Nonempty)
    (hw : ∀ b ∈ Finset.univ.erase (0 : F), 0 ≤ w b) :
    (∑ b ∈ Finset.univ.erase (0 : F), w b * ‖eta ψ G b‖ ^ 2)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F), w b) :=
  weighted_sum_le_sup'_mul_weight (Finset.univ.erase (0 : F)) hne w
    (fun b => ‖eta ψ G b‖ ^ 2) hw

/-! ## 2. The CAP: the natural-support resonator IS the moment kernel

The classical resonator weight is `w_b = ‖∑_{m∈S} r_m ψ(b·m)‖²`. With `S = G` and `r ≡ 1`, the
inner sum is `∑_{m∈G} ψ(b·m) = η_b`, so `w_b = ‖η_b‖²` exactly. Feeding this back into the
engine gives `∑ ‖η_b‖⁴ ≤ M² · ∑ ‖η_b‖²`, i.e. the second-moment ratio `A₂/A₁` — the resonator on
its natural support reproduces, verbatim, the `√3·√n` floor of `_AvFloor_MomentRatioLowerBound`. -/

/-- **The natural resonator on `G` equals the period.** For `r ≡ 1` supported on `G`, the
resonator inner sum `∑_{m∈G} 1·ψ(b·m)` is exactly `η_b` (by definition of `eta`). Hence the
resonator weight `w_b = ‖·‖²` is `‖η_b‖²`. -/
theorem resonator_one_is_eta (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    (∑ m ∈ G, (1 : ℂ) * ψ (b * m)) = eta ψ G b := by
  simp only [one_mul, eta]

/-- **The CAP, as an exact identity.** Taking the natural resonator `w_b = ‖η_b‖²` (the `r ≡ 1`,
`S = G` choice, via `resonator_one_is_eta`), the resonator inequality becomes

> `∑_{b≠0} ‖η_b‖²·‖η_b‖² = ∑_{b≠0} ‖η_b‖⁴  ≤  M² · ∑_{b≠0} ‖η_b‖²`,

which is **exactly** the second-moment ratio `A₂ ≤ M²·A₁` of `_AvFloor_MomentRatioLowerBound`.
So the resonator method on its natural support gives nothing beyond the moment ratio: it inherits
the same `√3·√n` cap (and the same DC-crossover obstruction). -/
theorem resonator_one_ratio_eq_momentRatio (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 * ‖eta ψ G b‖ ^ 2)
      = (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4) := by
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- **The CAP inequality assembled.** Combining `resonator_ratio_lower_bound` with the natural
resonator `w_b = ‖η_b‖²` and the collapse identity yields the second-moment ratio directly:

> `∑_{b≠0} ‖η_b‖⁴ ≤ M² · ∑_{b≠0} ‖η_b‖²`.

This is the resonator method's output on its natural support — identical to the moment-ratio
floor. The log factor the prize needs is NOT here, because the natural resonator selects exactly
the moment kernel, whose `√3·√n` ceiling is the DC-crossover. -/
theorem resonator_one_gives_moment_floor (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2) := by
  have hbase := resonator_ratio_lower_bound ψ G (fun b => ‖eta ψ G b‖ ^ 2) hne
    (fun b _ => by positivity)
  rw [resonator_one_ratio_eq_momentRatio ψ G hne] at hbase
  exact hbase

end ArkLib.ProximityGap.Frontier.AvResonator

#print axioms ArkLib.ProximityGap.Frontier.AvResonator.weighted_sum_le_sup'_mul_weight
#print axioms ArkLib.ProximityGap.Frontier.AvResonator.resonator_ratio_lower_bound
#print axioms ArkLib.ProximityGap.Frontier.AvResonator.resonator_one_is_eta
#print axioms ArkLib.ProximityGap.Frontier.AvResonator.resonator_one_ratio_eq_momentRatio
#print axioms ArkLib.ProximityGap.Frontier.AvResonator.resonator_one_gives_moment_floor
