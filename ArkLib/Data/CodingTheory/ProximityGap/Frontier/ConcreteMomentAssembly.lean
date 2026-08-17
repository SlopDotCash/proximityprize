/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031OrbitCountPartition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ProveAssembly

/-!
# The CONCRETE moment hypothesis for the prize assembly (#444)

`_ProveAssembly.prize_floor_of_noWraparound` reduces the prize to a single named residual
`hNoWrap : E = E0`, but it consumes the moment identity

> `hMoment : M^{2r} ≤ q·E − n^{2r}`

as an *abstract real hypothesis* ("a theorem, not an assumption, for the concrete `η`/`E_r`"). It was
NEVER discharged on the concrete analytic objects in-tree. This file supplies that concrete brick:

> `worstPeriod_pow_le_qEnergy_sub_dc` :
>   `M(μ_n)^{2r} ≤ q·E_r(G) − n^{2r}`,  where `M(μ_n) = max_{b≠0} ‖η_b‖`,

PROVEN from the in-tree DC-subtracted moment identity `sum_nonzero_moment`
(`∑_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}`) and the elementary `max ≤ sum` step
(`M^{2r} = max_{b≠0}‖η_b‖^{2r} ≤ ∑_{b≠0}‖η_b‖^{2r}`). This is *exactly* the shape `hMoment` requires,
so the assembly's moment pillar is now a THEOREM for the worst nonzero period, not a carried hypothesis.

Then `concrete_prize_floor_of_noWraparound` instantiates `prize_floor_of_noWraparound` with this
concrete `hMoment` discharged, leaving the SAME single open residual `hNoWrap` (and the char-0
envelope + depth, both proven elsewhere) — a concrete `M(μ_n) ≤ √e·√(2rn)` conditional ONLY on the
named no-wraparound prize core.

## Honesty (the wall is untouched)

This DISCHARGES the moment pillar concretely; it does NOT touch the open residual `hNoWrap : E = E0`
(no `r`-fold wraparound at `r ≈ log p`), which IS the prize (`_NoExcessOnsetThreshold.OnsetExceedsSaddle`).
CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN. Pure consolidation: turns one carried hypothesis of the
assembly into an in-tree theorem over the real `eta`/`rEnergy`.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.Frontier

namespace ProximityGap.Frontier.ConcreteMomentAssembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The worst nonzero period** `M(G) = max_{b≠0} ‖η_b‖`, over the nonzero frequencies. -/
noncomputable def worstPeriod (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) : ℝ :=
  (nonzeroFreqs F).sup' hne (fun b => ‖eta ψ G b‖)

/-- **`M(G) ≥ 0`.** The worst period is a norm sup', hence nonnegative. -/
theorem worstPeriod_nonneg (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) : 0 ≤ worstPeriod ψ G hne := by
  unfold worstPeriod
  obtain ⟨b, hb⟩ := hne
  exact le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖eta ψ G b‖) hb)

/-- **The concrete moment pillar `hMoment` for `μ_n`.** The worst nonzero period satisfies
`M(G)^{2r} ≤ q·E_r(G) − n^{2r}`. Proof: `M^{2r} = (max_{b≠0}‖η_b‖)^{2r} = max_{b≠0}‖η_b‖^{2r}`
(raising the sup' to the `2r`-power, monotone on `≥0`), which is `≤ ∑_{b≠0}‖η_b‖^{2r}` (a single sup'
member is at most the full nonnegative sum), and that sum is exactly `q·E_r − n^{2r}` by the in-tree
DC-subtracted moment identity `sum_nonzero_moment`. Discharges the abstract `hMoment` hypothesis of
`_ProveAssembly.prize_floor_of_noWraparound` on the concrete `eta`/`rEnergy`. -/
theorem worstPeriod_pow_le_qEnergy_sub_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hne : (nonzeroFreqs F).Nonempty) :
    (worstPeriod ψ G hne) ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  -- M^{2r} = max_{b≠0} (‖η_b‖^{2r}) : raise the sup' to the 2r-power (monotone on nonneg)
  obtain ⟨b₀, hb₀, hmax⟩ := (nonzeroFreqs F).exists_mem_eq_sup' hne (fun b => ‖eta ψ G b‖)
  have hMpow : (worstPeriod ψ G hne) ^ (2 * r) = ‖eta ψ G b₀‖ ^ (2 * r) := by
    unfold worstPeriod; rw [hmax]
  rw [hMpow]
  -- ‖η_{b₀}‖^{2r} ≤ ∑_{b≠0} ‖η_b‖^{2r}  (single nonneg term ≤ sum)
  have hb₀mem : b₀ ∈ univ.erase (0 : F) := by
    rw [mem_nonzeroFreqs] at hb₀; exact Finset.mem_erase.mpr ⟨hb₀, Finset.mem_univ b₀⟩
  have hterm : ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) := by
    apply Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r))
    · intro i _; positivity
    · exact hb₀mem
  -- the nonprincipal sum = q·E_r − n^{2r}
  rw [sum_nonzero_moment hψ G r] at hterm
  exact hterm

/-- **Concrete prize floor from the single no-wraparound residual.** Instantiates
`_ProveAssembly.prize_floor_of_noWraparound` with the concrete moment pillar
`worstPeriod_pow_le_qEnergy_sub_dc` discharged. The only remaining inputs are the OPEN residual
`hNoWrap : q·E_r = E0` (no `r`-fold wraparound — the prize core), the proven char-0 envelope
`hChar0 : E0 ≤ (2rn)^r`, and the depth `hdepth : q ≤ exp r`. Conclusion: the worst nonzero period
obeys the prize floor `M(μ_n) ≤ √e·√(2rn)` (at `r ≈ log p` this is `√(2e·n·log p)`).

So the assembly's reduction now holds for the CONCRETE `M(μ_n) = max_{b≠0}‖η_b‖` — its moment pillar
is no longer a carried hypothesis. The wall is unchanged: `hNoWrap` is the named open prize core. -/
theorem concrete_prize_floor_of_noWraparound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {r : ℕ} (hr : 0 < r) (hne : (nonzeroFreqs F).Nonempty)
    {E0 : ℝ}
    (hNoWrap : (rEnergy G r : ℝ) = E0)
    (hChar0 : E0 ≤ (2 * r * (G.card : ℝ)) ^ r)
    (hdepth : (Fintype.card F : ℝ) ≤ Real.exp r) :
    worstPeriod ψ G hne ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * (G.card : ℝ)) := by
  -- assembly E := rEnergy G r, q := |F|, so q·E = Σ_b‖η_b‖^{2r} and q·E − n^{2r} = Σ_{b≠0}.
  exact ArkLib.ProximityGap.Frontier.ProveAssembly.prize_floor_of_noWraparound
    (M := worstPeriod ψ G hne) (q := (Fintype.card F : ℝ)) (n := (G.card : ℝ))
    (E := (rEnergy G r : ℝ)) (E0 := E0)
    hr (worstPeriod_nonneg ψ G hne) (by positivity) (by positivity)
    (worstPeriod_pow_le_qEnergy_sub_dc hψ G r hne) hNoWrap hChar0 hdepth

end ProximityGap.Frontier.ConcreteMomentAssembly

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod_pow_le_qEnergy_sub_dc
#print axioms ProximityGap.Frontier.ConcreteMomentAssembly.concrete_prize_floor_of_noWraparound
