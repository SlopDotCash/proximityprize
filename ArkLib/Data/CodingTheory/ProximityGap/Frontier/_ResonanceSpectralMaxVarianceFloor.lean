/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralVariance

/-!
# The worst-frequency kernel mass exceeds the mean by the normalized spectral variance (#444)

The companion files `_ResonanceTowerRatioSpectralCap` / `_ResonanceTowerGeometricEnvelope` localized
the open content of the named door-(iv) tower to the **squared spectral sup-norm**
`μ := max_k ‖K̂(k)‖²` — the worst single-frequency Gauss-period kernel mass (the BGK object). Those
were UPPER-side statements (`T(r+1)/T(r) ≤ μ`, `T r ≤ μ^r`), with `μ` supplied as a free realised
upper bound.

This file lands a **lower bound on `μ` itself**, driven by the spectral variance. Apply the BGK lower
engine `(∑ w²)/(∑ w) ≤ max w` (inlined here as `ratio_le_max_local`, the standard
`a_i² ≤ (max a)·a_i` term-by-term bound) to the spectral weights
`w_k = ‖K̂(k)‖²`, then evaluate the two power sums via the Parseval bridge
(`∑ w_k² = m·T 2`, `∑ w_k = m·(m−1)`):

> **`max_k ‖K̂(k)‖² ≥ T 2 / (m−1) = (m−1) + (T 2 − (m−1)²)/(m−1)`**
> (`specMaxSq_ge_quadratic_mean`, `specMaxSq_ge_mean_add_normalized_variance`),

where `T 2 − (m−1)²` is exactly the spectral variance `(1/m)∑_k (‖K̂(k)‖² − (m−1))²`
(`_ResonanceSpectralVariance.sum_sq_centered_kernelSpectrum_eq`). Equivalently the worst frequency
exceeds the Plancherel mean `m−1` by at least `Var/(m−1) ≥ 0`.

## Door-(iv) reading: any spectral spread forces the worst frequency above the floor

The two-sided sandwich pinned the tower growth ratio in `[m−1, μ]`. Here we bound `μ` from BELOW by the
mean plus the normalized variance: the BGK object `μ` cannot collapse to the Plancherel mean `m−1`
unless the spectrum is exactly flat (`Var = 0`, the Ramanujan/equidistributed case already
characterized by `_ResonanceFlatnessCriterion`). So **any** second-moment spread (`T 2 > (m−1)²`,
which is the generic Gauss-period regime) forces `μ` STRICTLY above the floor by a variance-controlled
amount — the worst frequency is the carrier of the spread, not the mean. This is the lower-side
companion of the upper envelope: together they bracket the open object `μ` between
`(m−1) + Var/(m−1)` and the trivial `(m−1)²`, with the prize collapse living in that gap.

## Honest scope (rules 1,3,6)

CERTAIN exact consequence of the BGK lower engine + the Parseval bridge + the variance identity. This
is a LOWER bound on `μ` (the open object), so it pushes the open object UP, away from the prize regime
`μ = O(m log m)` — it is the wrong-way (lower) companion that confirms `μ` is genuinely large unless
the spectrum is flat. It does NOT bound `μ` from above (that IS the open prize), and is NOT
thinness-essential (rule 3): it holds in the thick window too. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED /
OPEN. No CORE / cancellation / completion / moment-as-proof / anti-concentration / capacity claim.
Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- Spectral weight `w_k = ‖K̂(k)‖²`. -/
private noncomputable def w (u : ZMod m → ℂ) (k : ZMod m) : ℝ :=
  ‖kernelSpectrum (dftChar k) u‖ ^ 2

private theorem w_nonneg (u : ZMod m → ℂ) (k : ZMod m) : 0 ≤ w u k := by
  unfold w; positivity

/-- **BGK lower engine (inlined, leaf).** For a nonempty finite nonnegative family with positive
total, the max dominates the quadratic mean: `∃ i₀, (∑ a²)/(∑ a) ≤ a i₀`. Term-by-term
`a_j² ≤ (max a)·a_j`. (Self-contained copy of `_BGKTwoSided.ratio_le_max` to keep this file a leaf
over built modules only — the BGK file is an orphan whose olean is not on the build path.) -/
private theorem ratio_le_max_local {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (hne : s.Nonempty) (ha : ∀ i ∈ s, 0 ≤ a i) (hpos : 0 < ∑ i ∈ s, a i) :
    ∃ i₀ ∈ s, (∑ j ∈ s, (a j) ^ 2) / (∑ j ∈ s, a j) ≤ a i₀ := by
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image a hne
  refine ⟨i₀, hi₀, ?_⟩
  rw [div_le_iff₀ hpos, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have h0 := ha j hj
  have h1 := hmax j hj
  nlinarith [h0, h1]

/-- `∑_k w_k = m·(m−1)` (spectral mean, unit phases). -/
private theorem sum_w_eq (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    (∑ k : ZMod m, w u k) = (m : ℝ) * ((m : ℝ) - 1) := by
  unfold w; exact sum_normSq_kernelSpectrum_eq u hu

/-- `∑_k w_k² = m·T 2` (Parseval bridge at `r = 2`). -/
private theorem sum_w_sq_eq (u : ZMod m → ℂ) :
    (∑ k : ZMod m, (w u k) ^ 2) = (m : ℝ) * resonanceMoment u 2 := by
  classical
  unfold w
  rw [resonanceMoment_eq_spectral_powerMean u 2]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← pow_mul]

/-- **The worst-frequency mass dominates the quadratic mean of the spectrum** (unit phases, `m ≥ 2`):
there is a frequency `b₀` whose squared kernel mass realises the max and satisfies
`T 2 / (m−1) ≤ ‖K̂(b₀)‖²`. The BGK lower engine `(∑ w²)/(∑ w) ≤ max w` evaluated through the bridge
`∑ w² = m·T 2`, `∑ w = m·(m−1)`. -/
theorem specMaxSq_ge_quadratic_mean (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) :
    ∃ b₀ : ZMod m, resonanceMoment u 2 / ((m : ℝ) - 1)
      ≤ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2 := by
  classical
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  have hm1pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  -- total energy ∑ w = m·(m-1) > 0
  have hsumpos : 0 < ∑ k : ZMod m, w u k := by
    rw [sum_w_eq u hu]; positivity
  -- BGK lower engine on the weights w over univ
  obtain ⟨b₀, _, hb₀⟩ :=
    ratio_le_max_local (Finset.univ) (w u)
      Finset.univ_nonempty (fun i _ => w_nonneg u i) hsumpos
  -- rewrite the abstract ratio (∑ w²)/(∑ w) as (m·T2)/(m·(m-1)) = T2/(m-1)
  rw [sum_w_sq_eq u, sum_w_eq u hu] at hb₀
  have hsimp :
      ((m : ℝ) * resonanceMoment u 2) / ((m : ℝ) * ((m : ℝ) - 1))
        = resonanceMoment u 2 / ((m : ℝ) - 1) := by
    rw [mul_div_mul_left _ _ (ne_of_gt hmpos)]
  rw [hsimp] at hb₀
  exact ⟨b₀, by simpa [w] using hb₀⟩

/-- **The worst frequency exceeds the Plancherel mean by the normalized spectral variance** (unit
phases, `m ≥ 2`): there is `b₀` realising the spectral max with
`(m−1) + (T 2 − (m−1)²)/(m−1) ≤ ‖K̂(b₀)‖²`, where `T 2 − (m−1)² ≥ 0` is the spectral variance. Hence
the worst-frequency kernel mass collapses to the mean `m−1` only when the spectrum is flat
(`Var = 0`). -/
theorem specMaxSq_ge_mean_add_normalized_variance (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) :
    ∃ b₀ : ZMod m,
      ((m : ℝ) - 1) + (resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2) / ((m : ℝ) - 1)
        ≤ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2 := by
  obtain ⟨b₀, hb₀⟩ := specMaxSq_ge_quadratic_mean u hu hm
  refine ⟨b₀, ?_⟩
  have hm1pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  -- (m-1) + (T2 - (m-1)²)/(m-1) = T2/(m-1):  combine over the common denominator
  have hid :
      ((m : ℝ) - 1) + (resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2) / ((m : ℝ) - 1)
        = resonanceMoment u 2 / ((m : ℝ) - 1) := by
    field_simp
    ring
  rw [hid]
  exact hb₀

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.specMaxSq_ge_quadratic_mean
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.specMaxSq_ge_mean_add_normalized_variance
