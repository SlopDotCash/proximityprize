/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceTowerRatioSpectralCap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceTowerGeometricEnvelope
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralMaxVarianceFloor

/-!
# Door-(iv) μ-localization capstone: the worst-frequency mass is the whole open object (#444)

The named door-(iv) free variable is the resonance tower `T r = resonanceMoment u r`. Three pushed
facts localize its ENTIRE open content to the single number `μ := max_k ‖K̂(k)‖²` — the worst
single-frequency Gauss-period kernel mass (the BGK object) — and bracket `μ` itself. This file conjoins
them into ONE axiom-clean citable statement, at a frequency `b₀` that realises the spectral max.

For unit-modulus phases and `m ≥ 2`, with `μ := ‖K̂(b₀)‖²` the realised spectral max:

1. **growth-ratio sandwich** — `m − 1 ≤ T(r+1)/T(r) ≤ μ` for every `r`
   (`resonanceMoment_ratio_sandwich_realised`);
2. **geometric envelope** — `T r ≤ μ^r` for every `r`
   (`resonanceMoment_le_specMaxSq_pow_realised`);
3. **variance floor on μ** — `μ ≥ (m−1) + (T 2 − (m−1)²)/(m−1)`, i.e. `μ` exceeds the Plancherel
   mean by the normalized spectral variance (`specMaxSq_ge_mean_add_normalized_variance`, transported
   to the same realised `b₀`).

Together: the open content of the whole resonance tower is exactly the size of `μ`, pinned BELOW by
`(m−1) + Var/(m−1)` (so `μ = m−1` forces a flat spectrum) and ABOVE by the trivial `(m−1)²`
(per-frequency triangle). The prize `√`-collapse `M(μ_n) ≤ C√(n log m)` lives precisely in that gap:
a bound `μ ≤ C·m·log m` on the one worst frequency propagates by (1)+(2) to the whole tower, and (3)
shows no flat-spectrum shortcut exists. No moment/completion route survives (mapped elsewhere in the
campaign).

## Honest scope (rules 1,3,6)

CERTAIN conjunction of three pushed axiom-clean facts at a single realised `b₀`. `μ` is the realised
spectral max — facts (1),(2) supply it as an upper bound (no magnitude claim), fact (3) is a LOWER
bound on it; NONE bounds `μ` from above (that IS the open prize). Not thinness-essential (rule 3): the
bracket holds in the thick window too. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE /
cancellation / completion / moment-as-proof / anti-concentration / capacity claim. Axiom-clean
(`propext, Classical.choice, Quot.sound`). Issue #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Door-(iv) μ-localization capstone.** For unit phases and `m ≥ 2`, there is a frequency `b₀`
realising the spectral max `μ := ‖K̂(b₀)‖²` such that the whole resonance tower is governed by `μ`:
the growth ratio is sandwiched in `[m−1, μ]`, the tower is dominated by `μ^r`, and `μ` itself is
bounded below by the Plancherel mean plus the normalized spectral variance. The single number `μ`
carries the entire open content of the tower. -/
theorem doorIV_worstFrequency_mu_capstone (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) :
    ∃ b₀ : ZMod m,
      -- μ := ‖K̂(b₀)‖² realises the spectral max (every frequency is dominated by it)
      (∀ k : ZMod m,
          ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2) ∧
      -- (1) growth-ratio sandwich: m−1 ≤ T(r+1)/T(r) ≤ μ
      (∀ r : ℕ, (m : ℝ) - 1 ≤ resonanceMoment u (r + 1) / resonanceMoment u r ∧
          resonanceMoment u (r + 1) / resonanceMoment u r
            ≤ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2) ∧
      -- (2) geometric envelope: T r ≤ μ^r
      (∀ r : ℕ, resonanceMoment u r ≤ (‖kernelSpectrum (dftChar b₀) u‖ ^ 2) ^ r) ∧
      -- (3) variance floor on μ: μ ≥ (m−1) + Var/(m−1)
      ((m : ℝ) - 1 + (resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2) / ((m : ℝ) - 1)
        ≤ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2) := by
  classical
  -- choose b₀ as the spectral-max realiser (Finset.univ nonempty since NeZero m)
  have hne : (Finset.univ : Finset (ZMod m)).Nonempty := by
    have : Nonempty (ZMod m) := ⟨0⟩
    exact Finset.univ_nonempty
  obtain ⟨b₀, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (ZMod m))
      (fun k : ZMod m => ‖kernelSpectrum (dftChar k) u‖ ^ 2) hne
  have hb₀ : ∀ k : ZMod m,
      ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2 :=
    fun k => hmax k (Finset.mem_univ k)
  refine ⟨b₀, hb₀, ?_, ?_, ?_⟩
  · -- (1) sandwich at this realised b₀, for all r
    intro r
    exact resonanceMoment_ratio_sandwich_realised u hu hm r b₀ hb₀
  · -- (2) envelope at this realised b₀, for all r
    intro r
    exact resonanceMoment_le_specMaxSq_pow_realised u hu hm b₀ hb₀ r
  · -- (3) variance floor: the existential max realiser also satisfies the variance lower bound.
    -- Re-derive via specMaxSq_ge_mean_add_normalized_variance and transfer to b₀ (the global max).
    obtain ⟨b₁, hb₁⟩ := specMaxSq_ge_mean_add_normalized_variance u hu hm
    -- ‖K̂(b₁)‖² ≤ ‖K̂(b₀)‖² since b₀ is the global max; chain the lower bound through.
    exact le_trans hb₁ (hb₀ b₁)

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.doorIV_worstFrequency_mu_capstone
