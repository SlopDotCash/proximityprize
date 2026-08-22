/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralVariance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBSpikeMomentBound

/-!
# A worst-frequency spike costs spectral variance (#407 / #444, door-(iv) Lane-3 constraint)

This file INSTANTIATES the abstract one-sided-Chebyshev (Cantelli) spike obstruction
(`_DoorIVWorstBSpikeMomentBound.sndMoment_ge_sq_of_exists_threshold`) on the now-pinned spectral
profile `{w_k = ‖kernelSpectrum (dftChar k) u‖²}_k` of the one-step Gauss-period kernel, at the
proven spectral mean `μ = m − 1`.

The key substitution is that the centered second moment of the kernel profile is EXACTLY the
landed spectral variance identity:

  `∑_k (w_k − (m−1))² = m·(T 2 − (m−1)²)`   (`_ResonanceSpectralVariance.sum_sq_centered_kernelSpectrum_eq`).

So a worst-frequency spike `w_{k*} ≥ (m−1) + d` (the structure a door-(iv) attack must produce, since
`max_k w_k` is the object in CORE) forces, via Cantelli, the centered second moment `≥ d²`, hence:

> **`d² ≤ m·(T 2 − (m−1)²)`**, i.e. the spectral variance `T 2 − (m−1)² ≥ d²/m`.

## Why this is a Lane-3 constraint (not progress on CORE)

It is the precise quantitative form, ON THE ACTUAL KERNEL, of why the moment route is dead: any single
worst-frequency spike of height `d` above the mean is **paid for** by a full `d²` unit of the second
moment / spectral variance, which is itself a moment object (= the BGK wall). The constraint runs the
WRONG way for the prize: it lower-bounds the variance from a given spike, it does NOT upper-bound the
spike from a bounded variance. A large spike is fully consistent with the bound (it just demands
proportionally large variance, which the deep-`r` moments are free to supply). So bounding the
spectral profile's moments cannot cap `max_k w_k`; the cap must come from the open arithmetic
(non-moment) evaluation of the Gauss-period sum. This pins the b-side single-spike route as
variance/moment-equivalent on the kernel object, kernel-checked.

## Honest scope

CERTAIN inequality (Cantelli instantiation + the proven variance identity). No CORE / cancellation /
completion / moment-as-prize / anti-concentration / capacity claim; bounding `T 2 − (m−1)²` does NOT
bound `max_b |K̂(b)|`. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **A worst-frequency spike of height `d` above the spectral mean costs `d²` of centered second
moment**, expressed through the proven spectral-variance identity: if some frequency `k*` has
`‖K̂(k*)‖² ≥ (m−1) + d` with `d > 0`, then

  `d² ≤ m·(T 2 − (m−1)²)`.

Cantelli (`sndMoment_ge_sq_of_exists_threshold`) on `x = w`, `s = univ`, `μ = m−1`, with the centered
second moment rewritten by `sum_sq_centered_kernelSpectrum_eq`. The variance therefore lower-bounds
the achievable spike — a Lane-3 constraint that runs the WRONG way for the prize (it does not cap the
spike from a bounded variance). -/
theorem spike_cost_le_variance
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (d : ℝ) (hd : 0 < d)
    (hspike : ∃ k : ZMod m, ((m : ℝ) - 1) + d ≤ ‖kernelSpectrum (dftChar k) u‖ ^ 2) :
    d ^ 2 ≤ (m : ℝ) * (resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2) := by
  classical
  -- instantiate Cantelli on the kernel profile at mean μ = m-1
  have hex : ∃ k ∈ (Finset.univ : Finset (ZMod m)),
      ((m : ℝ) - 1) + d ≤ (fun k => ‖kernelSpectrum (dftChar k) u‖ ^ 2) k := by
    obtain ⟨k, hk⟩ := hspike
    exact ⟨k, Finset.mem_univ k, hk⟩
  have hcantelli :=
    ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.sndMoment_ge_sq_of_exists_threshold
      (fun k => ‖kernelSpectrum (dftChar k) u‖ ^ 2) (Finset.univ : Finset (ZMod m))
      ((m : ℝ) - 1) d hd hex
  -- the centered second moment is the proven spectral variance: ∑(w-(m-1))² = m·(T2-(m-1)²)
  have hvar := sum_sq_centered_kernelSpectrum_eq u hu
  -- hcantelli : d² ≤ ∑_{univ} (w k - (m-1))²; hvar rewrites that sum
  rw [hvar] at hcantelli
  exact hcantelli

/-- **Spectral-variance form of the spike cost: `d²/m ≤ T 2 − (m−1)²`** (unit-modulus phases). A
worst-frequency spike of height `d` above the mean forces the spectral variance `T 2 − (m−1)²` to be
at least `d²/m`. The clean per-frequency statement: the variance budget required by a spike of height
`d` is `d²/m`. Still the wrong direction for the prize (lower-bounds variance from a spike). -/
theorem variance_ge_spike_sq_div
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (d : ℝ) (hd : 0 < d)
    (hspike : ∃ k : ZMod m, ((m : ℝ) - 1) + d ≤ ‖kernelSpectrum (dftChar k) u‖ ^ 2) :
    d ^ 2 / (m : ℝ) ≤ resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  rw [div_le_iff₀ hmpos]
  -- d² ≤ (T2 - (m-1)²)·m  ⟺  d² ≤ m·(T2 - (m-1)²)
  have h := spike_cost_le_variance u hu d hd hspike
  linarith [h]

/-- **Multiplicity cap: at most `m·(T 2 − (m−1)²)/d²` frequencies can spike to height `d` above the
mean** (unit-modulus phases). The COUNT form of the spike obstruction, instantiating the abstract
Cantelli count bound (`threshold_count_le_sndMoment_div`) on the kernel profile at `μ = m−1` and
substituting the proven spectral-variance identity for the centered second moment:

  `#{k : ((m−1)+d) ≤ ‖K̂(k)‖²} ≤ m·(T 2 − (m−1)²)/d²`.

The number of near-worst frequencies is capped by the spectral variance over `d²`. Like the existence
form, this runs the WRONG way for the prize: a *small* count is *explained by* a small variance, it
does not bound the worst value. Any selector/count argument for the worst frequency therefore
consumes spectral-variance (= moment / BGK) budget. -/
theorem spike_count_le_variance_div
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (d : ℝ) (hd : 0 < d) :
    (((Finset.univ : Finset (ZMod m)).filter
        (fun k => ((m : ℝ) - 1) + d ≤ ‖kernelSpectrum (dftChar k) u‖ ^ 2)).card : ℝ)
      ≤ (m : ℝ) * (resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2) / d ^ 2 := by
  classical
  have hcount :=
    ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.threshold_count_le_sndMoment_div
      (fun k => ‖kernelSpectrum (dftChar k) u‖ ^ 2) (Finset.univ : Finset (ZMod m))
      ((m : ℝ) - 1) d hd
  -- rewrite the centered second moment as the proven spectral variance m·(T2-(m-1)²)
  rwa [sum_sq_centered_kernelSpectrum_eq u hu] at hcount

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.spike_cost_le_variance
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.variance_ge_spike_sq_div
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.spike_count_le_variance_div
