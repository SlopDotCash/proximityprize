/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceTowerRatioSpectralCap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentBaseCaseZero

/-!
# The resonance tower is dominated by a geometric envelope `T r ≤ (max_k ‖K̂(k)‖²)^r` (#444)

The named door-(iv) free variable is the resonance moment `T r = resonanceMoment u r`. The companion
file `_ResonanceTowerRatioSpectralCap` pinned the per-step growth ratio above by the squared spectral
sup-norm: `T(r+1)/T(r) ≤ max_k ‖K̂(k)‖²` (`resonanceMoment_ratio_le_specMaxSq`). The base is pinned
by `_ResonanceMomentBaseCaseZero.resonanceMoment_zero`: `T 0 = 1`.

This file **telescopes** the per-step cap from the pinned base into a closed GLOBAL envelope on the
whole tower:

> **`T r ≤ (max_k ‖K̂(k)‖²)^r`**   (`resonanceMoment_le_specMaxSq_pow`),

i.e. the entire tower is dominated by the geometric sequence whose ratio is the squared spectral
sup-norm `μ := max_k ‖K̂(k)‖²` (supplied as a realised entrywise upper bound).

## Door-(iv) reading: the single worst frequency drives the whole tower

The companion sandwich showed the asymptotic growth rate `lim_r T(r+1)/T(r) = μ`. This envelope is the
*non-asymptotic* form: a bound on the single worst Gauss-period kernel mass `μ = max_k ‖K̂(k)‖²`
propagates UNIFORMLY to every level of the tower, `T r ≤ μ^r`. Concretely the open prize collapse —
`μ ≤ C·m·log m` on the one worst frequency (the BGK object) — would by this envelope give
`T r ≤ (C·m·log m)^r`, the `√`-cancelled `Θ(m^r)`-order regime at every depth, vs the trivial ceiling
`μ ≤ (m−1)²` (per-frequency triangle) giving the trivial `T r ≤ (m−1)^{2r}`. So the entire open content
of the resonance tower's geometric envelope is the single number `μ`, the worst-frequency kernel mass —
exactly the door-(iv) localization. No bound on `μ` is produced here.

## Honest scope (rules 1,3,6 + ASYMPTOTIC GUARD)

CERTAIN exact telescoping of the proven per-step cap from the pinned base `T 0 = 1`. `μ` is supplied as
a *realised* entrywise upper bound on `‖K̂(k)‖²`; we prove NOTHING about its magnitude (that IS the open
object), so this is an UPPER envelope keyed to `μ` and gives no bound on `T r` beyond what `μ` already
encodes — with the trivial `μ ≤ (m−1)²` it recovers exactly the known trivial ceiling, NOT a sub-trivial
collapse. By rule 3 this is not thinness-essential and does not pretend to be; it is the wrong-way
(upper) envelope, the companion of the lower Plancherel floor. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED /
OPEN. No CORE / cancellation / completion / moment / anti-concentration / capacity / beyond-Johnson /
growth-law claim. Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Per-step multiplicative cap** (unit phases, `m ≥ 2`): `T(r+1) ≤ μ · T r` where `μ` is a
realised entrywise upper bound on the squared spectral moduli `‖K̂(k)‖²`. Clears the division in
`resonanceMoment_ratio_le_specMaxSq` against `T r > 0`. -/
theorem resonanceMoment_succ_le_mul (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) (Mcap : ℝ)
    (hMcap : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ Mcap) :
    resonanceMoment u (r + 1) ≤ Mcap * resonanceMoment u r := by
  -- positivity of T r from the proven tower floor
  have hTrpos : 0 < resonanceMoment u r := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hfloor : ((m : ℝ) - 1) ^ r ≤ resonanceMoment u r := resonanceMoment_ge_pow u hu r
    have : (0 : ℝ) < ((m : ℝ) - 1) ^ r := by positivity
    linarith
  -- the ratio cap (companion file), specialized to this Mcap (specWeight = ‖K̂‖²)
  have hratio :
      resonanceMoment u (r + 1) / resonanceMoment u r ≤ Mcap :=
    resonanceMoment_ratio_le_specMaxSq u hu hm r Mcap (fun k => hMcap k)
  rw [div_le_iff₀ hTrpos] at hratio
  linarith [hratio]

/-- **Geometric envelope on the whole resonance tower** (unit phases, `m ≥ 2`):
`T r ≤ μ^r` where `μ = max_k ‖K̂(k)‖²` is a realised entrywise upper bound on the squared spectral
moduli. Telescopes the per-step cap `T(r+1) ≤ μ·T r` from the pinned base `T 0 = 1`. -/
theorem resonanceMoment_le_specMaxSq_pow (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (Mcap : ℝ)
    (hMcap : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ Mcap) (r : ℕ) :
    resonanceMoment u r ≤ Mcap ^ r := by
  -- Mcap ≥ 0 (it dominates a squared norm at any frequency; use k = 0)
  have hMnn : 0 ≤ Mcap := le_trans (by positivity) (hMcap 0)
  induction r with
  | zero => simp [resonanceMoment_zero u]
  | succ n ih =>
    calc resonanceMoment u (n + 1)
        ≤ Mcap * resonanceMoment u n := resonanceMoment_succ_le_mul u hu hm n Mcap hMcap
      _ ≤ Mcap * Mcap ^ n := by exact mul_le_mul_of_nonneg_left ih hMnn
      _ = Mcap ^ (n + 1) := by rw [pow_succ]; ring

/-- **Realised form**: with `b₀` attaining the spectral max, the envelope reads
`T r ≤ (‖K̂(b₀)‖²)^r`, exhibiting the worst single-frequency Gauss-period kernel mass as the geometric
ratio dominating every level of the tower. -/
theorem resonanceMoment_le_specMaxSq_pow_realised (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (b₀ : ZMod m)
    (hb₀ : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2)
    (r : ℕ) :
    resonanceMoment u r ≤ (‖kernelSpectrum (dftChar b₀) u‖ ^ 2) ^ r :=
  resonanceMoment_le_specMaxSq_pow u hu hm (‖kernelSpectrum (dftChar b₀) u‖ ^ 2) (fun k => hb₀ k) r

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_succ_le_mul
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_le_specMaxSq_pow
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_le_specMaxSq_pow_realised
