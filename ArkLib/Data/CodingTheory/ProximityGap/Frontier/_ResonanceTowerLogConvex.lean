/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceParsevalBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceTowerFloor

/-!
# Log-convexity of the resonance tower (#407 / #444)

The named `√p`-free free variable of door-(iv) is the resonance moment
`T r = resonanceMoment u r = (1/m) ∑_k ‖K̂(k)‖^{2r}`, the `2r`-th spectral power-mean of the
one-step Gauss-period kernel spectrum `K̂(k) = kernelSpectrum (dftChar k) u` (the Parseval bridge
`resonanceMoment_eq_spectral_powerMean`). This file lands the **shape** constraint that the whole
tower `r ↦ T r` must obey, derived directly from that bridge by a single Cauchy–Schwarz on the
spectral measure:

> **`(T (r+1))² ≤ (T r) · (T (r+2))`** (`resonanceMoment_sq_le_mul_succ_succ`),

i.e. the tower is **log-convex** in `r`. Equivalently the spectral `ℓ^{2r}`-power sums
`P r = ∑_k ‖K̂(k)‖^{2r}` satisfy `P(r+1)² ≤ P r · P(r+2)` — the standard Lyapunov / power-mean
interpolation inequality for the moments of the nonnegative spectral measure `‖K̂(·)‖²`.

Its immediate corollary is the **monotonicity of the tower growth ratio**, stated directly on the
named free variable (the abstract ratio ladder `PowerSumRatioMonotone.powerSum_ratio_monotone` was
never connected to `resonanceMoment`):

> **`T(r+1)/T(r) ≤ T(r+2)/T(r+1)`** (`resonanceMoment_ratio_monotone`, unit phases, `m ≥ 2`).

With the proven Chebyshev floor `(m−1) ≤ T(r+1)/T(r)` (`_ResonanceChebyshevLower`) and the trivial
per-level ceiling, the door-(iv) growth ratio is squeezed into a **monotone sequence bounded below by
`m−1`** — so the prize `√`-cancellation (if real) is a SINGLE monotone geometric rate of the whole
tower, not a depth-localized dip. This is the citable door-(iv) growth-rate constraint at the level
of the actual prize object.

## Why this is a genuinely new structural lever (not a spectral-cap brick, not a moment route)

The campaign already has the per-level Chebyshev *monotonicity from below* `(m−1)·T r ≤ T (r+1)`
(`_ResonanceChebyshevLower`) and the trivial ceiling `T r ≤ (m−1)^{2r}/m·m`. Those bound a single
level. Log-convexity is different in kind: it is a **two-step shape constraint linking three
consecutive levels** of the named free variable, with NO appeal to a moment/energy expansion and NO
spectral cap on any individual `‖K̂(k)‖`. It is the Lyapunov inequality of the spectral measure,
which is exactly the Cauchy–Schwarz `(∑ a·b)² ≤ (∑ a²)(∑ b²)` with `a = ‖K̂‖^r`, `b = ‖K̂‖^{r+2}`
(so `a·b = ‖K̂‖^{2(r+1)}`).

## Door-(iv) reading: log-convexity is the WRONG-WAY constraint for the prize

The prize needs `T r` to *collapse* to the `√`-cancelled `Θ(m^r)` regime away from the trivial
`Θ(m^{2r-1})` ceiling. Log-convexity says the tower can never dip in the "interior" relative to its
endpoints: a measure whose low moments are large (`T 1 = m−1` is forced, the Plancherel floor) and
which is log-convex CANNOT have anomalously small middle moments without its high moments paying for
it. Concretely, log-convexity + the forced floor `T 1 = m−1` gives, by the standard chaining
`T r ≥ (T 1)^? `… — but in the OTHER direction: it shows the `√`-cancellation, if it exists, must be
a *uniform geometric decay rate* of the whole tower, not a localized dip. This **localizes the open
content**: a prize bound is equivalent to controlling the log-convex tower's geometric ratio
`T(r+1)/T(r)`, which the bridge identifies with the spectral measure's `(2r+2)/(2r)`-power-mean
ratio — and THAT ratio is governed by the `‖K̂(k)‖` profile at `k ≠ 0` (the open Gauss-period/BGK
object), not by any quantity already bounded. No new bound on `K̂` is produced.

## Honest scope

CERTAIN exact consequence of the Parseval bridge + Cauchy–Schwarz (Lyapunov). It is a constraint
on the SHAPE of the tower, NOT a bound on any `‖K̂(k)‖`, hence NOT a bound on `T r` itself beyond
what the endpoints already give. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE /
cancellation / completion / moment / anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- Abbreviation for the one-step kernel spectral modulus at frequency `k`. -/
private noncomputable def specMod (u : ZMod m → ℂ) (k : ZMod m) : ℝ :=
  ‖kernelSpectrum (dftChar k) u‖

private theorem specMod_nonneg (u : ZMod m → ℂ) (k : ZMod m) : 0 ≤ specMod u k :=
  norm_nonneg _

/-- **Spectral power-sum Cauchy–Schwarz (Lyapunov three-term log-convexity).**
For the nonnegative spectral moduli, the `(r+1)`-power sum squared is dominated by the product of
the `r`- and `(r+2)`-power sums:
`(∑_k ‖K̂(k)‖^{2(r+1)})² ≤ (∑_k ‖K̂(k)‖^{2r}) · (∑_k ‖K̂(k)‖^{2(r+2)})`.
This is `Finset.sum_mul_sq_le_sq_mul_sq` with `f k = ‖K̂(k)‖^r`, `g k = ‖K̂(k)‖^{r+2}`. -/
theorem spectral_powerSum_sq_le_mul (u : ZMod m → ℂ) (r : ℕ) :
    (∑ k : ZMod m, specMod u k ^ (2 * (r + 1))) ^ 2
      ≤ (∑ k : ZMod m, specMod u k ^ (2 * r)) *
        (∑ k : ZMod m, specMod u k ^ (2 * (r + 2))) := by
  classical
  have hCS :
      (∑ k : ZMod m, specMod u k ^ r * specMod u k ^ (r + 2)) ^ 2
        ≤ (∑ k : ZMod m, (specMod u k ^ r) ^ 2) *
          (∑ k : ZMod m, (specMod u k ^ (r + 2)) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k => specMod u k ^ r) (fun k => specMod u k ^ (r + 2))
  -- rewrite the three exponent identities:
  --   x^r * x^(r+2) = x^(2(r+1)),  (x^r)^2 = x^(2r),  (x^(r+2))^2 = x^(2(r+2))
  have e1 : ∀ k : ZMod m,
      specMod u k ^ r * specMod u k ^ (r + 2) = specMod u k ^ (2 * (r + 1)) := by
    intro k; rw [← pow_add]; congr 1; ring
  have e2 : ∀ k : ZMod m,
      (specMod u k ^ r) ^ 2 = specMod u k ^ (2 * r) := by
    intro k; rw [← pow_mul]; congr 1; ring
  have e3 : ∀ k : ZMod m,
      (specMod u k ^ (r + 2)) ^ 2 = specMod u k ^ (2 * (r + 2)) := by
    intro k; rw [← pow_mul]; congr 1; ring
  simp only [e1] at hCS
  simp only [e2, e3] at hCS
  exact hCS

/-- **Log-convexity of the resonance tower.**
`(T (r+1))² ≤ (T r) · (T (r+2))`: the named door-(iv) free variable `T r = resonanceMoment u r`
is log-convex in `r`. Proven by transporting the spectral power-sum Cauchy–Schwarz
(`spectral_powerSum_sq_le_mul`) through the Parseval bridge `m·T r = ∑_k ‖K̂(k)‖^{2r}`. -/
theorem resonanceMoment_sq_le_mul_succ_succ (u : ZMod m → ℂ) (r : ℕ) :
    (resonanceMoment u (r + 1)) ^ 2
      ≤ (resonanceMoment u r) * (resonanceMoment u (r + 2)) := by
  classical
  have hmpos : (0 : ℝ) < m := by
    have := (NeZero.ne (m : ℕ)); positivity
  -- bridge at the three levels (as plain `(m:ℝ)*T = ∑ ‖K̂‖^{2·}`)
  have bR : (m : ℝ) * resonanceMoment u r
      = ∑ k : ZMod m, specMod u k ^ (2 * r) := by
    simpa [specMod] using resonanceMoment_eq_spectral_powerMean u r
  have b1 : (m : ℝ) * resonanceMoment u (r + 1)
      = ∑ k : ZMod m, specMod u k ^ (2 * (r + 1)) := by
    simpa [specMod] using resonanceMoment_eq_spectral_powerMean u (r + 1)
  have b2 : (m : ℝ) * resonanceMoment u (r + 2)
      = ∑ k : ZMod m, specMod u k ^ (2 * (r + 2)) := by
    simpa [specMod] using resonanceMoment_eq_spectral_powerMean u (r + 2)
  -- scale the spectral CS by 1: multiply both sides of `T(r+1)² ≤ T r · T(r+2)` by m²>0.
  have key :
      ((m : ℝ) * resonanceMoment u (r + 1)) ^ 2
        ≤ ((m : ℝ) * resonanceMoment u r) * ((m : ℝ) * resonanceMoment u (r + 2)) := by
    rw [b1, bR, b2]
    exact spectral_powerSum_sq_le_mul u r
  -- divide out m² > 0
  have hmsq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hrw :
      ((m : ℝ) * resonanceMoment u (r + 1)) ^ 2
        = (m : ℝ) ^ 2 * (resonanceMoment u (r + 1)) ^ 2 := by ring
  have hrw2 :
      ((m : ℝ) * resonanceMoment u r) * ((m : ℝ) * resonanceMoment u (r + 2))
        = (m : ℝ) ^ 2 * ((resonanceMoment u r) * (resonanceMoment u (r + 2))) := by ring
  rw [hrw, hrw2] at key
  exact le_of_mul_le_mul_left key hmsq

/-- Strict positivity of the resonance moment for unit phases when `m ≥ 2`, via the proven tower
floor `(m−1)^r ≤ T r` (`resonanceMoment_ge_pow`). -/
private theorem resonanceMoment_pos (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) : 0 < resonanceMoment u r := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hfloor : ((m : ℝ) - 1) ^ r ≤ resonanceMoment u r := resonanceMoment_ge_pow u hu r
  have : (0 : ℝ) < ((m : ℝ) - 1) ^ r := by positivity
  linarith

/-- **Monotonicity of the resonance tower growth ratio** (unit phases, `m ≥ 2`).
`T(r+1)/T(r) ≤ T(r+2)/T(r+1)`: the named door-(iv) free variable's consecutive growth ratio is
monotone non-decreasing in `r` — the direct corollary of log-convexity, stated at the level of the
actual prize object. Transports `PowerSumRatioMonotone.powerSum_ratio_monotone` (on the spectral
moduli `‖K̂(k)‖`) through the Parseval bridge, then clears the common `m` factor. -/
theorem resonanceMoment_ratio_monotone (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) :
    resonanceMoment u (r + 1) / resonanceMoment u r
      ≤ resonanceMoment u (r + 2) / resonanceMoment u (r + 1) := by
  classical
  -- log-convexity (already proven) gives the cross-multiplied inequality directly
  have hlc := resonanceMoment_sq_le_mul_succ_succ u r
  have hT0 : 0 < resonanceMoment u r := resonanceMoment_pos u hu hm r
  have hT1 : 0 < resonanceMoment u (r + 1) := resonanceMoment_pos u hu hm (r + 1)
  rw [div_le_div_iff₀ hT0 hT1]
  -- goal: T(r+1) * T(r+1) ≤ T(r+2) * T r, exactly log-convexity reassociated
  nlinarith [hlc]

/-- **Parseval-floor lower bound for every resonance growth ratio.**
For unit phases and `m ≥ 2`, every consecutive ratio of the named door-(iv) tower is at least the
forced spectral mean `m−1`:
`(m−1) ≤ T(r+1)/T(r)`.  This is the Chebyshev lower step with the positive denominator cleared.
Together with `resonanceMoment_ratio_monotone`, it says the whole ratio ladder is monotone and never
has a below-Parseval interior dip; any prize-saving input must lower the global geometric scale, not
manufacture a local cheap rung. -/
theorem resonanceMoment_ratio_floor (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) :
    ((m : ℝ) - 1) ≤ resonanceMoment u (r + 1) / resonanceMoment u r := by
  have hT : 0 < resonanceMoment u r := resonanceMoment_pos u hu hm r
  have hstep : ((m : ℝ) - 1) * resonanceMoment u r ≤ resonanceMoment u (r + 1) :=
    resonanceMoment_succ_ge u hu r
  rw [le_div_iff₀ hT]
  simpa [mul_comm] using hstep

/-- **No below-floor ratio dip.**
A direct constraint form of `resonanceMoment_ratio_floor`: no unit-phase resonance tower in the
`m ≥ 2` door-(iv) regime can have a consecutive growth ratio strictly below the Parseval floor `m−1`.
This is a refuted-lever guard against any proposed proof that relies on an anomalously cheap local
moment rung. -/
theorem not_resonanceMoment_ratio_lt_floor (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) :
    ¬ resonanceMoment u (r + 1) / resonanceMoment u r < ((m : ℝ) - 1) := by
  exact not_lt_of_ge (resonanceMoment_ratio_floor u hu hm r)

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.spectral_powerSum_sq_le_mul
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_sq_le_mul_succ_succ
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_monotone
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_floor
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.not_resonanceMoment_ratio_lt_floor
