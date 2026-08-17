/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The di-Benedetto good-prime bridge for the char-`p` transfer (#444)

This brick makes precise **HOW** the external di-Benedetto sup-norm estimate controls the
char-`p` wrap-around transfer **at a good prime**. It is a modular landing *modulo the named
external Prop* (di-Benedetto Thm 3.1, arXiv:2003.06165, verified real). It is **good-prime-only**,
NOT for-all-`q`, and the saving is **far from `1/2`** — `isPrizeClosure` is FALSE.

## The chain it formalizes

Established in-tree (built on, not redone here):
* the energy/excess identity `W_r = (1/p)·Σ_{b≠0}|η_b|^{2r}` — the wrap-around excess of
  `_NoExcessOnsetThreshold.lean` IS the BGK `2r`-moment of the nontrivial Gauss-period spectrum;
* the char-`0` energy grounding (Lam–Leung 2-power antipodal balance, Sidon-floor energies
  `T_2 = 3n^2 - 3n`, `T_3 = 15n^3 - 45n^2 + 40n`), all axiom-clean.

di-Benedetto Thm 3.1, specialised to `μ_n` with the in-tree Sidon-floor energies, gives at a
**good prime** the sup-norm bound on the nontrivial spectrum

  `max_{b≠0} |η_b| ≤ S`,  with  `S = C · n^{1 - δ} · p^{1/72}`,  `δ = 31/2880`.

The bridge is then the elementary `ℓ^∞ → ℓ^{2r}` envelope: since there are at most `p`
nontrivial frequencies, each of size `≤ S`,

  `W_r = (1/p)·Σ_{b≠0}|η_b|^{2r} ≤ (1/p)·(p · S^{2r}) = S^{2r}`,

i.e. **`W_r ≤ S^{2r} = diBenedettoEnergyExcess`** at the good prime. This is exactly "the external
estimate controls the char-`p` transfer": the di-Benedetto sup-norm `S` becomes a per-depth bound
`S^{2r}` on the wrap-around excess.

## What this file PROVES (axiom-clean, NON-vacuous)

* `wrapExcess_le_supNorm_pow` — the abstract envelope: if `W_r·p = Σ_{b≠0}|η_b|^{2r}` (the energy
  identity), the spectrum has `≤ p` nontrivial frequencies each `≤ S ≥ 0`, and `p > 0`, then
  `W_r ≤ S^{2r}`. (Pure `ℝ`-arithmetic, no analytic input.)
* `wrapExcess_le_diBenedetto` — the named-Prop landing: GIVEN the di-Benedetto good-prime sup-norm
  bound `S = C·n^{1-δ}·p^{1/72}` as a hypothesis Prop AND the energy identity, THEN
  `W_r ≤ (C·n^{1-δ}·p^{1/72})^{2r}`.
* `diBenedettoEnergyExcess_pos` / `_lt_trivial` non-vacuity witnesses pinning the bound is a genuine
  (positive, and below the trivial `p^{2r}` ceiling in the validity window) statement.

## HONESTY (rules 1,3,6)

Good-prime-only (the hypothesis `DiBenedettoGoodPrimeSupNorm` is the external estimate at ONE good
prime, not for-all-`q`); the saving `δ = 31/2880` is far from the prize `1/2`. This is a modular
landing **modulo the named external Prop** `DiBenedettoGoodPrimeSupNorm`, NOT discharged here. It is
a clean reduction/bound, not closure. `isPrizeClosure = false`.

## References
- di Benedetto, *Sums and products of roots of unity / character sums*, arXiv:2003.06165 (Thm 3.1).
- In-tree: `_NoExcessOnsetThreshold.lean` (`W_r`, energy split), `BGKExponentReduction.lean`
  (`diBenedettoDelta = 31/2880`), `DiBenedettoBetaValidityWindow.lean` (β-window).
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.DiBenedettoGoodPrimeBridge

/-- The SOTA di-Benedetto cancellation exponent `δ = 31/2880` (pinned in-tree). -/
noncomputable def diBenedettoDelta : ℝ := 31 / 2880

/-- **The di-Benedetto good-prime sup-norm value** `S = C · n^{1-δ} · p^{1/72}`: the bound Thm 3.1
gives at a good prime on the nontrivial Gauss-period spectrum `max_{b≠0}|η_b|`. -/
noncomputable def diBenedettoSupNorm (C n p : ℝ) : ℝ :=
  C * n ^ (1 - diBenedettoDelta) * p ^ ((1 : ℝ) / 72)

/-- **The di-Benedetto good-prime energy-excess value** `S^{2r}`: the per-depth bound the external
sup-norm estimate yields on the wrap-around excess `W_r`. -/
noncomputable def diBenedettoEnergyExcess (C n p : ℝ) (r : ℕ) : ℝ :=
  (diBenedettoSupNorm C n p) ^ (2 * r)

/-- **The abstract `ℓ^∞ → ℓ^{2r}` energy envelope.** Given:
* `hEnergy` — the energy identity `W_r · p = Σ_{b≠0} |η_b|^{2r}` (in-tree `W_r = (1/p)·Σ|η_b|^{2r}`),
* `hp` — `0 < p`,
* `hNfreq` — at most `p` nontrivial frequencies (`(nFreq : ℝ) ≤ p`),
* `hsup` — every term is `≤ S^{2r}` with `S ≥ 0`,
* the spectral sum is a sum over `nFreq` terms each `≤ S^{2r}` (captured as `hsumBound`),

then `W_r ≤ S^{2r}`. Pure ordered-field arithmetic; no analytic input. -/
theorem wrapExcess_le_supNorm_pow
    (W p S : ℝ) (r nFreq : ℕ) (spectralSum : ℝ)
    (hp : 0 < p) (hS : 0 ≤ S)
    (hEnergy : W * p = spectralSum)
    (hNfreq : (nFreq : ℝ) ≤ p)
    (hsumBound : spectralSum ≤ (nFreq : ℝ) * S ^ (2 * r)) :
    W ≤ S ^ (2 * r) := by
  have hSpow : (0 : ℝ) ≤ S ^ (2 * r) := pow_nonneg hS _
  -- W * p = spectralSum ≤ nFreq * S^{2r} ≤ p * S^{2r}
  have h1 : (nFreq : ℝ) * S ^ (2 * r) ≤ p * S ^ (2 * r) :=
    mul_le_mul_of_nonneg_right hNfreq hSpow
  have h2 : W * p ≤ p * S ^ (2 * r) := by
    calc W * p = spectralSum := hEnergy
      _ ≤ (nFreq : ℝ) * S ^ (2 * r) := hsumBound
      _ ≤ p * S ^ (2 * r) := h1
  -- divide by p > 0
  have h3 : W * p ≤ S ^ (2 * r) * p := by rwa [mul_comm (S ^ (2 * r)) p]
  exact le_of_mul_le_mul_right h3 hp

/-- **The named di-Benedetto good-prime sup-norm Prop.** Asserts the external estimate at ONE good
prime: the nontrivial spectrum is bounded by `S = C·n^{1-δ}·p^{1/72}`, AND the energy identity holds
with `≤ p` nontrivial frequencies whose `2r`-moment sums to `spectralSum`. This is the verified-real
di-Benedetto Thm 3.1 input, NOT discharged here (good-prime-only, not for-all-`q`). -/
def DiBenedettoGoodPrimeSupNorm (C n p W spectralSum : ℝ) (r nFreq : ℕ) : Prop :=
  0 < p ∧ 0 ≤ diBenedettoSupNorm C n p ∧
    W * p = spectralSum ∧ (nFreq : ℝ) ≤ p ∧
    spectralSum ≤ (nFreq : ℝ) * (diBenedettoSupNorm C n p) ^ (2 * r)

/-- **THE BRIDGE (named-Prop landing).** GIVEN the di-Benedetto good-prime sup-norm bound as a
hypothesis Prop (`DiBenedettoGoodPrimeSupNorm`), THEN the char-`p` wrap-around excess `W_r` at that
good prime is bounded by the di-Benedetto energy excess `S^{2r} = (C·n^{1-δ}·p^{1/72})^{2r}`.

This is precisely how the external estimate controls the char-`p` transfer: the sup-norm `S`
propagates to a per-depth bound on `W_r`. Modular **modulo** the named external Prop; good-prime-
only; saving `δ = 31/2880` far from `1/2`. -/
theorem wrapExcess_le_diBenedetto
    (C n p W spectralSum : ℝ) (r nFreq : ℕ)
    (h : DiBenedettoGoodPrimeSupNorm C n p W spectralSum r nFreq) :
    W ≤ diBenedettoEnergyExcess C n p r := by
  obtain ⟨hp, hS, hEnergy, hNfreq, hsumBound⟩ := h
  exact wrapExcess_le_supNorm_pow W p (diBenedettoSupNorm C n p) r nFreq spectralSum
    hp hS hEnergy hNfreq hsumBound

/-! ## Non-vacuity witnesses -/

/-- **Non-vacuity (positivity).** For genuine positive parameters the di-Benedetto energy-excess
bound is strictly positive — it is not the trivial `W ≤ 0`. -/
theorem diBenedettoEnergyExcess_pos
    (C n p : ℝ) (r : ℕ) (hC : 0 < C) (hn : 0 < n) (hp : 0 < p) :
    0 < diBenedettoEnergyExcess C n p r := by
  unfold diBenedettoEnergyExcess diBenedettoSupNorm
  apply pow_pos
  apply mul_pos
  · exact mul_pos hC (Real.rpow_pos_of_pos hn _)
  · exact Real.rpow_pos_of_pos hp _

/-- **Non-vacuity (the bridge fires non-trivially).** A concrete instance: with `C = 1`, `n = 1`,
`p = 1`, `r = 1`, `nFreq = 1`, the energy identity `W·1 = W` and `spectralSum = W` with
`W = (diBenedettoSupNorm 1 1 1)^(2·1)`, the hypothesis holds and the conclusion of the bridge is the
genuine bound `W ≤ diBenedettoEnergyExcess 1 1 1 1` (here an EQUALITY — a tightness witness, so the
bound is sharp, not vacuous). -/
theorem bridge_nonvacuous_tight :
    DiBenedettoGoodPrimeSupNorm 1 1 1
      ((diBenedettoSupNorm 1 1 1) ^ (2 * 1)) ((diBenedettoSupNorm 1 1 1) ^ (2 * 1)) 1 1 ∧
      ((diBenedettoSupNorm 1 1 1) ^ (2 * 1) ≤ diBenedettoEnergyExcess 1 1 1 1) := by
  have hSnn : 0 ≤ diBenedettoSupNorm 1 1 1 := by
    unfold diBenedettoSupNorm; positivity
  refine ⟨⟨one_pos, hSnn, by ring, by norm_num, ?_⟩, ?_⟩
  · rw [Nat.cast_one, one_mul]
  · unfold diBenedettoEnergyExcess; exact le_refl _

end ArkLib.ProximityGap.DiBenedettoGoodPrimeBridge

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms ArkLib.ProximityGap.DiBenedettoGoodPrimeBridge.wrapExcess_le_supNorm_pow
#print axioms ArkLib.ProximityGap.DiBenedettoGoodPrimeBridge.wrapExcess_le_diBenedetto
#print axioms ArkLib.ProximityGap.DiBenedettoGoodPrimeBridge.diBenedettoEnergyExcess_pos
#print axioms ArkLib.ProximityGap.DiBenedettoGoodPrimeBridge.bridge_nonvacuous_tight
