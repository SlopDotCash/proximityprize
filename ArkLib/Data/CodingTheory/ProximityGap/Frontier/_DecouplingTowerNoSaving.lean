/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The ℓ²-decoupling octave telescope is SAVING-NEUTRAL for the L^∞ period (#407 / #444)

## The hybrid under test (exotic domain: decoupling × antipodal-tower self-similarity)

The antipodal split of the Gauss period over the 2-power tower `μ_{2^μ} = H ⊔ h·H`
(`H = μ_{2^{μ-1}}`) gives the EXACT one-octave decomposition
`η_b^{G} = η_b^{H} + η_{bh}^{H}` (two sub-periods over the half-group; reconstruction is exact,
probe `rec_err ~1e-15`, the in-tree `comp (X^{2^s})` identity `_DyadicTowerDescent`).

An **ℓ²-decoupling / multiscale-wavelet** attack hopes to bound the L^∞ object
`M(G)² = max_b |η_b^G|²` by the per-octave decoupling
`|η_b^G|² ≤ Δ · (|η_b^H|² + |η_{bh}^H|²)` and telescope `s = μ` octaves to
`M(G)² ≤ Δ^μ · base`. For this to beat the trivial `√n` scale (and reach the prize
`M ≤ C√(n log p)`) one needs a per-octave constant `Δ < 2` — a genuine *decoupling gain*.

## The refutation-with-mechanism (this file = the telescope arithmetic; probes = the constant)

The decoupling constant is `Δ = 2` exactly at the worst frequency `b`, because the two octave
sub-periods are **constructively aligned** there (probe: `cos(angle) = 1.0000` at the
maximizer, `|η_b^H| ≈ |η_{bh}^H|` ⟹ Cauchy–Schwarz tight `Δ = 2`). With `Δ = 2` the telescope
collapses to the trivial scale:

> `M(G)² ≤ 2^μ · base = n · base`  ⟹  `M(G) ≤ √n · √base`,

the geometric-mean / Johnson / L²-average scale — **no √(log p) prize factor**. This is the
ℓ²-decoupling form of the C27 (Hasse–Davenport telescope) obstruction: any symmetric per-octave
operation is blind to *which* conjugate is the sup; the worst `b` aligns the octave halves so the
multiscale induction never destroys mass. The √(log p) prize factor lives in the archimedean phase
spread across the `m = (p-1)/n` conjugates (the BGK/Paley open core), which a per-octave decoupling
cannot manufacture.

This file lands the **abstract telescope arithmetic** (char-free, prime-free): a per-octave
decoupling step with constant `Δ ≥ 2` telescopes to `≥ 2^μ`, i.e. the trivial scale, while a
genuine sub-trivial bound requires `Δ < 2` at *every* octave (a uniform decoupling gain), which the
worst-frequency alignment denies. It is the decoupling sibling of
`_TowerDescentNoSaving.towerDescent_saving_iff`.

## Honest scope (rules 1, 3, 4, 6 — NOT a CORE closure)

A **refutation-with-mechanism**: it walls the ℓ²-decoupling / multiscale hope by proving the
telescope is saving-neutral *when the per-octave constant is 2* (the measured value), and pins that
a closure would need `Δ < 2` uniformly = systematic destructive interference at the worst `b`, which
the probe (`cos = 1`) refutes. It does NOT close CORE; `M(μ_n) ≤ C√(n·log(p/n))` stays OPEN, blocked
on the archimedean conjugate-spread (BGK/Paley) the decoupling cannot supply.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issues #407, #444.
-/

namespace ProximityGap.Frontier.DecouplingTowerNoSaving

/-- **One ℓ²-decoupling octave with constant `Δ` is a single multiplicative step.** If
`Mᵤ² ≤ Δ · Mᵤ₋₁²` (the per-octave decoupling bound, `Mⱼ²` the level-`j` worst-case squared
period), then iterating it `μ` times gives `M² ≤ Δ^μ · base`. Stated as the telescope of a
geometric per-step factor over the tower. -/
theorem telescope_geom (Δ base : ℝ) (M : ℕ → ℝ) (hΔ : 0 ≤ Δ) (h0 : M 0 ≤ base)
    (hstep : ∀ j, M (j + 1) ≤ Δ * M j) (hMnn : ∀ j, 0 ≤ M j) (μ : ℕ) :
    M μ ≤ Δ ^ μ * base := by
  induction μ with
  | zero => simpa using h0
  | succ k ih =>
      calc M (k + 1) ≤ Δ * M k := hstep k
        _ ≤ Δ * (Δ ^ k * base) := by
              exact mul_le_mul_of_nonneg_left ih hΔ
        _ = Δ ^ (k + 1) * base := by ring

/-- **The measured-constant collapse (`Δ = 2`): the telescope lands at the trivial `2^μ` scale.**
With the worst-frequency octave constant `Δ = 2` (Cauchy–Schwarz tight, octave halves aligned), the
μ-fold telescope gives `M² ≤ 2^μ · base = n · base` (`n = 2^μ`). After the square root this is
`M ≤ √n · √base` — the geometric-mean / Johnson scale, with NO √(log p) prize factor. -/
theorem telescope_trivial_at_two (base : ℝ) (M : ℕ → ℝ) (h0 : M 0 ≤ base)
    (hstep : ∀ j, M (j + 1) ≤ 2 * M j) (hMnn : ∀ j, 0 ≤ M j) (μ : ℕ) :
    M μ ≤ (2 : ℝ) ^ μ * base :=
  telescope_geom 2 base M (by norm_num) h0 hstep hMnn μ

/-- **The decoupling gain a closure would require (the exact threshold).** To beat the trivial
`2^μ = n` scale by a factor `2^μ / T` (so that `M² ≤ T · base` with `T < 2^μ`, e.g. `T = O(log p)`
for the prize), the per-octave constant must satisfy `Δ^μ ≤ T`, i.e. a *uniform* `Δ < 2`.
Contrapositive: if `Δ ≥ 2` at any octave that octave already spends the full doubling — there is no
slack to telescope below `2^μ`. Stated cleanly: `Δ ≥ 2 ⟹ Δ^μ ≥ 2^μ`, so the telescope upper bound
is `≥ 2^μ · base` and cannot certify sub-trivial. -/
theorem no_subtrivial_telescope_of_two_le (Δ : ℝ) (hΔ : 2 ≤ Δ) (μ : ℕ) :
    (2 : ℝ) ^ μ ≤ Δ ^ μ :=
  pow_le_pow_left₀ (by norm_num) hΔ μ

/-- **The genuine-gain criterion (the sharp dichotomy).** A sub-trivial telescope bound
`M μ ≤ T · base` with `T < 2^μ` is reachable from the per-octave geometric mechanism **only if**
the per-octave constant is a genuine decoupling gain `Δ < 2` (since the telescope yields exactly
`Δ^μ · base`, and `Δ^μ < 2^μ ↔ Δ < 2` for `Δ ≥ 0`). The worst-frequency alignment (`cos = 1`,
probe) forces `Δ = 2`, denying the gain — so the ℓ²-decoupling / multiscale route is saving-neutral,
the decoupling sibling of `towerDescent_saving_iff`. -/
theorem gain_iff_lt_two (Δ : ℝ) (hΔ : 0 ≤ Δ) {μ : ℕ} (hμ : 0 < μ) :
    Δ ^ μ < (2 : ℝ) ^ μ ↔ Δ < 2 := by
  constructor
  · intro h
    by_contra hge
    push_neg at hge
    exact absurd h (not_lt.mpr (pow_le_pow_left₀ (by norm_num) hge μ))
  · intro h
    exact pow_lt_pow_left₀ h hΔ hμ.ne'

end ProximityGap.Frontier.DecouplingTowerNoSaving

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.DecouplingTowerNoSaving.telescope_geom
#print axioms ProximityGap.Frontier.DecouplingTowerNoSaving.telescope_trivial_at_two
#print axioms ProximityGap.Frontier.DecouplingTowerNoSaving.no_subtrivial_telescope_of_two_le
#print axioms ProximityGap.Frontier.DecouplingTowerNoSaving.gain_iff_lt_two
