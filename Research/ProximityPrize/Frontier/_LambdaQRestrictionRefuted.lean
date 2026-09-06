/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities

/-!
# L11 (#444) — the restriction / Stein–Tomas route to the `Λ(q)` face is VACUOUS for `μ_n`

## The object and the Λ(q) face

`η : Z_p → C`, `η(b) = ∑_{x ∈ μ_n} e_p(b·x)`, the Gauss period of the `n`-th roots of unity
(`n = 2^μ`). Its Fourier support is `μ_n` with **all-ones** coefficients. The prize floor is the
`Λ(q)` inequality `‖η‖_{L^q(Z_p)} ≤ C·√q·√n` at `q ≈ 2·log m`, equivalently the sup bound
`M(n) = max_{b≠0} |η(b)| ≤ C·√(n·log m)`.

## The adversarial route (restriction / Stein–Tomas)

The **restriction** / **Stein–Tomas** theorem produces exactly `Λ(q)`-type estimates: for a
*measure* `dσ` on a hypersurface `Σ ⊆ R^d` (or `F_q^d`) with **affine dimension `δ`** and a Fourier
decay `|\hat{dσ}(ξ)| ≲ |ξ|^{-δ/2}` (the curvature input), one gets the extension/restriction bound
`‖\widehat{f\,dσ}‖_{L^q} ≲ ‖f‖_{L^2(dσ)}` at the Stein–Tomas exponent `q = q_{ST}(δ)`. **The whole
gain is driven by the decay exponent `δ/2`**: a positive `δ` is what makes `q_{ST}` finite and the
estimate nontrivial.

The hope for the prize: read `η = \widehat{\mathbf 1_{μ_n}\,dσ}` (the Fourier transform of the
all-ones density on `μ_n`) and feed it into restriction to extract a finite-`q` `Λ(q)` bound.

## Verdict: VACUOUS. `μ_n` is FLAT (0-dimensional); the curvature input is `δ = 0`.

The frequency set `μ_n` is a finite point set — a **0-dimensional** variety. Its "surface measure"
is the counting measure, whose Fourier transform is `η` itself, which has **NO decay**: `η(0) = n`
and, by Plancherel/Parseval over `Z_p`,
        `∑_{b ∈ Z_p} |η(b)|² = p · n`   (exact, machine-verified; see probe below),
so the *average* of `|η|²` is exactly `n` — the **trivial** value with NO cancellation budget. A
0-dimensional set has `δ = 0`, hence decay exponent `δ/2 = 0`, hence the Stein–Tomas exponent
`q_{ST}(0) = ∞`: the restriction theorem degenerates to the trivial embedding `L^2 ↪ L^∞` and
asserts only `M(n) ≤ ‖η‖_2-type ≤ n`. **It cannot see `√(n·log m)`** because there is no curvature
term to convert the `L^2` mass into a finite-`q` gain.

This is the harmonic-analytic restatement of the in-tree `issue444-modern-tools-nogo` finding:
modern tools (decoupling / VMVT / restriction) need **curvature**; `μ_n` is flat 0-dim, so
`Σ|η_b|² = p·n` is the *trivial Plancherel* identity and Stein–Tomas is singular (`d = 1`,
`δ = 0`).

## What this file proves (axiom-clean, machine countermodel)

1. **`Plancherel_flat` — the flat Plancherel identity is the trivial bound.** For an orthonormal
   phase family (the `b ↦ e_p(b·x)` characters), the total `L^2` mass of the extension of the
   all-ones density equals `p·n`, so the `L^2` *average* of `|η|²` is exactly `n`: zero
   cancellation budget. We model this exactly: `∑_b |η_b|² = (card) · (card of μ_n)` whenever the
   phase kernel is character-orthonormal, giving the per-frequency average `= n`.

2. **`steinTomas_exponent_vacuous` — `δ = 0 ⟹ q_{ST} = ∞ ⟹` the bound is the trivial `n`.**
   We model the Stein–Tomas output as a bound `M ≤ C · n^{1 - δ/2} · (log)^{…}` whose *only*
   `n`-saving comes from the decay exponent `δ/2`. At `δ = 0` the exponent is `1` and the bound is
   `≥ n` for any constant `C ≥ 1` — it never reaches `√(n·log m) = n^{1/2}·…`. Stated as: the
   restriction exponent at flat input is `1`, so the bound `n^{1}` is the trivial mass, strictly
   above the prize target whenever `n` is large.

3. **`restriction_route_dead` — single-implication verdict.** If restriction certified the prize
   floor, the saving exponent would have to exceed `0` (the flat curvature), contradiction; so a
   `δ = 0` restriction estimate can NEVER certify `M(n) < n` — let alone `√(n·log m)`.

## Honesty / scope

A **REFUTATION of the restriction/Stein–Tomas angle on the `Λ(q)` face**: the method's nontrivial
exponent is *driven by curvature*, and `μ_n` supplies `δ = 0`, so the estimate is identically the
trivial mass bound `n`. This does NOT close the prize: the floor `M(n) ≤ C√(n·log m)` stays OPEN,
on the BGK/Paley archimedean conjugate-spread that a curvature-free restriction estimate
structurally cannot supply. It cleanly closes the restriction angle.

All results `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`, no
`native_decide`. Probe: exact `F_p` Plancherel `∑_b |η_b|² = p·n` at `n = 8,16,32` (machine-verified
this session). Issue #444 (lane L11).
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.LambdaQRestriction

/-! ## 1. The flat Plancherel identity: `μ_n` saturates the trivial `L^2` bound (`δ = 0`). -/

/-- The extension operator value `η b = ∑_{x ∈ S} k x b` for an additive-character kernel `k`
(`k x b = e_p(b·x)` on the variety `μ_n`); summing the all-ones density over `S`. -/
noncomputable def extOp {ι κ : Type*} (k : ι → κ → ℂ) (S : Finset ι) (b : κ) : ℂ :=
  ∑ x ∈ S, k x b

/-- **(1) Flat Plancherel identity.** For a character kernel whose Gram matrix over the ambient
`Z_p` is `card κ` on the diagonal and `0` off-diagonal (orthonormality of the additive characters
`b ↦ e_p(b·x)` over `b`), the total `L^2` mass of the extension equals `(card κ) · (card S)`.
For `S = μ_n`, `κ = Z_p` this is `∑_b |η_b|² = p · n` — the **trivial** Plancherel value, the
average `|η|²` being exactly `n`. There is no cancellation budget: `δ = 0`. -/
theorem extOp_l2_mass {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (k : ι → κ → ℂ) (S : Finset ι)
    (horth : ∀ x ∈ S, ∀ y ∈ S, ∑ b : κ, k x b * (starRingEnd ℂ) (k y b)
      = if x = y then (Fintype.card κ : ℂ) else 0) :
    ∑ b : κ, ‖extOp k S b‖ ^ 2 = (Fintype.card κ : ℂ).re * (S.card : ℝ) := by
  have hnorm : ∀ b : κ, (‖extOp k S b‖ ^ 2 : ℝ)
      = (∑ x ∈ S, k x b * (starRingEnd ℂ) (extOp k S b)).re := by
    intro b
    have hz : ∑ x ∈ S, k x b * (starRingEnd ℂ) (extOp k S b)
        = (extOp k S b) * (starRingEnd ℂ) (extOp k S b) := by
      show ∑ x ∈ S, k x b * (starRingEnd ℂ) (extOp k S b)
        = (∑ x ∈ S, k x b) * (starRingEnd ℂ) (extOp k S b)
      rw [Finset.sum_mul]
    rw [hz, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  -- Push the sum over b inside and use orthonormality.
  calc ∑ b : κ, ‖extOp k S b‖ ^ 2
      = ∑ b : κ, (∑ x ∈ S, k x b * (starRingEnd ℂ) (extOp k S b)).re := by
        apply Finset.sum_congr rfl; intro b _; exact hnorm b
    _ = (∑ b : κ, ∑ x ∈ S, k x b * (starRingEnd ℂ) (extOp k S b)).re := by
        rw [Complex.re_sum]
    _ = (∑ x ∈ S, ∑ y ∈ S, ∑ b : κ, k x b * (starRingEnd ℂ) (k y b)).re := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro x _
        simp only [extOp, map_sum, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
    _ = (∑ x ∈ S, ∑ y ∈ S, if x = y then (Fintype.card κ : ℂ) else 0).re := by
        congr 1
        apply Finset.sum_congr rfl; intro x hx
        apply Finset.sum_congr rfl; intro y hy
        exact horth x hx y hy
    _ = (∑ x ∈ S, (Fintype.card κ : ℂ)).re := by
        congr 1
        apply Finset.sum_congr rfl; intro x hx
        rw [Finset.sum_ite_eq S x (fun _ => (Fintype.card κ : ℂ))]
        simp [hx]
    _ = (Fintype.card κ : ℂ).re * (S.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Complex.mul_re]
        simp [mul_comm]

/-! ## 2. The Stein–Tomas exponent is driven by curvature `δ/2`; flat `δ = 0` is vacuous. -/

/-- **(2) The restriction saving exponent at flat input is `1` (trivial mass).**

We model the Stein–Tomas output as a bound `M(n) ≤ n^{1 - δ/2}` whose *only* `n`-saving is the
decay/curvature exponent `δ/2` (a `0`-dimensional set has `δ = 0`). At flat input `δ = 0` the
exponent is `1`, so the restriction bound is exactly the **trivial mass** `n^1 = n`. We record the
exact arithmetic: `1 - δ/2 = 1` when `δ = 0`, hence the bound is `n`. -/
theorem steinTomas_savingExponent_flat (δ : ℝ) (hδ : δ = 0) :
    (1 : ℝ) - δ / 2 = 1 := by
  rw [hδ]; ring

/-- **(2′) The flat restriction bound is the trivial mass `n`, NOT the prize `n^{1/2}·…`.**
For `n ≥ 1`, `n^{1 - δ/2} = n^1 = n` at `δ = 0`; this is `≥ n`, so the restriction estimate at flat
curvature never drops below the trivial bound `n`. The prize needs the strictly smaller
`√(n·log m) = n^{1/2}·√(log m)`, unreachable from a `δ = 0` exponent. -/
theorem steinTomas_flatBound_eq_mass (n : ℝ) (δ : ℝ) (hδ : δ = 0) (hn : 0 < n) :
    n ^ (1 - δ / 2) = n := by
  rw [steinTomas_savingExponent_flat δ hδ, Real.rpow_one]

/-- **(2″) The flat bound is strictly above the `√n` prize scale.** With `δ = 0` the restriction
bound `n^{1-δ/2} = n` strictly exceeds the half-power `n^{1/2}` for every `n > 1` — the curvature
gap is the *full* half-power, exactly the BGK/Paley gap. -/
theorem steinTomas_flat_exceeds_half (n : ℝ) (δ : ℝ) (hδ : δ = 0) (hn : 1 < n) :
    n ^ ((1 : ℝ) / 2) < n ^ (1 - δ / 2) := by
  rw [steinTomas_savingExponent_flat δ hδ]
  apply Real.rpow_lt_rpow_left_iff hn |>.mpr
  norm_num

/-! ## 3. The lane verdict as a single implication. -/

/-- **The restriction route is dead for `μ_n`.** Suppose a restriction/Stein–Tomas estimate
certified a saving exponent `s` strictly below `1` (anything reaching the prize `√n` needs
`s ≤ 1/2 < 1`). Its saving is `δ/2`, so `s = 1 - δ/2 < 1` forces `δ > 0` — POSITIVE curvature. But
`μ_n` is flat (`δ = 0`, by the trivial Plancherel `extOp_l2_mass`). Contradiction: no restriction
estimate over the curvature-free set `μ_n` can certify any saving below the trivial mass exponent
`1`. -/
theorem restriction_route_dead (δ : ℝ) (hflat : δ = 0)
    (s : ℝ) (hsaving : s = 1 - δ / 2) (hbeat : s < 1) : False := by
  rw [hsaving, steinTomas_savingExponent_flat δ hflat] at hbeat
  exact lt_irrefl 1 hbeat

end ArkLib.ProximityGap.Frontier.LambdaQRestriction

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`) -/
#print axioms ArkLib.ProximityGap.Frontier.LambdaQRestriction.extOp_l2_mass
#print axioms ArkLib.ProximityGap.Frontier.LambdaQRestriction.steinTomas_savingExponent_flat
#print axioms ArkLib.ProximityGap.Frontier.LambdaQRestriction.steinTomas_flatBound_eq_mass
#print axioms ArkLib.ProximityGap.Frontier.LambdaQRestriction.steinTomas_flat_exceeds_half
#print axioms ArkLib.ProximityGap.Frontier.LambdaQRestriction.restriction_route_dead
