/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The cosh-MGF even-moment identity — a root-free restatement of CORE (#407, §11e)

The prize `CORE` inequality is a bound on the **sup-norm** `M(G) = max_{b≠0} ‖η_b‖` of the
Gauss periods `η_b = ∑_{x∈G} ψ(b·x)`.  A `max` is awkward to bound directly; the dossier
(`#407` §11e) proposes a **root-free** restatement that trades the `max` for a moment
generating function (MGF).

This file formalises the exact MGF identity (probed numerically in
`scripts/probes/probe_cosh_identity_mgf.py`, ratio `1.000000` at
`p = 4129/12289/40961/786433`) and the elementary sup-norm bound it yields.

## The identity (`coshMGF_eq_evenMoment_tsum`)

For every real `y`,
> **`∑_{b∈F} cosh(‖η_b‖·y) = ∑_{r≥0} (q·E_r(G)/(2r)!) · y^{2r}`**,
where `q = |F|` and `E_r(G)` is the `r`-fold additive energy of `G`.

This is a direct consequence of the in-tree even-moment law
`subgroup_gaussSum_moment : ∑_b ‖η_b‖^{2r} = q·E_r(G)`:
expand each `cosh(‖η_b‖y) = ∑_r (‖η_b‖y)^{2r}/(2r)!` and interchange the **finite** sum over
`b` with the (everywhere-convergent) `cosh` power series.  No `√`, no `max`, no analysis on
the period values beyond `cosh`'s entire power series.

For `G = μ_n` this is precisely the dossier's `∑_b cosh(|η_b|y) = p·I₀(2y)^{n/2}` once the
char-0 even-moment generating function `∑_r E_r y^{2r}/(2r)! = I₀(2y)^{n/2}` is substituted
(the Bessel law `DyadicEnergyK1.lean`); here we keep the energies `E_r` symbolic so the
identity is **unconditional and field-general** (no dyadic / roots-of-unity hypothesis).

## The sup-norm bound it yields (`cosh_supNorm_le_coshMGF`)

Because every summand `cosh(‖η_b‖y) ≥ 0`, a single term is dominated by the whole sum:
> **`cosh(‖η_{b₀}‖·y) ≤ ∑_b cosh(‖η_b‖·y)`** for every `b₀` and every `y`.

Combined with the identity, for `y > 0` this gives a per-`b` upper bound
`‖η_{b₀}‖ ≤ arcosh(RHS(y))/y`, optimisable in `y` — the **root-free CORE upper-bound
mechanism**.  Empirically (the probe) `min_y arcosh(p·I₀(2y)^{n/2})/y` already beats the
floor `√(2n log m)` at `n = 8` (`8.56–9.38` vs `9.99–11.69`).  This file lands the exact
algebraic substrate; turning the optimised bound into the prize constant is the open `§5.0`
work (it requires the asymptotics of `I₀(2y)^{n/2}` at the saddle, not just the identity).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.  Issue #407, §11e.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.CoshMGFIdentity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The cosh-MGF even-moment identity (#407 §11e).**  Summing `cosh(‖η_b‖·y)` over all
`b ∈ F` equals the even-moment power series with coefficients `q·E_r(G)/(2r)!`:
`∑_b cosh(‖η_b‖ y) = ∑_r (q·E_r(G)/(2r)!) y^{2r}`.  Proof: expand each `cosh` by its
(entire) power series and interchange with the finite sum over `b`, then apply the in-tree
even-moment law `∑_b ‖η_b‖^{2r} = q·E_r(G)`.  Field-general and unconditional. -/
theorem coshMGF_eq_evenMoment_tsum {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (y : ℝ) :
    (∑ b : F, Real.cosh (‖eta ψ G b‖ * y))
      = ∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ) := by
  classical
  -- per-`b`, `cosh(‖η_b‖y)` is the sum of its (entire) power series
  have hb : ∀ b : F,
      HasSum (fun r : ℕ => (‖eta ψ G b‖ * y) ^ (2 * r) / ((2 * r).factorial : ℝ))
        (Real.cosh (‖eta ψ G b‖ * y)) := fun b => Real.hasSum_cosh _
  -- the finite sum over `b` of these `HasSum`s sums termwise
  have hsum := hasSum_sum (fun b (_ : b ∈ (Finset.univ : Finset F)) => hb b)
  rw [← hsum.tsum_eq]
  refine tsum_congr (fun r => ?_)
  -- termwise: ∑_b (‖η_b‖y)^{2r}/(2r)! = (∑_b ‖η_b‖^{2r}) y^{2r}/(2r)! = q·E_r·y^{2r}/(2r)!
  rw [← subgroup_gaussSum_moment hψ G r]
  rw [show ((∑ b : F, ‖eta ψ G b‖ ^ (2 * r)) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
        = ∑ b : F, (‖eta ψ G b‖ ^ (2 * r) * y ^ (2 * r) / ((2 * r).factorial : ℝ)) by
      rw [Finset.sum_mul, Finset.sum_div]]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [mul_pow]

/-- **Single-period domination (the root-free sup-norm mechanism).**  Since every summand
`cosh(‖η_b‖·y)` is nonnegative, the term at any fixed `b₀` is at most the whole sum:
`cosh(‖η_{b₀}‖·y) ≤ ∑_b cosh(‖η_b‖·y)`.  Combined with `coshMGF_eq_evenMoment_tsum`, for
`y > 0` this bounds `‖η_{b₀}‖` by `arcosh(RHS(y))/y` — turning the prize sup-norm `CORE`
into a `max`-free MGF comparison. -/
theorem cosh_supNorm_le_coshMGF {F : Type*} [Field F] [Fintype F]
    {ψ : AddChar F ℂ} (G : Finset F) (y : ℝ) (b₀ : F) :
    Real.cosh (‖eta ψ G b₀‖ * y) ≤ ∑ b : F, Real.cosh (‖eta ψ G b‖ * y) := by
  refine Finset.single_le_sum (f := fun b => Real.cosh (‖eta ψ G b‖ * y)) ?_ (Finset.mem_univ b₀)
  intro b _; positivity

/-- **The CORE sup-norm MGF bound (assembled).**  For every `b₀` and every real `y`, the
single Gauss period `cosh(‖η_{b₀}‖·y)` is bounded by the even-moment MGF:
`cosh(‖η_{b₀}‖·y) ≤ ∑_r (q·E_r(G)/(2r)!) y^{2r}`.  This is the root-free, `max`-free upper
bound on `CORE` (one `b` at a time); optimising the free parameter `y` is the open `§5.0`
step. -/
theorem cosh_period_le_evenMoment_tsum {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (y : ℝ) (b₀ : F) :
    Real.cosh (‖eta ψ G b₀‖ * y)
      ≤ ∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ) :=
  (cosh_supNorm_le_coshMGF G y b₀).trans_eq (coshMGF_eq_evenMoment_tsum hψ G y)

end ProximityGap.Frontier.CoshMGFIdentity

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — NO sorryAx)
open ProximityGap.Frontier.CoshMGFIdentity in
#print axioms coshMGF_eq_evenMoment_tsum
open ProximityGap.Frontier.CoshMGFIdentity in
#print axioms cosh_supNorm_le_coshMGF
open ProximityGap.Frontier.CoshMGFIdentity in
#print axioms cosh_period_le_evenMoment_tsum
