/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# wf-NA: finite-field RESTRICTION collapses to the deep moment (even-r extension norm)

**Lane wf-NA (#407): Mockenhaupt–Tao / Iosevich–Koh finite-field restriction for `μ_n`.**

`M(n) = max_{b ≠ 0} ‖Σ_{x ∈ μ_n} e_p(b x)‖` is the `L^∞` norm of the EXTENSION operator
`(E f)(b) = Σ_{x ∈ μ_n} f(x) e_p(b x)` applied to `f = 1`. The finite-field restriction
framework would bound `M(n)` via the extension `L^r` norms `‖E 1‖_{L^r(F_q)}`.

This file isolates, axiom-clean, the **exact algebraic reason the EVEN-`r` extension norm
gives nothing the deep moments do not**:

  `‖E 1‖_{L^{2s}(F_q, counting)}^{2s} = Σ_{b} ‖η_b‖^{2s}`  and each `‖η_b‖^{2s} = (‖η_b‖²)^s`

where `η_b = (E 1)(b)`. The right-hand side is, term by term, the `s`-th deep moment of
the periods — exactly the object `q · E_s` of the moment route (`SubgroupGaussSumRawMoment`).
So for every even exponent the restriction `L^r` norm is the deep moment **verbatim**; the
`L^∞`-from-`L^r` step is mere monotonicity (`max ≤ L^r`), and Hölder interpolation of the
`L^r` family is log-convex, so no family of even moments beats the per-`r` minimum.

The numerical companions
`scripts/probes/probe_wf2NA_restriction_extension.py` (restriction−moment = 0 to machine
precision at every prize prime n=8,16,32) and
`scripts/probes/probe_wf2NA_steintomas_dual.py` (the dual Stein–Tomas side is circular: its
non-trivial input is the Fourier decay = `M(n)` itself; the only borrowable input —
additive energy `E₂` — caps at the L4 no-go) close the lane:

**finite-field restriction for `μ_n` reduces to the deep-moment wall.**

This is the honest "pinned with precise reason" brick: it proves the *collapse identity*,
not any sub-trivial bound (none exists from this lens).
-/

namespace ArkLib.ProximityGap.Frontier.WfNARestriction

open Finset BigOperators

variable {ι κ : Type*} [Fintype κ]

/-- The extension operator value `η b = Σ_{x} f x · k x b` for a kernel `k` (the additive
character `e_p(b·)` evaluated on the variety, abstracted as an arbitrary `ℂ`-kernel).
`f = 1` recovers the Gauss period `η_b = Σ_{x ∈ μ_n} e_p(b x)`. -/
noncomputable def extOp (f : ι → ℂ) (k : ι → κ → ℂ) (S : Finset ι) (b : κ) : ℂ :=
  ∑ x ∈ S, f x * k x b

/-- **Restriction-collapse identity (exact).** The `L^{2s}` extension norm to the `2s`-th
power, over the ambient `F_q` (counting measure = `∑_b`), equals the bare sum of the
`2s`-th powers of the period magnitudes, each rewritten as `(‖η_b‖²)^s`. The summand
`(‖η_b‖²)^s` is exactly the per-frequency deep-moment contribution; summing over `b` is
`q · E_s`. Hence the even-`r` extension norm IS the deep moment, with no extra structure. -/
theorem extNorm_pow_eq_moment
    (f : ι → ℂ) (k : ι → κ → ℂ) (S : Finset ι) (s : ℕ) :
    ∑ b : κ, ‖extOp f k S b‖ ^ (2 * s)
      = ∑ b : κ, (‖extOp f k S b‖ ^ 2) ^ s := by
  apply Finset.sum_congr rfl
  intro b _
  rw [pow_mul]

/-- **`L^∞`-from-`L^r` is monotonicity only (no restriction gain).** For any single
frequency `b₀`, its magnitude to the `2s` is bounded by the full `L^{2s}` sum, i.e.
`‖η_{b₀}‖^{2s} ≤ Σ_b ‖η_b‖^{2s}`. Taking `b₀` the maximizer gives `M(n)^{2s} ≤ q·E_s` —
the exact moment bound and nothing sharper. (This is the only inequality the restriction
`L^r → L^∞` step provides; it is term-domination, not a restriction theorem.) -/
theorem maxFreq_le_extNorm
    (f : ι → ℂ) (k : ι → κ → ℂ) (S : Finset ι) (s : ℕ) (b₀ : κ) :
    ‖extOp f k S b₀‖ ^ (2 * s)
      ≤ ∑ b : κ, ‖extOp f k S b‖ ^ (2 * s) := by
  refine Finset.single_le_sum (f := fun b => ‖extOp f k S b‖ ^ (2 * s))
    (fun b _ => ?_) (Finset.mem_univ b₀)
  positivity

end ArkLib.ProximityGap.Frontier.WfNARestriction
