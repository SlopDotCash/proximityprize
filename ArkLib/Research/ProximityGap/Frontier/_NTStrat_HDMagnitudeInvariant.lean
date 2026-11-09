/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Analytic-NT strategy I1 (Hasse–Davenport 2-adic Gauss-sum tower): the duplication is magnitude-invariant (#444)

**The strategy and its barrier.** The prize `M = max_{b≠0}|η_b| ≤ C√(n log q)` is equivalent to square-root
cancellation in the `b`-twisted Gauss-sum sum `G(b) = Σ_{χⁿ=1,χ≠1} χ̄(b)·g(χ)`, where each `|g(χ)| = √p`. The
genuinely-new lead I1 hoped that the **Hasse–Davenport duplication**
`g(χ²) = χ(4)⁻¹ · g(χ) · g(χψ) / g(ψ)` (`ψ` the quadratic character) — which ties the `n = 2^μ` Gauss sums into a
depth-`μ` product tree via index doubling `j ↦ 2j` — would force the `√m` cancellation in `G(b)`.

**Why it stalls at Weil (this file's content).** The HD relation is **magnitude-invariant**: since `|g(χ)| =
|g(χψ)| = |g(ψ)| = √p` and `|χ(4)⁻¹| = 1`, the duplication gives `|g(χ²)| = √p·√p/√p = √p` exactly at *every* node
of the doubling tree. So HD only ever **rotates the phase** of a Gauss sum; it never reduces a magnitude. Therefore
the triangle inequality over the `m−1` summands of `G(b)` is completely unimproved by HD —
`|G(b)| ≤ (m−1)·√p`, giving `M ≤ √p = n^{β/2}` (`= n²` at `β = 4`) = the **Weil** bound, with the full
`√m ~ n^{(β−1)/2} = n^{1.5}` gap to the prize left untouched. (Probe confirmed: the doubling map fragments the `m−1`
sums into `~m/log m` prime-dependent orbits, each HD step spawning a fresh equal-size `ψ`-branch — DOF-conserving,
never DOF-reducing; and the true `√`-cancellation in `G(b)` is the generic Weyl/BGK `b`-equidistribution, smooth and
*uncorrelated* with the HD orbit structure.)

**What this file proves (axiom-clean).** The load-bearing complex-modulus fact, abstracted from the Gauss sums:
the HD-shaped product `a·b/c` of three equal-modulus-`R` complex numbers again has modulus `R` (`hd_modulus_invariant`),
optionally with a unit twist `u` (`|u| = 1`); hence HD conserves the Weil modulus and the triangle bound on a sum of
`N` such terms is `N·R` with no HD improvement (`hd_triangle_unimproved`). This is the precise reason strategy I1
matches Weil. **Not** a closure and **not** an escape — a sharp barrier-localization. Issue #444.
-/

namespace ProximityGap.Frontier.NTStratHD

open Complex

/-- **HD magnitude invariance (core).** For nonzero `c` with `|a| = |b| = |c| = R` and a unit twist `|u| = 1`
(`u = χ(4)⁻¹` in the Hasse–Davenport duplication `g(χ²) = u·g(χ)·g(χψ)/g(ψ)`), the HD-shaped product `u·a·b/c`
again has modulus exactly `R`. So the duplication is a pure phase rotation: it conserves the Weil modulus `√p` at
every node of the doubling tree and never reduces a Gauss-sum magnitude. -/
theorem hd_modulus_invariant (a b c u : ℂ) (R : ℝ) (hc : c ≠ 0)
    (ha : ‖a‖ = R) (hb : ‖b‖ = R) (hcR : ‖c‖ = R) (hu : ‖u‖ = 1) :
    ‖u * a * b / c‖ = R := by
  rw [norm_div, norm_mul, norm_mul, hu, ha, hb, hcR, one_mul]
  have hR : R ≠ 0 := by
    intro h; rw [h] at hcR; exact hc (norm_eq_zero.mp hcR)
  field_simp

/-- **The triangle bound is unimproved by HD.** A sum of `N` HD-tower Gauss sums, each of modulus `R = √p` (modulus
preserved at every node by `hd_modulus_invariant`), is bounded only by `N·R` — the Weil bound. HD redistributes
phases but supplies no magnitude reduction, so it cannot beat `|G(b)| ≤ (m−1)√p`, i.e. `M ≤ √p` (Weil). -/
theorem hd_triangle_unimproved {N : ℕ} (g : Fin N → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hmod : ∀ i, ‖g i‖ = R) :
    ‖∑ i, g i‖ ≤ (N : ℝ) * R := by
  calc ‖∑ i, g i‖ ≤ ∑ i, ‖g i‖ := by
        simpa using norm_sum_le (Finset.univ) g
    _ = ∑ _i : Fin N, R := by exact Finset.sum_congr rfl (fun i _ => hmod i)
    _ = (N : ℝ) * R := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end ProximityGap.Frontier.NTStratHD

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.NTStratHD.hd_modulus_invariant
#print axioms ProximityGap.Frontier.NTStratHD.hd_triangle_unimproved
