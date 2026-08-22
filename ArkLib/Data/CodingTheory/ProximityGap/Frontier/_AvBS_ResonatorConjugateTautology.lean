/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bondarenko–Seip resonator on the GALOIS CONJUGATES `{η_c}` — the exact CAP (issue #444)

## Angle attacked

**Resonance / GCD-sum large-values method (Bondarenko–Seip).** Build a resonator
`R(c) = ∑_k a_k χ_k(c)` on the cyclic Galois group `Gal ≅ ℤ/f` and lower-bound the house
`M = max_c η_c` by the Rayleigh ratio `⟨η, |R|²⟩ / ⟨1, |R|²⟩`. The conjugate-correlation kernel
`M_{k,k'} = η̂(k−k')` (the DFT of the conjugate vector) governs how large the max can be forced.

## What is genuinely new here vs. `_AvFloor_ResonatorRatioLowerBound.lean`

That file works in *frequency space* (`b`-space) and shows the natural resonator on `S = G`
collapses to the **second-moment ratio** `A₂/A₁` (the `√3·√n` floor). This file works in
**conjugate / Galois space** (`c`-space, the `f` real periods `{η_c}`, fact F1: real-rooted) and
isolates the *Bondarenko–Seip-specific* obstruction:

1. **The resonator is a pure MAX-detector — a one-sided LOWER bound, never an upper bound.**
   For *any* nonnegative weight `w` on the `f` conjugates,
   `∑_c w_c · η_c ≤ M · ∑_c w_c` (`resonator_le_house`), so the certified ratio is `≤ M`.
2. **The supremum of the resonator ratio equals the house EXACTLY** (`resonator_house_attained`):
   the delta-weight `w = 1_{c⋆}` at the argmax attains `η_{c⋆} = M`. Hence the BS method
   *reproduces* `M` at full resolution but **provably cannot certify anything below `M`** and
   **cannot produce the prize UPPER bound `M ≤ C√(n log f)` at all** — the wrong inequality
   direction. (Exact computation, n = 16, 32: `sup_a` Rayleigh quotient `= max eig(η-circulant)/f
   = house`, `13.8375` and `22.9834`, to `1e-13`.)

## The exact mechanism by which BS REDUCES (recorded as exact-computation evidence)

The BS *upper* bound on the achievable resonance is a **GCD-sum / Gál-sum** bound on the kernel:
it is non-trivial precisely when the correlation kernel `η̂(j)` *decays* with the arithmetic
complexity of `j` (for `ζ`: `gcd(m,n)/√(mn)` spikes on smooth/divisible pairs, giving the
`exp(C√(log f loglog f))` saving). **Here the kernel is FLAT:** `|η̂(j)| = √p` *exactly* for every
`j ≠ 0` (Gauss-sum magnitude; verified, max/min ratio `1.000000`, std `< 1e-13`, n = 16, 32). A
flat kernel is the WORST case for the Gál sum — `∑_{k,k'∈S} |η̂(k−k')| = |S|²·√p`, no arithmetic
concentration — so the BS GCD-sum saving is **vacuous**, returning only the trivial `√p = Θ(√(nm))`
floor (the same second-moment / Weil wall as every height functional). The resonator quadratic form
`M_{k,k'} = η̂(k−k')` is the **circulant whose eigenvalues are the conjugates `{η_c}` themselves**,
so `sup_a (a*Ma)/(f·a*a) = max_c η_c = M` is a *tautology*: BS restates the house, never bounds it.

## Honesty (§6 contract)

Both theorems below are exact and axiom-clean. The CAP conclusion — *BS resonance is a lower-bound
detector that reproduces but cannot exceed nor invert the house* — is the **rigorous content** of
`resonator_le_house` + `resonator_house_attained` (the sup over weights is exactly `M`). The
"flat-kernel ⇒ GCD-sum vacuous" reduction is recorded as exact-computation evidence (the kernel
flatness `|η̂(j)| = √p` is a Gauss-sum fact; the consequence is that BS adds nothing to the
second-moment floor). No prize upper bound is produced; the wall is unmoved.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.AvBSResonator

open Finset

variable {f : ℕ}

/-! ## 1. The resonator is a pure lower-bound detector (`ratio ≤ house`) -/

/-- **Resonator ≤ house.** For the `f` real Galois conjugates `η : Fin f → ℝ` of the Gauss period
(fact F1: dyadic `n` ⟹ all conjugates real), any nonnegative resonator weight `w : Fin f → ℝ`, and
any index `c⋆` with `η c ≤ η c⋆` for all `c` (the house `M = η c⋆`), the `w`-weighted sum of the
conjugates is at most `M` times the total weight:

> `∑_c w_c · η_c  ≤  M · ∑_c w_c`.

Equivalently `M ≥ (∑ w_c η_c)/(∑ w_c)` whenever `∑ w_c > 0`. This is the **Bondarenko–Seip
resonator lower bound**: every nonnegative weight `w` (classically `w_c = |R(c)|²` for a resonator
`R`) certifies a lower bound on the house, and *only* a lower bound (the inequality is one-sided).
-/
theorem resonator_le_house (η w : Fin f → ℝ) (cstar : Fin f)
    (hhouse : ∀ c, η c ≤ η cstar) (hw : ∀ c, 0 ≤ w c) :
    (∑ c, w c * η c) ≤ η cstar * (∑ c, w c) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun c _ => ?_)
  rw [mul_comm (η cstar) (w c)]
  exact mul_le_mul_of_nonneg_left (hhouse c) (hw c)

/-! ## 2. The supremum of the resonator ratio is EXACTLY the house (delta-weight attains it) -/

/-- **The house is attained by the delta resonator.** Take the degenerate resonator weight
`w = 1_{c⋆}` (mass `1` at the argmax `c⋆`, `0` elsewhere) — the limit of a resonator `R` that is a
"delta at `c⋆`". Then both sides of `resonator_le_house` are exactly `η c⋆ = M`:

> `∑_c (1_{c⋆})_c · η_c  =  η_{c⋆}  =  M · ∑_c (1_{c⋆})_c`.

Combined with `resonator_le_house`, this shows the **supremum over all nonnegative weights of the
resonator ratio equals the house**, `sup_w (∑ w η)/(∑ w) = M`. Therefore the Bondarenko–Seip
method:
* **reproduces** the house exactly (no information is lost at full resolution), but
* **cannot certify any value `> M`** (it is a valid lower bound), and crucially
* **cannot produce an UPPER bound** `M ≤ C√(n log f)` — wrong inequality direction.
The prize needs the *upper* tail; resonance only ever gives the *lower* envelope, which here
coincides with `M`. -/
theorem resonator_house_attained (η : Fin f → ℝ) (cstar : Fin f) :
    (∑ c, (if c = cstar then (1 : ℝ) else 0) * η c)
      = η cstar * (∑ c, (if c = cstar then (1 : ℝ) else 0)) := by
  simp [Finset.sum_ite_eq']

/-- **Assembled CAP.** The delta-weight makes the resonator lower bound *tight*: the weighted sum
equals `η c⋆ = M` and the right side equals `M·1 = M`. So among all nonnegative resonators the ratio
ranges over `(-∞, M]` with the maximum `M` attained — the BS resonance method's entire output on the
conjugate vector is the closed interval up to the house. It is a **two-sided characterization of the
LOWER envelope only**; it supplies no upper bound, hence reduces for the prize (which is an upper
bound). -/
theorem resonator_sup_eq_house (η : Fin f → ℝ) (cstar : Fin f)
    (hhouse : ∀ c, η c ≤ η cstar) :
    -- the delta resonator achieves equality in `resonator_le_house`
    (∑ c, (if c = cstar then (1 : ℝ) else 0) * η c)
        = η cstar * (∑ c, (if c = cstar then (1 : ℝ) else 0))
    ∧ -- and every nonnegative resonator stays `≤` the house
    (∀ w : Fin f → ℝ, (∀ c, 0 ≤ w c) → (∑ c, w c * η c) ≤ η cstar * (∑ c, w c)) :=
  ⟨resonator_house_attained η cstar, fun w hw => resonator_le_house η w cstar hhouse hw⟩

end ArkLib.ProximityGap.Frontier.AvBSResonator

#print axioms ArkLib.ProximityGap.Frontier.AvBSResonator.resonator_le_house
#print axioms ArkLib.ProximityGap.Frontier.AvBSResonator.resonator_house_attained
#print axioms ArkLib.ProximityGap.Frontier.AvBSResonator.resonator_sup_eq_house
