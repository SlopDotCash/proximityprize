/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bondarenko–Seip resonator on the GALOIS CONJUGATES `{η_c}` — the exact CAP (issue #444)

## Angle attacked

**Resonance / GCD-sum large-values method (Bondarenko–Seip).** Build a resonator
`R(c) = ∑_k a_k χ_k(c)` on the cyclic Galois group `Gal ≅ ℤ/f` and lower-bound the signed
maximum `M = max_c η_c` (not in general the house `max_c |η_c|`) by the Rayleigh ratio
`⟨η, |R|²⟩ / ⟨1, |R|²⟩`. The conjugate-correlation kernel
`M_{k,k'} = η̂(k−k')` (the DFT of the conjugate vector) governs how large the max can be forced.

## What is genuinely new here vs. `_AvFloor_ResonatorRatioLowerBound.lean`

That file works in *frequency space* (`b`-space) and shows the natural resonator on `S = G`
collapses to the **second-moment ratio** `A₂/A₁` (the `√3·√n` floor). This file works in
**conjugate / Galois space** (`c`-space, the `f` real periods `{η_c}`, fact F1: real-rooted) and
isolates the *Bondarenko–Seip-specific* obstruction:

*Corrections (audit 2026-10-28, R-219).* Throughout, `M` in the Lean statements is the **signed**
maximum `max_c η_c` of the real conjugates, which need not equal the house `max_c |η_c|` (e.g. for
`μ_2 ⊆ 𝔽_5` the signed maximum is `(√5 − 1)/2` while the house is `(√5 + 1)/2`; R-068). The two
theorems are a **variational characterization** of that signed maximum, not an impossibility
result for upper bounds.

1. **Weighted averages lie below the signed maximum.** For any nonnegative weight `w` on the `f`
   conjugates, `∑_c w_c · η_c ≤ M · ∑_c w_c` (`resonator_le_house`). For nonzero nonnegative
   weights the normalized averages range over the convex interval `[min_c η_c, max_c η_c]`
   (not `(−∞, M]`; e.g. for `η ≡ 1` every ratio is `1`).
2. **The supremum of the normalized ratio is the signed maximum** (`resonator_house_attained`):
   the delta-weight `w = 1_{c⋆}` attains `η_{c⋆} = M`. Consequently a uniform upper bound on every
   normalized ratio is **equivalent** to the same upper bound on `M`; the characterization neither
   proves nor excludes an arithmetic upper estimate for the associated kernel. (Exact computation,
   n = 16, 32: `sup_a` Rayleigh quotient `= max eig(η-circulant)/f`, `13.8375` and `22.9834`, to
   `1e-13`; finite evidence only.)

## The exact mechanism by which BS REDUCES (recorded as exact-computation evidence)

The BS *upper* bound on the achievable resonance is a **GCD-sum / Gál-sum** bound on the kernel:
it is non-trivial precisely when the correlation kernel `η̂(j)` *decays* with the arithmetic
complexity of `j` (for `ζ`: `gcd(m,n)/√(mn)` spikes on smooth/divisible pairs, giving the
`exp(C√(log f loglog f))` saving). **Here the kernel is FLAT:** `|η̂(j)| = √p` *exactly* for every
`j ≠ 0` (Gauss-sum magnitude; verified, max/min ratio `1.000000`, std `< 1e-13`, n = 16, 32). A
flat kernel is the WORST case for the Gál sum — `∑_{k,k'∈S} |η̂(k−k')| = |S|²·√p`, no arithmetic
concentration — so this particular entrywise GCD-sum (triangle) estimate gives no saving beyond
the trivial `√p = Θ(√(nm))` scale. Absolute flatness of the entries only makes such an entrywise
estimate weak; it does not rule out phase-sensitive operator estimates for the same kernel. The
resonator quadratic form `M_{k,k'} = η̂(k−k')` is the **circulant whose eigenvalues are the
conjugates `{η_c}` themselves**, so `sup_a (a*Ma)/(f·a*a) = max_c η_c` is a restatement of the
signed maximum: bounding that operator norm from above is *equivalent* to bounding the signed
maximum, neither easier nor provably impossible.

## Honesty (§6 contract)

Both theorems below are exact and axiom-clean generic finite-array lemmas: `resonator_le_house`
(weighted averages are `≤` the signed maximum) and `resonator_house_attained` (the delta weight
attains it). They are a variational characterization of `max_c η_c`. They do NOT show that the
Bondarenko–Seip representation cannot yield an upper bound, and no actual Gauss kernel or class of
Bondarenko–Seip arguments is formalized here. The "flat kernel ⇒ entrywise GCD-sum estimate is
weak" remark is exact-computation evidence about one estimate. No prize upper bound is produced.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.AvBSResonator

open Finset

variable {f : ℕ}

/-! ## 1. Weighted averages are at most the signed maximum (`ratio ≤ M`) -/

/-- **Resonator ≤ signed maximum.** For real values `η : Fin f → ℝ` (e.g. the real Galois
conjugates of a dyadic Gauss period), any nonnegative weight `w : Fin f → ℝ`, and any index `c⋆`
with `η c ≤ η c⋆` for all `c` (the **signed** maximum `M = η c⋆`, which need not be the house
`max_c |η_c|`), the `w`-weighted sum is at most `M` times the total weight:

> `∑_c w_c · η_c  ≤  M · ∑_c w_c`.

Equivalently `M ≥ (∑ w_c η_c)/(∑ w_c)` whenever `∑ w_c > 0`: every nonnegative weight (classically
`w_c = |R(c)|²`) certifies a lower bound on `M`. This lemma by itself says nothing about whether
upper bounds on `M` are obtainable from the same representation (R-219).
-/
theorem resonator_le_house (η w : Fin f → ℝ) (cstar : Fin f)
    (hhouse : ∀ c, η c ≤ η cstar) (hw : ∀ c, 0 ≤ w c) :
    (∑ c, w c * η c) ≤ η cstar * (∑ c, w c) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun c _ => ?_)
  rw [mul_comm (η cstar) (w c)]
  exact mul_le_mul_of_nonneg_left (hhouse c) (hw c)

/-! ## 2. The supremum of the normalized ratio is the signed maximum (delta weight attains it) -/

/-- **The signed maximum is attained by the delta weight.** Take `w = 1_{c⋆}` (mass `1` at the
argmax `c⋆`). Then both sides of `resonator_le_house` are exactly `η c⋆ = M`:

> `∑_c (1_{c⋆})_c · η_c  =  η_{c⋆}  =  M · ∑_c (1_{c⋆})_c`.

Combined with `resonator_le_house`: `sup_w (∑ w η)/(∑ w) = M` over nonzero nonnegative weights.
Consequently a uniform upper bound `C` on every normalized ratio is **equivalent** to `M ≤ C`.
This is a variational characterization; it neither proves nor excludes an upper bound
`M ≤ C√(n log f)` (an earlier docstring claimed the method "cannot produce an UPPER bound";
that does not follow, R-219). -/
theorem resonator_house_attained (η : Fin f → ℝ) (cstar : Fin f) :
    (∑ c, (if c = cstar then (1 : ℝ) else 0) * η c)
      = η cstar * (∑ c, (if c = cstar then (1 : ℝ) else 0)) := by
  simp [Finset.sum_ite_eq']

/-- **Assembled variational characterization.** The delta weight makes the lower bound *tight*
(the weighted sum equals `η c⋆ = M`, the right side `M·1 = M`), and every nonnegative weight stays
`≤ M`. For nonzero nonnegative weights the normalized ratios fill the convex interval
`[min_c η_c, max_c η_c]` (not `(−∞, M]`), with `M` the signed maximum, which can differ from the
house. Since the maximum is attained, upper bounds on all ratios and upper bounds on `M` are
equivalent; this lemma does not show the representation is useless for the prize upper bound. -/
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
