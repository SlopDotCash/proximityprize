/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The moment/energy route is vacuous at scale: Cauchy–Schwarz forces the moment bound `≥ n` (#444)

**The result.** After mapping the wall from 14 analytic-NT directions, the only routes that could in principle reach
the prize `M = max_{b≠0}|η_b| ≤ C√(n log q)` are the **moment/energy** family: from the exact identity
`Σ_{b∈F_p} |η_b|^{2r} = p·E_r` (`E_r` = the `r`-fold additive energy of `μ_n`, `= Σ_s c_r(s)²` where
`c_r(s) = #{r-tuples from μ_n summing to s}`), one gets `M^{2r} ≤ p·E_r`, hence the moment bound
`M ≤ (p·E_r)^{1/2r}`. The char-0 ideal `E_r ≤ (2r−1)‼·n^r` at the optimal depth `r ≈ log p` would give exactly the
prize `√(2n log p)`.

**⚠ CORRECTION (2026-06-18) — this file does NOT close the moment route for the prize.** The bound used below,
`M^{2r} ≤ p·E_r`, is **loose**: it includes the trivial `b = 0` frequency `η_0 = Σ_{x∈μ_n} 1 = n`. The prize is
`M = max_{b≠0}|η_b|`, bounded by the **b≠0 energy** `M^{2r} ≤ Σ_{b≠0}|η_b|^{2r} = p·E_r − n^{2r}` (subtracting
`|η_0|^{2r} = n^{2r}`). The Cauchy–Schwarz "floor" `p·E_r ≥ n^{2r}` is **exactly** that subtracted `b=0` term — so
the "saturation" `E_r → n^{2r}/p` at `r > β` is the trivial frequency `η_0 = n` taking over the *full* energy, and is
**irrelevant** to `M`. The prize-relevant `b≠0` bound `(p·E_r − n^{2r})^{1/2r}`, optimized over `r`, empirically gives
`M ≤ C·√(2n log m)` with **C bounded** (≈ 0.88, 1.0, 1.2 at `n = 8, 16, 32`, → `√(β/(β−1)) ≈ 1.155`; the b≠0 MGF
margin `K(y*) − log m` stays `≤ −1.4` to `n = 256`). So the moment/MGF route is **NOT vacuous** for the prize. The
theorems below remain **true as abstract inequalities about `p·E_r`** (the b=0-inflated full energy), but they do not
bound `M`, and the "cannot reach the prize" reading is withdrawn. The genuine open core is the **b≠0 sub-Gaussian
energy** `μ_{2r} = (p·E_r − n^{2r})/(p−1) ≤ (2r−1)‼·n^r` (`= Wick·e^{−r²/2n}(1+o(1))`), which holds empirically and
yields the prize via the moment bound — the actual solution-space target.

**Original (now-corrected) statement.** The additive energy has an **unconditional Cauchy–Schwarz lower bound**: the
`n^r` `r`-tuples distribute over at most `p` sums, so `n^{2r} = (Σ_s c_r(s))² ≤ (#support)·Σ_s c_r(s)² ≤ p·E_r`
(Chebyshev/Cauchy–Schwarz), i.e. `p·E_r ≥ n^{2r}` for every depth `r` and every prime `p`. This makes the **looser**
`(p·E_r)^{1/2r} ≥ n` bound vacuous — but per the correction above, `p·E_r` is the wrong object (it includes `η_0`);
the prize uses `p·E_r − n^{2r}`.

**What this file proves (axiom-clean).**
* `energy_cauchy_schwarz_lower` — the unconditional `N² ≤ p·E` from Chebyshev (`N = Σc`, support `≤ p`, `E = Σc²`).
* `moment_bound_ge_card` — specialized to `N = n^r`: `n^{2r} ≤ p·E_r` (the saturation floor).
* `moment_certificate_cannot_reach_prize` — if a target `T` has `T < n` then `T^{2r} < p·E_r`, so the **looser**
  certificate `M^{2r} ≤ p·E_r` cannot certify `M ≤ T`. **(Per the correction: this is the b=0-inflated bound; the
  prize-relevant `M^{2r} ≤ p·E_r − n^{2r}` is not closed by this.)**

Not a closure, and (per the 2026-06-18 correction) **not** a no-go for the prize either: the theorems bound the
b=0-inflated `p·E_r`, not `M = max_{b≠0}|η_b|`. Issue #444.
-/

namespace ProximityGap.Frontier.MomentSaturation

open Finset

/-- **Unconditional Cauchy–Schwarz (Chebyshev) energy floor.** For a nonnegative fiber-count function `c` supported
on a finset `s` of size `≤ p`, with total mass `Σ_{s} c = N`, the energy `E = Σ_{s} c²` satisfies `N² ≤ p·E`. (For
the additive energy, `c = c_r` the `r`-tuple fiber counts over `F_p`, `N = n^r`, `s` the `r`-fold sumset support
`≤ p`.) The `n^r` tuples cannot concentrate below the `n^{2r}/p` energy floor — the saturation lower bound. -/
theorem energy_cauchy_schwarz_lower {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (p : ℕ) (hcard : (s.card : ℝ) ≤ (p : ℝ)) (hcsq : 0 ≤ ∑ i ∈ s, c i ^ 2)
    (N : ℝ) (hN : ∑ i ∈ s, c i = N) :
    N ^ 2 ≤ (p : ℝ) * ∑ i ∈ s, c i ^ 2 := by
  have hcheb : (∑ i ∈ s, c i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, c i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc N ^ 2 = (∑ i ∈ s, c i) ^ 2 := by rw [hN]
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, c i ^ 2 := hcheb
    _ ≤ (p : ℝ) * ∑ i ∈ s, c i ^ 2 := by exact mul_le_mul_of_nonneg_right hcard hcsq

/-- **The saturation floor for the additive energy.** Specializing the Cauchy–Schwarz floor to the `r`-fold sumset
(`N = n^r` tuples over a support `≤ p`): `n^{2r} ≤ p·E_r`. So the moment quantity `p·E_r` — which upper-bounds
`M^{2r}` via `M^{2r} ≤ Σ_b|η_b|^{2r} = p·E_r` — is itself `≥ n^{2r}`, i.e. the moment bound `(p·E_r)^{1/2r} ≥ n`. -/
theorem moment_bound_ge_card {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (p n r : ℕ) (hcard : (s.card : ℝ) ≤ (p : ℝ)) (hcsq : 0 ≤ ∑ i ∈ s, c i ^ 2)
    (hN : ∑ i ∈ s, c i = (n : ℝ) ^ r) :
    ((n : ℝ) ^ r) ^ 2 ≤ (p : ℝ) * ∑ i ∈ s, c i ^ 2 :=
  energy_cauchy_schwarz_lower s c p hcard hcsq ((n : ℝ) ^ r) hN

/-- **The moment certificate cannot reach a sub-`n` target (vacuity at scale).** Given the saturation floor
`n^{2r} ≤ p·E` and any target `T` with `0 ≤ T < n` (the prize target `√(2n log q)` is `< n` for all `n > 2 log q`),
the certificate `M^{2r} ≤ p·E` cannot prove `M ≤ T`: indeed `T^{2r} < n^{2r} ≤ p·E`, so the upper bound `p·E` on
`M^{2r}` strictly exceeds `T^{2r}`, leaving `M > T` consistent. The moment/energy route is therefore vacuous for the
prize (which is far below `n`); only the direct sup-norm bound can reach it. -/
theorem moment_certificate_cannot_reach_prize
    (p n r : ℕ) (E T : ℝ) (hr : 1 ≤ r) (hT0 : 0 ≤ T) (hTn : T < (n : ℝ))
    (hfloor : ((n : ℝ) ^ r) ^ 2 ≤ (p : ℝ) * E) :
    T ^ (2 * r) < (p : ℝ) * E := by
  have h2r : 2 * r ≠ 0 := by omega
  have hTlt : T ^ (2 * r) < (n : ℝ) ^ (2 * r) :=
    pow_lt_pow_left₀ hTn hT0 h2r
  have hrw : ((n : ℝ) ^ r) ^ 2 = (n : ℝ) ^ (2 * r) := by
    rw [← pow_mul, mul_comm]
  rw [hrw] at hfloor
  linarith

end ProximityGap.Frontier.MomentSaturation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.MomentSaturation.energy_cauchy_schwarz_lower
#print axioms ProximityGap.Frontier.MomentSaturation.moment_bound_ge_card
#print axioms ProximityGap.Frontier.MomentSaturation.moment_certificate_cannot_reach_prize
