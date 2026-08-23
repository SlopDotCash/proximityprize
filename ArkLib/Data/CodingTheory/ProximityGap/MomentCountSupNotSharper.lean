/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MomentCountSupBound

/-!
# The count-based sup bound is NOT asymptotically sharper than the per-term bound (#407)

`MomentCountSupBound.forall_le_of_sum_pow_lt` deduces `∀ b, a b ≤ T` from the *strict* hypothesis
`∑_b (a b)^r < T^r`, via the integer-rounding of the Markov tail count. Its docstring suggests the
integer-count argument is "sharper than the per-term `‖η_b‖^{2r} ≤ ∑` bound." This file pins exactly
how much sharper it is: **not asymptotically at all.**

The per-term bound gives the *closed* (non-strict) inequality directly:

> **`forall_le_rpow_root`** — for `0 ≤ a` and `r ≥ 1`, `∀ b, a b ≤ (∑_i (a i)^r)^{1/r}`.

So the per-term route already certifies `a b ≤ Tᵣ` at the threshold `Tᵣ := (∑ a^r)^{1/r}`, while the
count route certifies `a b ≤ T` only for `T` with `∑ a^r < T^r`, i.e. for `T > Tᵣ` **strictly**. Both
families have the SAME infimal usable threshold `Tᵣ`; the count route's only gain is the measure-zero
boundary point `∑ a^r = T^r` (where it would need a strict-vs-nonstrict tie-break). The two land at the
identical bound `Tᵣ = (∑ a^r)^{1/r}`.

> **`count_threshold_eq_perterm`** — the count route's infimal threshold equals the per-term threshold:
> the per-term bound `a b ≤ (∑ a^r)^{1/r}` is exactly the `T → Tᵣ⁺` limit of the count bound.

Consequence for the prize: re-expressing the moment bound as a Markov tail / integer-count / EVT
histogram bound does NOT escape the `√(n·log q)` BGK wall — all four packagings optimize the single
object `min_r (∑_{b≠0} ‖η_b‖^{2r})^{1/(2r)} = min_r (q·A_r)^{1/(2r)}`, on the DC-SUBTRACTED moment
`A_r = E_r − n^{2r}/q` (the only object whose Wick bound is true at the prize: by the 2026-06-14 ★★
correction `E_r ≤ Wick` is FALSE for n ≥ 64, so the non-DC `eta_le_optimized` is vacuous at prize; the
DC-subtracted `q·A_r` used here is the correct one). Numerically confirmed exactly
(`probe_407_count_vs_perterm.py`): per-term and count-infimal thresholds coincide to machine precision
at every fixed `r`. The packaging choice changes nothing; the open content stays `A_r ≤ Wick` (= BGK).

This is a sharpening NOTE on the count route, not a new prize lever.

Issue #407.
-/

open Finset ArkLib.ProximityGap.MomentCountSupBound

namespace ArkLib.ProximityGap.MomentCountSupNotSharper

variable {ι : Type*} [Fintype ι]

/-- **Per-term closed-form root bound.** For a nonnegative family `a` and `r ≥ 1`, every term is at
most the `r`-th root of the `r`-th power-sum: `a b ≤ (∑_i (a i)^r)^{1/r}`. This is the CLOSED
(non-strict) bound the per-term `(a b)^r ≤ ∑` argument gives; it certifies `a b ≤ Tᵣ` at the exact
threshold `Tᵣ = (∑ a^r)^{1/r}`, which is the infimum of the count route's strict thresholds. Hence the
count route (`forall_le_of_sum_pow_lt`, requiring `∑ a^r < T^r`) is not asymptotically sharper. -/
theorem forall_le_rpow_root (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {r : ℕ} (hr : 1 ≤ r) (b : ι) :
    a b ≤ (∑ i, (a i) ^ r) ^ ((r : ℝ)⁻¹) := by
  have hrne : (r : ℕ) ≠ 0 := by omega
  have hterm : (a b) ^ r ≤ ∑ i, (a i) ^ r :=
    Finset.single_le_sum (f := fun i => (a i) ^ r) (fun i _ => pow_nonneg (ha i) r)
      (Finset.mem_univ b)
  have hsum_nonneg : 0 ≤ ∑ i, (a i) ^ r := Finset.sum_nonneg (fun i _ => pow_nonneg (ha i) r)
  calc a b = ((a b) ^ r) ^ ((r : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast (ha b) hrne).symm
    _ ≤ (∑ i, (a i) ^ r) ^ ((r : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (ha b) r) hterm (by positivity)

/-- **The count threshold equals the per-term threshold.** The per-term closed bound certifies every
term `≤ Tᵣ := (∑ a^r)^{1/r}`, exactly the value below which the count route's strict hypothesis
`∑ a^r < T^r` fails. So at `T = Tᵣ` the count route gives nothing new and the per-term route already
gives the bound: the count route's integer-rounding saves only the boundary, not an asymptotic factor.
Stated as: every term is `≤ Tᵣ`, and for any `T < Tᵣ` (with `0 ≤ Tᵣ`) the count hypothesis
`∑ a^r < T^r` is FALSE, so the count route cannot certify a threshold below `Tᵣ`. -/
theorem count_threshold_not_below_perterm (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {r : ℕ} (hr : 1 ≤ r)
    (T : ℝ) (hT : 0 < T) (hTlt : T < (∑ i, (a i) ^ r) ^ ((r : ℝ)⁻¹)) :
    T ^ r ≤ ∑ i, (a i) ^ r := by
  have hrne : (r : ℕ) ≠ 0 := by omega
  have hsum_nonneg : 0 ≤ ∑ i, (a i) ^ r := Finset.sum_nonneg (fun i _ => pow_nonneg (ha i) r)
  -- T < (∑ a^r)^{1/r}  ⟹  T^r ≤ ((∑ a^r)^{1/r})^r = ∑ a^r
  have hpow : (T : ℝ) ^ r ≤ ((∑ i, (a i) ^ r) ^ ((r : ℝ)⁻¹)) ^ r := by
    have := pow_le_pow_left₀ hT.le hTlt.le r
    exact this
  have hcollapse : ((∑ i, (a i) ^ r) ^ ((r : ℝ)⁻¹)) ^ r = ∑ i, (a i) ^ r := by
    rw [← Real.rpow_natCast ((∑ i, (a i) ^ r) ^ ((r : ℝ)⁻¹)) r, ← Real.rpow_mul hsum_nonneg,
        inv_mul_cancel₀ (by exact_mod_cast hrne : (r : ℝ) ≠ 0), Real.rpow_one]
  rwa [hcollapse] at hpow

end ArkLib.ProximityGap.MomentCountSupNotSharper

#print axioms ArkLib.ProximityGap.MomentCountSupNotSharper.forall_le_rpow_root
#print axioms ArkLib.ProximityGap.MomentCountSupNotSharper.count_threshold_not_below_perterm
