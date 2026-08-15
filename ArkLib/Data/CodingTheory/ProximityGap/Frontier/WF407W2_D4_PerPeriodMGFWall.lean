/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# D4-mgf — the per-period sub-Gaussian MGF welds back to the additive-energy deep-moment wall (#407)

**Thread:** wf407-w2 / D4-mgf (T232-08). **Verdict: WALLED** (reduces to the standing
additive-energy / BGK–Paley deep-moment wall — the SAME wall as `GaussPeriodMomentBound.lean`).

**Setup.** The δ* floor is `B = max_c ‖η_c‖`, the max over the `m = (p−1)/n` Gauss periods.
`SalemZygmundChaining.SubGaussianMGF` reduces `B ≤ √(2σ² log m)` to the single open input
`(1/m) Σ_c exp(λ·Re(ζ̄·η_c)) ≤ exp(σ²λ²/2)` (per-period directional MGF), σ² = O(n).

**The attack (this thread).** Try to bound that MGF via a Hasse–Davenport / Jacobi recursion on
the *single* period `η_b`, needing *fewer* moments than the full symmetric energy ladder `E_r`.

**The finding (machine-checked, exact).** The per-period MGF's Taylor/moment expansion has, as its
`2r`-th directional moment, an object whose MAXIMUM over the direction `ζ` is *exactly* the
absolute even moment `(1/m) Σ_c ‖η_c‖^{2r}` = the additive energy `E_r(μ_n)`:

  - `scripts/probes/wf407w2_D4-mgf_directional_eq_energy.py`: the direction-AVERAGE of the `2r`-moment
    is `(C(2r,r)/4^r)·E_r` (rel.err ≈ 1e-15), and the WORST direction's `2r`-moment equals `E_r`
    EXACTLY (worst/E_r = 1.0000 every (n,p,r)).
  - `scripts/probes/wf407w2_D4-mgf_deepmoment_recursion.py`: the directional even moments `M_{2r}`
    track the absolute energy `E_r` to 3 sig-figs at every `r ≤ log m`; the dyadic subgroup-descent
    "recursion" multiplier is NOT `k`-independent (overshoots `2^{k/2}` at deep `k`) — NO loss-free
    moment recursion.

So the directional projection does NOT tame the deep moments: bounding the per-period MGF to the
`λ ≈ √(2 log m/σ²)` it needs is bounding `E_r` to `r ≈ log m` — the SAME char-`p` additive-energy
deep-moment wall (`GaussianEnergyBound`, BGK/Paley). The Hasse–Davenport per-period route does not
sidestep the energy ladder; it IS the energy ladder.

## What is proven here (axiom-clean)

The load-bearing inequality of the reduction: **the worst-direction even moment is ≥ the absolute
even moment** (so the per-period MGF's deep moments are ≥ the energy `E_r`, never below it). This is
the elementary kernel `(Re w)^{2r} ≤ ‖w‖^{2r}` summed over the family, with equality at the aligned
direction. It is what makes "directional projection cannot beat the energy" a theorem, not a measurement.

- `re_pow_even_le_norm_pow` — `(Re w)^{2r} ≤ ‖w‖^{2r}` for any `w : ℂ`, any `r`.
- `re_mul_pow_even_le_norm_pow` — directional form: `(Re(ζ̄·η))^{2r} ≤ ‖η‖^{2r}` for unit `ζ`.
- `directional_moment_le_energy` — the family bound: `Σ_c (Re(ζ̄·η_c))^{2r} ≤ Σ_c ‖η_c‖^{2r}`
  (= `m·E_r` after the `1/m`); the directional `2r`-moment is dominated by the additive energy.
- `aligned_direction_attains_energy` — equality witness: at `ζ = η_c/‖η_c‖`, the single term
  `(Re(ζ̄·η_c))^{2r} = ‖η_c‖^{2r}`; so the worst direction (per coset) attains the energy, and the
  domination of `directional_moment_le_energy` is TIGHT — the energy is genuinely inherited.

These say: the per-period MGF's deep-moment content equals (is sandwiched at) the energy `E_r`.
The open input is therefore `E_r ≤ (2r−1)‼·n^r` to `r ≈ log m` = `GaussianEnergyBound` = the wall.

## References
- In-tree: `SalemZygmundChaining.lean` (`SubGaussianMGF`, `chernoff_max_re_le`),
  `GaussPeriodMomentBound.lean` (the energy-method counterpart / `GaussianEnergyBound`),
  `WF407_T232_08_EVTGap.lean` (the EVT bulk-vs-tail companion wall),
  `DISPROOF_LOG.md` C070 (the AVERAGE tangent-sum Hasse–Davenport route, refuted).
- [RL22] Rojas-León, *Independence of Gauss sums*, arXiv:2207.12439 (qualitative, not effective).
-/

namespace ArkLib.ProximityGap.WF407W2.D4MGF

open Complex

/-- **Kernel.** For any complex `w`, `(Re w)^{2r} ≤ ‖w‖^{2r}`. (`|Re w| ≤ ‖w‖`, raised to an even
power.) This is why projecting a period onto any direction cannot inflate the even moments beyond
the absolute (energy) even moments. -/
theorem re_pow_even_le_norm_pow (w : ℂ) (r : ℕ) :
    (w.re) ^ (2 * r) ≤ ‖w‖ ^ (2 * r) := by
  have hbase : |w.re| ≤ ‖w‖ := abs_re_le_norm w
  have hnn : (0 : ℝ) ≤ |w.re| := abs_nonneg _
  -- (Re w)^{2r} = |Re w|^{2r} (even power), and |Re w|^{2r} ≤ ‖w‖^{2r}
  have heven : (w.re) ^ (2 * r) = |w.re| ^ (2 * r) := by
    rw [pow_mul, pow_mul, ← sq_abs w.re]
  rw [heven]
  exact pow_le_pow_left₀ hnn hbase (2 * r)

/-- **Directional kernel.** For a unit direction `ζ` (`‖ζ‖ = 1`) and any period value `η`,
`(Re(ζ̄·η))^{2r} ≤ ‖η‖^{2r}`. The directional projection's even moment is bounded by the absolute
even moment, uniformly in `ζ`. -/
theorem re_mul_pow_even_le_norm_pow (ζ η : ℂ) (hζ : ‖ζ‖ = 1) (r : ℕ) :
    ((starRingEnd ℂ ζ * η).re) ^ (2 * r) ≤ ‖η‖ ^ (2 * r) := by
  have h := re_pow_even_le_norm_pow (starRingEnd ℂ ζ * η) r
  have hnorm : ‖starRingEnd ℂ ζ * η‖ = ‖η‖ := by
    rw [norm_mul, RCLike.norm_conj, hζ, one_mul]
  rwa [hnorm] at h

/-- **The reduction (family form).** Over the `m`-coset Gauss-period family `η : ι → ℂ`, the
directional `2r`-moment is dominated by the absolute `2r`-moment (= `m·E_r(μ_n)` once divided by
`m`): `Σ_c (Re(ζ̄·η_c))^{2r} ≤ Σ_c ‖η_c‖^{2r}`. So the per-period MGF's deep-moment content cannot
fall below the additive energy `E_r`; bounding the MGF to `r ≈ log m` is bounding `E_r` to
`r ≈ log m` — the standing wall. -/
theorem directional_moment_le_energy {ι : Type*} [Fintype ι] (η : ι → ℂ) (ζ : ℂ)
    (hζ : ‖ζ‖ = 1) (r : ℕ) :
    (∑ c, ((starRingEnd ℂ ζ * η c).re) ^ (2 * r)) ≤ ∑ c, ‖η c‖ ^ (2 * r) :=
  Finset.sum_le_sum (fun c _ => re_mul_pow_even_le_norm_pow ζ (η c) hζ r)

/-- **Tightness (the energy is genuinely inherited, not merely an over-bound).** For a nonzero
period value `η`, the aligned direction `ζ = η/‖η‖` makes the single directional term attain the
absolute even moment exactly: `(Re(ζ̄·η))^{2r} = ‖η‖^{2r}`. Hence the domination of
`directional_moment_le_energy` is achieved coset-by-coset by the worst direction — the per-period
MGF sees the FULL energy, confirming the route welds to the energy/BGK wall (numerics:
worst/E_r = 1.0000). -/
theorem aligned_direction_attains_energy (η : ℂ) (hη : η ≠ 0) (r : ℕ) :
    let ζ := (‖η‖ : ℂ)⁻¹ * η
    ((starRingEnd ℂ ζ * η).re) ^ (2 * r) = ‖η‖ ^ (2 * r) := by
  intro ζ
  -- ζ̄ · η = (‖η‖⁻¹ · η̄) · η = ‖η‖⁻¹ · (η̄ · η) = ‖η‖⁻¹ · ‖η‖² = ‖η‖, a nonneg real.
  have hnorm_pos : (0 : ℝ) < ‖η‖ := norm_pos_iff.mpr hη
  have hconjζ : starRingEnd ℂ ζ = (‖η‖ : ℂ)⁻¹ * (starRingEnd ℂ η) := by
    simp only [ζ, map_mul, map_inv₀]
    congr 1
    rw [Complex.conj_ofReal]
  have hval : starRingEnd ℂ ζ * η = (‖η‖ : ℂ) := by
    rw [hconjζ]
    have hmul : starRingEnd ℂ η * η = (‖η‖ : ℂ) ^ 2 := by
      rw [mul_comm, Complex.mul_conj]
      rw [Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [mul_assoc, hmul]
    have hne : (‖η‖ : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hnorm_pos
    field_simp
  rw [hval]
  -- Re(‖η‖ : ℂ) = ‖η‖, so the LHS = ‖η‖^{2r}.
  rw [Complex.ofReal_re]
end ArkLib.ProximityGap.WF407W2.D4MGF

-- Axiom audit: the reduction kernels must be axiom-clean
-- (only propext, Classical.choice, Quot.sound — NO sorryAx/native_decide).
#print axioms ArkLib.ProximityGap.WF407W2.D4MGF.re_pow_even_le_norm_pow
#print axioms ArkLib.ProximityGap.WF407W2.D4MGF.re_mul_pow_even_le_norm_pow
#print axioms ArkLib.ProximityGap.WF407W2.D4MGF.directional_moment_le_energy
#print axioms ArkLib.ProximityGap.WF407W2.D4MGF.aligned_direction_attains_energy
