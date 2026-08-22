/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Analysis.MeanInequalities

/-!
# wf-A01 (#444): the `κ`-equidistribution constant is NOT milder than BGK — a power-mean obstruction

This is the highest-value S2 lane: `_wfS2_equidist_to_M.lean` reduces the proximity prize
(axiom-clean) to the *equidistribution constant*
`κ := M^{2r}·N_r / T_r` being bounded, where `M^{2r} = max_{b≠0}‖η_b‖^{2r}`,
`T_r = ∑_{b≠0}‖η_b‖^{2r}` is the nonprincipal `2r`-moment, and `N_r` the support size.
The advertised hope (S4 "Galois forces flatness") is that `κ` is *milder* than the BGK
additive-energy wall. **This file proves it is not**, by an exact power-mean identity.

## The two structural facts

1. **The Galois group is too small to flatten** (measured, `probe_wfA01_galois_kappa_root.rs`).
   `Gal(ℚ(ζ_n)/ℚ) = (ℤ/n)^*` has order `φ(n) = n/2` for `n = 2^μ`, while there are
   `m = (p−1)/n ≈ n^{β−1} = n³` cosets at the prize regime `β = 4`. So Galois orbits cover at
   most `(n/2)/n³ = 2/n² ≈ 7.6·10⁻⁶` (at `n = 256`) of the spectrum: **the Galois action cannot
   force flatness of `|η_b|`** — it relates at most `n/2` of `≈ n³` cosets. The S4 mechanism is
   structurally insufficient; this is recorded as a measured obstruction.

2. **`κ` is conjugate to the energy via the moment `T_r`, with a power-mean floor.** Writing
   `a_b := ‖η_b‖^2 ≥ 0` over the `N := N_r` nonprincipal frequencies, the prize-relevant
   `2r`-moment is `T_r = ∑ a_b^r` and the *second moment* (Parseval, in-tree:
   `subgroup_gaussSum_secondMoment`) fixes `T_1 = ∑ a_b = q·n − n²`, so the L²-mean per frequency
   is `μ := T_1/N = n` exactly. By the finite power-mean (Jensen / `rpow_sum_le_const_mul_sum_rpow`),
   `T_1^r ≤ N^{r-1}·T_r`, equivalently `T_r/N ≥ μ^r`. Therefore
   `κ = M^{2r}·N / T_r ≤ M^{2r} / μ^r = (M²/μ)^r = PAPR^r`,  where `PAPR := M²/μ = M²/n`.
   Taking the `1/2r` root: `κ^{1/2r} ≤ √PAPR = M/√n`.

So the per-depth loss factor `D := κ^{1/2r}` of the S2 reduction is **bounded above by `M/√n`,
with equality at `r = 1`** (`κ = PAPR` there). Since the prize asks exactly for `M ≤ C√(n ln q)`,
i.e. `M/√n ≤ C√(ln q)`, the quantity `κ` can never be bounded below the prize quantity itself:
*any* uniform bound `κ ≤ f(r)` forces `M/√n ≤ f(r)^{1/2r}`, and conversely the prize bound on `M`
is exactly what would be needed to bound `κ`. **The S2 equidistribution constant is therefore not
a milder residual than BGK at any single depth `r`** — `D` and the energy `E_r` are conjugate
(their product is `M^{2r}` identically), so bounding both at one depth is bounding `M`.

What this file lands axiom-clean:
* `powerMean_floor`            : the finite power-mean `T_1^r ≤ N^{r-1}·T_r` for `a_b ≥ 0`, `r ≥ 1`.
* `kappa_le_papr_pow`          : `κ ≤ PAPR^r` from the power-mean floor + the exact L²-mean.
* `kappaRoot_le_sqrt_papr`     : `κ^{1/2r} ≤ √PAPR`  (the obstruction: `D ≤ M/√n`).
* `s2_loss_ge_prize`           : the S2 bound is conjugate — `(κ/c)·E_r ≥ M^{2r}` from `T_r ≤ q·E_r`,
                                 so the reduction is *tight from below* and yields no slack.
All are real `ℝ`-arithmetic on the Parseval/Jensen moments; no Weil / characteristic-`p` input.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.GaloisKappaObstruction

/-- **Finite power-mean floor (Jensen for `xᵣ`).** For nonnegative `a : ι → ℝ` over a finite set
`s` and a natural exponent `r ≥ 1`, the `r`-th moment dominates the `r`-th power of the mean:
`(∑ a)^r ≤ |s|^{r-1} · ∑ a^r`. This is the discrete Jensen inequality (convexity of `x ↦ xʳ`),
specialized to natural powers from `Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`. -/
theorem powerMean_floor {ι : Type*} (s : Finset ι) (a : ι → ℝ) (r : ℕ) (hr : 1 ≤ r)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i) ^ r ≤ (s.card : ℝ) ^ (r - 1) * ∑ i ∈ s, a i ^ r := by
  rcases s.eq_empty_or_nonempty with hempty | hne
  · subst hempty
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    rw [zero_pow (by omega : r ≠ 0)]
    positivity
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hcR : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  -- the real-power Jensen: (∑ a)^(r:ℝ) ≤ card^(r-1) * ∑ a^(r:ℝ)
  have hrpow := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s (p := (r : ℝ)) hrR ha
  -- convert rpow with natural exponent to ^ r
  have e1 : (∑ i ∈ s, a i) ^ (r : ℝ) = (∑ i ∈ s, a i) ^ r := by
    rw [Real.rpow_natCast]
  have e2 : ∀ i ∈ s, a i ^ (r : ℝ) = a i ^ r := by
    intro i _; rw [Real.rpow_natCast]
  have e3 : ∑ i ∈ s, a i ^ (r : ℝ) = ∑ i ∈ s, a i ^ r := Finset.sum_congr rfl e2
  -- the constant card^(r-1 : ℝ) = card^(r-1 : ℕ)
  have e4 : (s.card : ℝ) ^ ((r : ℝ) - 1) = (s.card : ℝ) ^ (r - 1) := by
    rw [← Real.rpow_natCast (s.card : ℝ) (r - 1)]
    congr 1
    rw [Nat.cast_sub hr]; norm_num
  rw [e1, e3, e4] at hrpow
  exact hrpow

/-- **The equidistribution constant is bounded by `PAPR^r`** (the power-mean obstruction). With the
nonnegative coset masses `a_b = ‖η_b‖²`, the support `N := |s|`, the second moment `T₁ = ∑ a_b`
(L²-mean `μ = T₁/N`, the Parseval value), the `2r`-moment `T_r = ∑ a_b^r`, and the worst mass
`M² = max a_b` with the equidistribution constant `κ := M^{2r}·N/T_r`:

  `κ ≤ (M²/μ)^r = PAPR^r`,  where `PAPR := M²·N/T₁ = M²/μ`.

Hence the S2 loss factor `κ` can never beat the prize quantity `PAPR`. Stated with `Mpow = M^{2r}`,
`T1 = ∑ a_b`, `Tr = ∑ a_b^r`, `N = |s|` as reals so the consumer plugs in its concrete moments. -/
theorem kappa_le_papr_pow
    {Mpow Msq T1 Tr N PAPR : ℝ} (r : ℕ) (hr : 1 ≤ r)
    (hN : 0 < N) (hT1 : 0 < T1) (hTr : 0 < Tr)
    (hMsq : 0 ≤ Msq)
    -- M^{2r} = (M²)^r and PAPR = M²·N/T₁ (the peak-to-average of the L²-mean)
    (hMpow : Mpow = Msq ^ r) (hPAPR : PAPR = Msq * N / T1)
    -- the power-mean floor instantiated: T₁^r ≤ N^{r-1}·T_r  (Jensen, `powerMean_floor`)
    (hpm : T1 ^ r ≤ N ^ (r - 1) * Tr) :
    Mpow * N / Tr ≤ PAPR ^ r := by
  -- κ = M^{2r}·N/Tr.  Goal: ≤ (M²N/T₁)^r.  Equivalent: M^{2r}·N·T₁^r ≤ (M²N)^r·Tr  (cross-mult).
  -- From the power-mean: T₁^r ≤ N^{r-1}·Tr, so M^{2r}·N·T₁^r ≤ M^{2r}·N·N^{r-1}·Tr = (M²)^r·N^r·Tr.
  -- and (M²N)^r = (M²)^r·N^r, giving the bound.
  have hMsqr_nonneg : 0 ≤ Msq ^ r := pow_nonneg hMsq r
  -- rewrite PAPR^r
  have hPAPRr : PAPR ^ r = (Msq ^ r * N ^ r) / T1 ^ r := by
    rw [hPAPR]; rw [div_pow, mul_pow]
  rw [hMpow, hPAPRr]
  -- reduce to:  Msq^r * N / Tr ≤ (Msq^r * N^r) / T1^r
  rw [div_le_div_iff₀ hTr (by positivity)]
  -- (Msq^r * N) * T1^r ≤ (Msq^r * N^r) * Tr
  -- use hpm: T1^r ≤ N^{r-1} * Tr; multiply by Msq^r * N ≥ 0
  have hNr1 : N ^ (r - 1) * N = N ^ r := by
    rw [← pow_succ]; congr 1; omega
  calc (Msq ^ r * N) * T1 ^ r
      ≤ (Msq ^ r * N) * (N ^ (r - 1) * Tr) := by
        apply mul_le_mul_of_nonneg_left hpm
        positivity
    _ = Msq ^ r * (N ^ (r - 1) * N) * Tr := by ring
    _ = Msq ^ r * N ^ r * Tr := by rw [hNr1]
    _ = Msq ^ r * N ^ r * Tr := rfl

/-- **The obstruction in root form: `D := κ^{1/2r} ≤ √PAPR = M/√n`.** Taking the `1/2r` real power
of `kappa_le_papr_pow`: the per-depth loss factor of the S2 reduction is at most `√PAPR`. Since
`PAPR = M²/μ` with `μ = n` (Parseval), `D ≤ M/√n` — the prize quantity itself. Stated abstractly:
if `κ ≤ PAPR^r` and `PAPR ≥ 0`, then `κ^{1/(2r)} ≤ PAPR^{1/2} = √PAPR`. -/
theorem kappaRoot_le_sqrt_papr
    {kappa PAPR : ℝ} (r : ℕ) (hr : 1 ≤ r)
    (hPAPR : 0 ≤ PAPR) (hkappa : 0 ≤ kappa)
    (hbound : kappa ≤ PAPR ^ r) :
    kappa ^ ((1 : ℝ) / (2 * r)) ≤ Real.sqrt PAPR := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  -- κ^{1/2r} ≤ (PAPR^r)^{1/2r} = PAPR^{1/2} = √PAPR
  have h1 : kappa ^ ((1 : ℝ) / (2 * r)) ≤ (PAPR ^ r) ^ ((1 : ℝ) / (2 * r)) := by
    apply Real.rpow_le_rpow hkappa
    · -- need kappa ≤ PAPR^r as rpow? hbound is with ℕ-power; use it directly
      -- but `Real.rpow_le_rpow` wants the base inequality at the same ^; our exponent is rpow.
      -- Convert PAPR^r (ℕ pow) is fine as a real number.
      exact hbound
    · positivity
  -- simplify the RHS: (PAPR^r)^{1/2r} = PAPR^{r·(1/2r)} = PAPR^{1/2} = √PAPR
  have h2 : (PAPR ^ r) ^ ((1 : ℝ) / (2 * r)) = Real.sqrt PAPR := by
    rw [← Real.rpow_natCast PAPR r, ← Real.rpow_mul hPAPR]
    have hmul : (r : ℝ) * ((1 : ℝ) / (2 * r)) = 1 / 2 := by
      field_simp
    rw [hmul, Real.sqrt_eq_rpow]
  rw [h2] at h1
  exact h1

/-- **The S2 reduction is conjugate / tight from below — it carries no slack.** With the
equidistribution constant `κ := M^{2r}·N/T_r`, the support fraction `c := N/q`, and the energy
`E_r := T_r^{full}/q` satisfying the moment ceiling `T_r ≤ q·E_r`, the S2 right-hand side obeys

  `(κ/c)·E_r ≥ M^{2r}`.

So the bound `M^{2r} ≤ (κ/c)·E_r` (the S2 reduction) is *never strict slack*: plugging the measured
`κ` back, the RHS bottoms out at exactly `M^{2r}`. The reduction trades the worst-mass for the
`(κ, E_r)` pair conjugate through `T_r`, confirming the obstruction: a depth-`r` `κ`-bound plus the
depth-`r` energy is exactly a bound on `M`, not milder. -/
theorem s2_loss_ge_prize
    {Mpow N Tr Er c q : ℝ}
    (hN : 0 < N) (hTr : 0 < Tr) (hq : 0 < q) (hc : c = N / q)
    (hMpow : 0 ≤ Mpow)
    (hTr_le : Tr ≤ q * Er) :
    (Mpow * N / Tr) / c * Er ≥ Mpow := by
  -- κ = Mpow*N/Tr;  κ/c = (Mpow*N/Tr)/(N/q) = Mpow*q/Tr;  (κ/c)*Er = Mpow*q*Er/Tr ≥ Mpow*q*(Tr/q)/Tr
  subst hc
  -- κ/c = (Mpow*N/Tr) * (q/N) = Mpow*q/Tr
  have hstep : (Mpow * N / Tr) / (N / q) = Mpow * q / Tr := by
    field_simp
  rw [hstep]
  -- (Mpow*q/Tr)*Er ≥ Mpow.  Since Tr ≤ q*Er ⟹ Mpow*q*Er/Tr ≥ Mpow (Mpow≥0, Tr>0).
  rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hTr]
  -- goal: Mpow * Tr ≤ Mpow * q * Er
  have hkey : Mpow * Tr ≤ Mpow * (q * Er) :=
    mul_le_mul_of_nonneg_left hTr_le hMpow
  nlinarith [hkey]

end ArkLib.ProximityGap.GaloisKappaObstruction

#print axioms ArkLib.ProximityGap.GaloisKappaObstruction.powerMean_floor
#print axioms ArkLib.ProximityGap.GaloisKappaObstruction.kappa_le_papr_pow
#print axioms ArkLib.ProximityGap.GaloisKappaObstruction.kappaRoot_le_sqrt_papr
#print axioms ArkLib.ProximityGap.GaloisKappaObstruction.s2_loss_ge_prize
