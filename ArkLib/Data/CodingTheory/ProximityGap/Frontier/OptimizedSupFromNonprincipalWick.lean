/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodOptimizedBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.NonprincipalWickIsDCWick

/-!
# The direct optimized `√(n log q)` sup bound from the SATISFIABLE nonprincipal Wick input (#444)

`GaussPeriodOptimizedBound.eta_le_optimized` proves the prize-shape sup-norm bound
`‖η_b‖ ≤ √(2e·n·r)` (at `r ≈ log q`, the `√(n log q)` Gauss-period floor) — but **conditional on the
RAW `GaussianEnergyBound G r`** (`E_r ≤ (2r−1)‼·n^r`), the FULL-spectrum even-moment input. That input
is **FALSE at the prize** (`DCEnergyEssential`: the `b=0` DC term `n^{2r}/q` exceeds the Wick ceiling
once `r > β`). So the deployed direct moment→sup route rests on an unsatisfiable hypothesis.

This file re-grounds the SAME direct, MGF-free optimization on the **satisfiable** input — the
nonprincipal Wick bound `NonprincipalWickBound ψ G r` (`∑_{b≠0}‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r`), which the
live measurement validated sub-char-0 in the prize regime, and which
`NonprincipalWickIsDCWick.nonprincipalWick_iff_dcWick` shows is exactly the in-tree `DCWickBound` crux.
The per-frequency consequence `eta_pow_le_of_nonprincipalWick` (`‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` for `b≠0`)
has the SAME closed form the optimization consumes, so the whole `2r`-th-root / saddle estimate goes
through verbatim — but now for `b ≠ 0` (exactly the `M(n) = max_{b≠0}‖η_b‖` regime) under a hypothesis
consistent at the prize.

* `eta_sq_le_optimized_of_nonprincipalWick` — `‖η_b‖² ≤ 2e·n·r` for `b ≠ 0`, from `NonprincipalWickBound`.
* `eta_le_optimized_of_nonprincipalWick` — `‖η_b‖ ≤ √(2e·n·r)` for `b ≠ 0`; at `r = ⌈log q⌉` this is
  the prize sup-norm target `√(2e·n·log q)` up to the constant `√(2e)` (sharp `√2` needs Stirling).

**Honesty.** NOT a CORE closure. This is the elementary implication
`NonprincipalWickBound at r ≈ log q ⟹ √-cancellation sup-norm`, MGF-free, now on a satisfiable
hypothesis — it does NOT prove the input. The open residual is unchanged: the char-`p` nonprincipal /
DC Wick bound at `r ≈ log q` with an ABSOLUTE constant (the BGK wall; measured `K_eff(n)` drift is the
open `K^r`-slack). Mirrors `eta_le_optimized` exactly, swapping the unsatisfiable raw input for the
satisfiable nonprincipal one. CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.
-/

open Finset
open ArkLib.ProximityGap.GaussPeriodMomentBound ArkLib.ProximityGap.GaussPeriodOptimizedBound
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ProximityGap.Frontier.NonprincipalWickIsDCWick

namespace ProximityGap.Frontier.OptimizedSupFromNonprincipalWick

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


/-- **The nonprincipal even-moment Wick bound with explicit `K^r` slack.** This is the measured
`K_eff` form: the non-DC even moment is bounded by `q · K^r · (2r−1)‼ · |G|^r`.  `K = 1`
recovers `NonprincipalWickBound`; allowing an absolute `K` is the form needed by the prize constant
conversion and by the current reduced-energy measurements. -/
def NonprincipalWickBoundK (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) (K : ℝ) : Prop :=
  ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
    ≤ (Fintype.card F : ℝ) * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))

/-- **`K = 1` embeds the old nonprincipal Wick bound into the explicit-slack form.** -/
theorem nonprincipalWickBoundK_one {ψ : AddChar F ℂ} {G : Finset F} {r : ℕ}
    (h : NonprincipalWickBound ψ G r) : NonprincipalWickBoundK ψ G r 1 := by
  unfold NonprincipalWickBoundK NonprincipalWickBound at *
  simpa using h

/-- **Single-frequency transfer from the `K^r` nonprincipal Wick bound.** A single nonzero frequency
is bounded by the nonprincipal moment total, now with explicit `K^r` slack. -/
theorem eta_pow_le_of_nonprincipalWickK {ψ : AddChar F ℂ} {G : Finset F} {r : ℕ} {K : ℝ}
    (h : NonprincipalWickBoundK ψ G r K) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  have hterm : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) := by
    apply Finset.single_le_sum (f := fun b' => ‖eta ψ G b'‖ ^ (2 * r))
    · intro i _; positivity
    · exact Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  exact hterm.trans h

/-- **Optimized square bound from the `K^r` nonprincipal Wick input.** For every nontrivial frequency,
`NonprincipalWickBoundK ψ G r K` at `r ≥ log q` gives
`‖η_b‖² ≤ 2e · K · |G| · r`.  This is the AddChar-level version of the wf-K1 conversion: an
absolute `K` in the reduced/nonprincipal energy route only changes the final prize constant by
`√K`.  The hard content is still proving the `K^r` input uniformly at prize depth. -/
theorem eta_sq_le_optimized_of_nonprincipalWickK {ψ : AddChar F ℂ}
    {G : Finset F} {r : ℕ} {K : ℝ} (hr : 1 ≤ r) (hK : 0 ≤ K)
    (hrq : Real.log (Fintype.card F) ≤ r) (h : NonprincipalWickBoundK ψ G r K)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq_def
  set nc : ℝ := (G.card : ℝ) with hnc_def
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℕ) ≠ 0 := by omega
  have hqpos : 0 < q := by rw [hq_def]; exact_mod_cast Fintype.card_pos
  have hd0 : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by positivity
  have hKnc : 0 ≤ K * nc := by positivity
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r
      ≤ q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (K * nc) ^ r := by
    rw [← pow_mul]
    have := eta_pow_le_of_nonprincipalWickK h hb
    calc ‖eta ψ G b‖ ^ (2 * r)
        ≤ q * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r)) := this
      _ = q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (K * nc) ^ r := by
          rw [mul_pow]
          ring
  have hstep1 : ‖eta ψ G b‖ ^ 2
      ≤ (q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (K * nc) ^ r) ^ ((r : ℝ)⁻¹) := by
    calc ‖eta ψ G b‖ ^ 2
        = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sq_nonneg _) hrne).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hpow (by positivity)
  have hexpand : (q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (K * nc) ^ r) ^ ((r : ℝ)⁻¹)
      = q ^ ((r : ℝ)⁻¹) * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * (K * nc) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (le_of_lt hqpos) hd0,
        Real.pow_rpow_inv_natCast hKnc hrne]
  rw [hexpand] at hstep1
  have hbq : q ^ ((r : ℝ)⁻¹) ≤ Real.exp 1 := rpow_inv_le_exp_one hqpos hr0 hrq
  have hbd : (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) ≤ 2 * (r : ℝ) := by
    calc (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹)
        ≤ (((2 * r : ℕ) : ℝ) ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow hd0 (doubleFactorial_le_pow r) (by positivity)
      _ = ((2 * r : ℕ) : ℝ) := Real.pow_rpow_inv_natCast (by positivity) hrne
      _ = 2 * (r : ℝ) := by push_cast; ring
  calc ‖eta ψ G b‖ ^ 2
      ≤ q ^ ((r : ℝ)⁻¹) * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * (K * nc) := hstep1
    _ ≤ Real.exp 1 * (2 * (r : ℝ)) * (K * nc) := by gcongr
    _ = 2 * Real.exp 1 * K * nc * (r : ℝ) := by ring

/-- **Optimized norm bound from the `K^r` nonprincipal Wick input.** The reduced-energy `K_eff`
hypothesis gives `‖η_b‖ ≤ √(2e · K · |G| · r)` for `b ≠ 0`.  This is not a CORE closure; the open
BGK/Paley content is the uniform proof of `NonprincipalWickBoundK` at `r ≈ log q`. -/
theorem eta_le_optimized_of_nonprincipalWickK {ψ : AddChar F ℂ}
    {G : Finset F} {r : ℕ} {K : ℝ} (hr : 1 ≤ r) (hK : 0 ≤ K)
    (hrq : Real.log (Fintype.card F) ≤ r) (h : NonprincipalWickBoundK ψ G r K)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ≤ Real.sqrt (2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ)) := by
  have hsq := eta_sq_le_optimized_of_nonprincipalWickK hr hK hrq h hb
  calc ‖eta ψ G b‖ = Real.sqrt (‖eta ψ G b‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ)) := Real.sqrt_le_sqrt hsq

/-- **Optimized per-frequency square bound from the satisfiable nonprincipal Wick input.** For every
nontrivial frequency `b ≠ 0`, `NonprincipalWickBound ψ G r` (at `r ≥ max(1, log q)`) gives
`‖η_b‖² ≤ 2e·n·r`. Same proof as `eta_sq_le_optimized`, with the per-`r` bound supplied by
`eta_pow_le_of_nonprincipalWick` (`‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r`, the same closed form) instead of the
raw-energy `eta_pow_le_of_energyBound`. -/
theorem eta_sq_le_optimized_of_nonprincipalWick {ψ : AddChar F ℂ}
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F) ≤ r) (h : NonprincipalWickBound ψ G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq_def
  set nc : ℝ := (G.card : ℝ) with hnc_def
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℕ) ≠ 0 := by omega
  have hqpos : 0 < q := by rw [hq_def]; exact_mod_cast Fintype.card_pos
  have hd0 : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by positivity
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r := by
    rw [← pow_mul]
    have := eta_pow_le_of_nonprincipalWick h hb
    -- `‖η_b‖^{2r} ≤ q·((2r−1)‼·n^r)`; reassociate to `q·(2r−1)‼·n^r`
    calc ‖eta ψ G b‖ ^ (2 * r)
        ≤ q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r) := this
      _ = q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r := by ring
  -- ‖η‖² ≤ X^{1/r}, then expand the rpow over the product (verbatim from eta_sq_le_optimized)
  have hstep1 : ‖eta ψ G b‖ ^ 2
      ≤ (q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r) ^ ((r : ℝ)⁻¹) := by
    calc ‖eta ψ G b‖ ^ 2
        = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sq_nonneg _) hrne).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hpow (by positivity)
  have hexpand : (q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r) ^ ((r : ℝ)⁻¹)
      = q ^ ((r : ℝ)⁻¹) * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * nc := by
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (le_of_lt hqpos) hd0,
        Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ nc) hrne]
  rw [hexpand] at hstep1
  have hbq : q ^ ((r : ℝ)⁻¹) ≤ Real.exp 1 := rpow_inv_le_exp_one hqpos hr0 hrq
  have hbd : (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) ≤ 2 * (r : ℝ) := by
    calc (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹)
        ≤ (((2 * r : ℕ) : ℝ) ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow hd0 (doubleFactorial_le_pow r) (by positivity)
      _ = ((2 * r : ℕ) : ℝ) := Real.pow_rpow_inv_natCast (by positivity) hrne
      _ = 2 * (r : ℝ) := by push_cast; ring
  calc ‖eta ψ G b‖ ^ 2
      ≤ q ^ ((r : ℝ)⁻¹) * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * nc := hstep1
    _ ≤ Real.exp 1 * (2 * (r : ℝ)) * nc := by gcongr
    _ = 2 * Real.exp 1 * nc * (r : ℝ) := by ring

/-- **The optimized Gauss-period bound from the satisfiable nonprincipal input (norm form).** For
`b ≠ 0`, `‖η_b‖ ≤ √(2e·n·r)` — the square-root-cancellation sup-norm, conditional on
`NonprincipalWickBound ψ G r` at `r ≥ max(1, log q)` (the SATISFIABLE prize input, = `DCWickBound`).
At `r = ⌈log q⌉` this is `‖η_b‖ ≤ √(2e·n·log q)(1+o(1))` — the prize target up to `√(2e)`. The
MGF-free, direct moment→sup route, now resting on a hypothesis consistent at the prize (the raw
`eta_le_optimized` input is false there). -/
theorem eta_le_optimized_of_nonprincipalWick {ψ : AddChar F ℂ}
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F) ≤ r) (h : NonprincipalWickBound ψ G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) := by
  have hsq := eta_sq_le_optimized_of_nonprincipalWick hr hrq h hb
  calc ‖eta ψ G b‖ = Real.sqrt (‖eta ψ G b‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) := Real.sqrt_le_sqrt hsq

end ProximityGap.Frontier.OptimizedSupFromNonprincipalWick

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.OptimizedSupFromNonprincipalWick.nonprincipalWickBoundK_one
#print axioms ProximityGap.Frontier.OptimizedSupFromNonprincipalWick.eta_pow_le_of_nonprincipalWickK
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.OptimizedSupFromNonprincipalWick.eta_sq_le_optimized_of_nonprincipalWickK
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.OptimizedSupFromNonprincipalWick.eta_le_optimized_of_nonprincipalWickK
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.OptimizedSupFromNonprincipalWick.eta_sq_le_optimized_of_nonprincipalWick
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.OptimizedSupFromNonprincipalWick.eta_le_optimized_of_nonprincipalWick
