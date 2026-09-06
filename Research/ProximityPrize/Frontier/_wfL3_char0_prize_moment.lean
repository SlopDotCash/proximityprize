/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DyadicEnergyK1
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodOptimizedBound

/-!
# L3: the FULL char-0 prize moment bound as ONE unconditional theorem (#444, lane wf-L3)

## What this lane assembles

The char-0 face of the Proximity-Prize per-frequency core is **essentially proven across pieces**:

* **the energy bound** `E_r(μ_{2^k}) ≤ (2r−1)‼·n^r` (Lam–Leung), formalized UNCONDITIONALLY in
  `DyadicEnergyK1.zeroSumCount_le_doubleFactorial_dyadic` (the antipodal-pairing residual `H` is
  *discharged* in char 0 by `LamLeungMultisetAntipodal` + the index-involution lift);
* **the moment → sup telescope at depth `r ≈ ln q`**, the field-independent real-analysis saddle
  `GaussPeriodOptimizedBound.{doubleFactorial_le_pow, rpow_inv_le_exp_one}` that turns a per-frequency
  `2r`-th moment bound into the prize square-root shape with the explicit constant `√(2e)`.

This file *welds those into a single named unconditional theorem*, `char0_prize_moment_bound`, so that
"the char-0 prize is proven" becomes one citable statement rather than a chain the reader must reconstruct.

## What "char-0" means here (the formal complex period model — read this before citing)

The smooth domain is `G ⊆ μ_{2^k}`, the `2^k`-th roots of unity, taken inside a **characteristic-zero
field** `L` (concretely `L = ℂ ⊇ ℤ[ζ_{2^k}]`; NO mod-`p` reduction). In this model:

* the additive energy `E_r(G)` is the genuine integer count of zero-sum `2r`-tuples
  (`NegationClosedWalk.zeroSumCount G (2r)`), and the Lam–Leung bound holds *unconditionally*
  (this is what `zeroSumCount_le_doubleFactorial_dyadic` proves — no Sidon/repThree hypothesis);
* a **formal period vector** has some count `Q ≥ 1` of frequencies and its sup `M := max_b‖η_b‖`
  obeys the moment-to-sup inequality `M^{2r} ≤ Q · E_r(G)` — this is the *definition* of the model,
  the single term ≤ the full `2r`-th moment `Σ_b‖η_b‖^{2r} = Q·E_r`. (In the finite-field instantiation
  `L = F_q`, `Q = q` and this inequality is the PROVEN `SubgroupGaussSumMoment.subgroup_gaussSum_moment`
  composed with `Finset.single_le_sum`; it carries no open content — it is field-independent counting.)

Under exactly these two ingredients the saddle yields `M ≤ √(2e · n · r)`, and at the optimal depth
`r = ⌈ln Q⌉` this is the prize bound `M ≤ √(2e) · √(n · ⌈ln Q⌉)` — the Gaussian/Ramanujan
per-frequency target up to the constant `√(2e)` (the sharp `√2` needs Stirling for `(2r−1)‼`).

## The SOLE gap to the full prize

The ONLY thing this theorem does NOT cover is the **char-`p` transfer**: replaying the Lam–Leung
energy bound in `F_q` (`q = p = Θ(n^β)`) at depth `r ≈ ln q`. The char-0 energy bound transfers to
`F_p` only while `p` exceeds the cyclotomic-norm threshold `p > (2r)^{φ(n)} = (2r)^{n/2}` (no short
`±1`-relation of `2^μ`-th roots vanishes mod `p`); this holds for `n < 2 log q / log log q ≈ 40` but
is OPEN at the prize scale `n = 2^30`, `q = 2^158`. That single transfer is the entire BGK wall; every
other ingredient of the per-frequency prize is proven here in char 0.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

set_option linter.style.longLine false


open Finset Nat
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.GaussPeriodOptimizedBound

namespace ArkLib.ProximityGap.Frontier.WFL3

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-! ## The abstract saddle (field-independent, the moment → sup telescope) -/

/-- **The abstract moment → prize saddle, axiom-clean.** From a per-frequency `2r`-th moment bound
`M^{2r} ≤ Q · (2r−1)‼ · n^r` (the formal-period moment identity composed with the char-0 energy
bound), at optimal depth `r ≥ max(1, log Q)`, the sup obeys the prize square-root shape
`M ≤ √(2e · n · r)`.

This is the field-independent kernel of `GaussPeriodOptimizedBound.eta_sq_le_optimized`, isolated so
the char-0 assembly does not need the finite-field `eta`/`subgroup_gaussSum_moment` machinery. It uses
only the two proven real-analysis bricks `doubleFactorial_le_pow` (`(2r−1)‼ ≤ (2r)^r`) and
`rpow_inv_le_exp_one` (`Q^{1/r} ≤ e` when `r ≥ log Q`). -/
theorem moment_to_prize_sq
    {M n Q : ℝ} {r : ℕ} (hM : 0 ≤ M) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hbound : M ^ (2 * r) ≤ Q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r) :
    M ^ 2 ≤ 2 * Real.exp 1 * n * (r : ℝ) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℕ) ≠ 0 := by omega
  have hd0 : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by positivity
  -- (M^2)^r = M^{2r} ≤ Q·(2r−1)‼·n^r
  have hpow : (M ^ 2) ^ r ≤ Q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r := by
    rw [← pow_mul]; exact hbound
  -- take r-th root: M^2 ≤ (Q·(2r−1)‼·n^r)^{1/r}
  have hstep1 : M ^ 2
      ≤ (Q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r) ^ ((r : ℝ)⁻¹) := by
    calc M ^ 2
        = ((M ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (by positivity) hrne).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hpow (by positivity)
  -- expand the rpow over the product
  have hexpand : (Q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r) ^ ((r : ℝ)⁻¹)
      = Q ^ ((r : ℝ)⁻¹) * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * n := by
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (le_of_lt hQ) hd0,
        Real.pow_rpow_inv_natCast hn hrne]
  rw [hexpand] at hstep1
  -- Q^{1/r} ≤ e  and  (2r−1)‼^{1/r} ≤ 2r
  have hbq : Q ^ ((r : ℝ)⁻¹) ≤ Real.exp 1 := rpow_inv_le_exp_one hQ hr0 hrQ
  have hbd : (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) ≤ 2 * (r : ℝ) := by
    calc (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹)
        ≤ (((2 * r : ℕ) : ℝ) ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow hd0 (doubleFactorial_le_pow r) (by positivity)
      _ = ((2 * r : ℕ) : ℝ) := Real.pow_rpow_inv_natCast (by positivity) hrne
      _ = 2 * (r : ℝ) := by push_cast; ring
  calc M ^ 2
      ≤ Q ^ ((r : ℝ)⁻¹) * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * n := hstep1
    _ ≤ Real.exp 1 * (2 * (r : ℝ)) * n := by gcongr
    _ = 2 * Real.exp 1 * n * (r : ℝ) := by ring

/-! ## The char-0 energy bound, restated for the formal-period model -/

/-- **The char-0 energy bound is UNCONDITIONAL.** For `G` a finset of `2^k`-th roots of unity
(`k ≥ 1`) in a characteristic-zero field, the additive energy `E_r(G) = zeroSumCount G (2r)` obeys the
real-Gaussian bound `E_r ≤ (2r−1)‼·n^r`, with NO Sidon/`repThree`/antipodal-pairing hypothesis. This is
`DyadicEnergyK1.zeroSumCount_le_doubleFactorial_dyadic` cast to `ℝ` — the Lam–Leung input the prize
program names as `GaussianEnergyBound`, here discharged outright in char 0. -/
theorem char0_energy_bound {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) :
    (zeroSumCount G (2 * r) : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  have hnat := zeroSumCount_le_doubleFactorial_dyadic (L := L) hk G hG (r := r)
  calc (zeroSumCount G (2 * r) : ℝ)
      ≤ (((2 * r - 1)‼ * G.card ^ r : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by push_cast; ring

/-! ## THE ASSEMBLY: the full char-0 prize moment bound, one unconditional theorem -/

/-- **THE CHAR-0 PRIZE MOMENT BOUND (squared form), UNCONDITIONAL.**

In the formal complex period model (char 0, `G ⊆ μ_{2^k}`, `k ≥ 1`, no mod-`p` reduction), let `M` be
the sup of a formal period vector with `Q ≥ 1` frequencies. The SOLE structural input is the
formal-period moment identity `M^{2r} ≤ Q · E_r(G)` (= the model's definition: one term ≤ the full
`2r`-th moment; field-independent counting, instantiated by `subgroup_gaussSum_moment` in `F_q`). Then,
at the optimal depth `r ≥ max(1, log Q)`, the char-0 Lam–Leung energy bound (discharged internally via
`char0_energy_bound`) gives the prize square-root shape

  `M² ≤ 2e · |G| · r`.

Everything is proven; the char-`p` transfer of the energy bound is the only gap to the full prize. -/
theorem char0_prize_moment_bound_sq {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : M ^ (2 * r) ≤ Q * (zeroSumCount G (2 * r) : ℝ)) :
    M ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) := by
  -- feed the char-0 energy bound into the moment identity, then run the saddle
  have henergy : (zeroSumCount G (2 * r) : ℝ)
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := char0_energy_bound hk G hG
  have hbound : M ^ (2 * r)
      ≤ Q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
    calc M ^ (2 * r) ≤ Q * (zeroSumCount G (2 * r) : ℝ) := hmoment
      _ ≤ Q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_left henergy (le_of_lt hQ)
      _ = Q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by ring
  exact moment_to_prize_sq hM (by positivity) hQ hr hrQ hbound

/-- **THE CHAR-0 PRIZE MOMENT BOUND (norm form), UNCONDITIONAL.** Square-root of
`char0_prize_moment_bound_sq`: the formal period sup obeys the prize bound

  `M ≤ √(2e · |G| · r)`,

with explicit constant `√(2e)`. At `r = ⌈log Q⌉` this is `M ≤ √(2e)·√(|G|·log Q)` — the
Gaussian/Ramanujan per-frequency target. The char-0 energy bound is discharged internally
(`char0_energy_bound` ← Lam–Leung); the SOLE gap to the prize is the char-`p` transfer at the prize
scale `n = 2^30` (the BGK wall). -/
theorem char0_prize_moment_bound {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : M ^ (2 * r) ≤ Q * (zeroSumCount G (2 * r) : ℝ)) :
    M ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) := by
  have hsq := char0_prize_moment_bound_sq hk G hG hM hQ hr hrQ hmoment
  calc M = Real.sqrt (M ^ 2) := (Real.sqrt_sq hM).symm
    _ ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) := Real.sqrt_le_sqrt hsq

end ArkLib.ProximityGap.Frontier.WFL3

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only. -/
#print axioms ArkLib.ProximityGap.Frontier.WFL3.moment_to_prize_sq
#print axioms ArkLib.ProximityGap.Frontier.WFL3.char0_energy_bound
#print axioms ArkLib.ProximityGap.Frontier.WFL3.char0_prize_moment_bound_sq
#print axioms ArkLib.ProximityGap.Frontier.WFL3.char0_prize_moment_bound
