/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The hypercontractive (Bonami–Beckner / (2,q)-norm) route for the phase function (#444, route A4)

**Route under test.** The antipodal phase contributions `Y_k = 2cos(2π·b·x_k/p)` are *degree-1*
functions of the frequency `b` (the phases `θ_k = b·x_k` are a RANK-1 linear form in `b`,
machine-verified in `phase_independence.py`). For degree-1 functions on a product probability
space, the **Bonami–Beckner / hypercontractive (2,q)-norm inequality** controls high moments by the
second moment with the *sharp degree-1 constant*:
```
  ‖f‖_q ≤ (q−1)^{1/2}·‖f‖_2      (degree-1 hypercontractivity).
```
Taking `q = 2r` and `f = η`, this reads `‖η‖_{2r}^{2r} ≤ (2r−1)^r·‖η‖_2^{2r}`, i.e. the energy bound
```
  E[η^{2r}] ≤ (2r−1)^r · n^r          (HYPERCONTRACTIVE).
```
Compare to the Wick / real-Gaussian shape used by the in-tree moment route
(`GaussPeriodMomentBound.GaussianEnergyBound`):
```
  E[η^{2r}] ≤ (2r−1)‼ · n^r           (WICK).
```

**This is a genuinely different route** (a functional inequality on the character group, NOT the
equidistribution of the Gauss-sum phases). So the natural questions the task poses are:
*(i) is the hypercontractive bound `≤` Wick, and (ii) does it give the prize?*

**Answers, both landed here, axiom-clean.**

* **(i) NO — the hypercontractive constant is STRICTLY LARGER than Wick** (for every `r ≥ 2`):
  `theorem doubleFact_le_pow` proves `(2r−1)‼ ≤ (2r−1)^r` (each of the `r` odd factors `2i+1`,
  `i < r`, is `≤ 2r−1`). So the **HYPERCONTRACTIVE energy bound is a strictly WEAKER hypothesis than
  WICK** (`theorem hyperc_energy_of_wick_energy`: any family satisfying the Wick bound a fortiori
  satisfies the hypercontractive bound). The ratio `(2r−1)^r/(2r−1)‼ ∼ e^r/√2` blows up: HC trades
  the Gaussian `√(2r/e)` factor for the larger `√(2r)`.

* **(ii) YES, it STILL gives the prize SHAPE — at a worse constant.** Running the exact same
  `r`-th-root + `r = ⌈ln q⌉` optimisation that the Wick route uses, the hypercontractive ceiling
  `‖η‖^{2r} ≤ q·(2r−1)^r·n^r` yields `‖η‖² ≤ 2e·n·(ln q + 1)`, i.e.
  `M ≤ √(2e·n·(ln q+1))` (`theorem hyperc_supnorm_bound`). Constant `√(2e) ≈ 2.33` vs Wick's
  `√2 ≈ 1.41`; both are `O(√(n log q))` — the prize FLOOR shape. So hypercontractivity *would*
  win the prize-shaped bound IF its hypothesis held.

**HONEST VERDICT (route REDUCES to the SAME open input — no free escape).** The (2,q)-hypercontractive
inequality with the degree-1 constant is a theorem of Bonami–Beckner only on a *product* probability
space (boolean/Gaussian cube): it requires the `n/2` coordinates to be INDEPENDENT (tensorisation of
the noise operator). Here the phases are RANK-1 in `b`, so the `n/2` contributions are exactly NOT
independent product coordinates (`phase_independence.py`: pairwise near-independent, max|Corr|=0.045,
but jointly a single linear form). Hence the hypercontractive *hypothesis* `E[η^{2r}] ≤ (2r−1)^r·n^r`
is NOT free — establishing it for the rank-1 phase family is the SAME low-order-equidistribution /
BGK obligation as the Wick bound, only with MORE slack to spare (it asks for `(2r−1)^r`, not the
tighter `(2r−1)‼`). The functional-inequality route therefore *cannot be easier to land than Wick
and simultaneously beat it*: by `hyperc_energy_of_wick_energy`, Wick ⟹ HC, so HC is the weaker
target; and it pays for that with the larger `√(2e)` constant. The route is a strictly-looser
reformulation, not an escape from the open core. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.Frontier.PhaseHypercontractive

open Real Finset

/-! ## Part I — the constant comparison: hypercontractive `(2r−1)^r` ≥ Wick `(2r−1)‼` -/

/-- The Wick double factorial as an explicit product of odd numbers:
`(2r−1)‼ = ∏_{i<r} (2i+1)`. (Reindexing of `Nat.doubleFactorial` at odd argument.) -/
theorem doubleFact_eq_prod (r : ℕ) :
    (Nat.doubleFactorial (2 * r - 1) : ℝ) = ∏ i ∈ Finset.range r, ((2 * i + 1 : ℕ) : ℝ) := by
  induction r with
  | zero => simp [Nat.doubleFactorial]
  | succ k ih =>
    -- (2(k+1)−1)‼ = (2k+1)‼ = (2k+1)·(2k−1)‼; split the product off its last factor.
    have hstep : Nat.doubleFactorial (2 * (k + 1) - 1)
        = (2 * k + 1) * Nat.doubleFactorial (2 * k - 1) := by
      cases k with
      | zero => decide
      | succ j =>
        -- LHS index: 2*(j+2)-1 = 2j+3 = (2j+1)+2; RHS index: 2*(j+1)-1 = 2j+1
        -- so `(2j+3)‼ = (2j+3)·(2j+1)‼` is `doubleFactorial_add_two` at `n = 2j+1`.
        have hL : 2 * (j + 1 + 1) - 1 = (2 * j + 1) + 2 := by omega
        have hR : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
        rw [hL, hR, Nat.doubleFactorial_add_two]
        ring_nf
    rw [Finset.prod_range_succ, ← ih, hstep]
    push_cast
    ring

/-- **The degree-1 hypercontractive constant DOMINATES the Wick constant.**
`(2r−1)‼ ≤ (2r−1)^r`: the Wick product `∏_{i<r}(2i+1)` has each of its `r` factors `2i+1 ≤ 2r−1`
(for `i < r`, `r ≥ 1`), so the product is at most `(2r−1)^r`. This is the precise sense in which the
Bonami–Beckner `(q−1)^{1/2}` constant (`q = 2r`) is WEAKER than the real-Gaussian/Wick constant. -/
theorem doubleFact_le_pow (r : ℕ) (hr : 1 ≤ r) :
    (Nat.doubleFactorial (2 * r - 1) : ℝ) ≤ ((2 * r - 1 : ℕ) : ℝ) ^ r := by
  rw [doubleFact_eq_prod r]
  calc ∏ i ∈ Finset.range r, ((2 * i + 1 : ℕ) : ℝ)
      ≤ ∏ _i ∈ Finset.range r, ((2 * r - 1 : ℕ) : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i hi
          have hir : i + 1 ≤ r := Finset.mem_range.mp hi
          have : (2 * i + 1 : ℕ) ≤ (2 * r - 1 : ℕ) := by omega
          exact_mod_cast this
    _ = ((2 * r - 1 : ℕ) : ℝ) ^ r := by rw [Finset.prod_const, Finset.card_range]

/-- A coarser, `r`-uniform form convenient for the optimisation: `(2r−1)^r ≤ (2r)^r`. -/
theorem pow_two_r_sub_one_le (r : ℕ) :
    ((2 * r - 1 : ℕ) : ℝ) ^ r ≤ (2 * (r : ℝ)) ^ r := by
  apply pow_le_pow_left₀ (by positivity)
  have : ((2 * r - 1 : ℕ) : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
  rw [show ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) by push_cast; ring] at this
  exact this

/-! ## Part II — the abstract energy bounds and the WEAKENING direction -/

/-- **The Wick / real-Gaussian energy bound** (the in-tree moment-route input shape):
`E_r ≤ (2r−1)‼·n^r`. Stated abstractly here on a real `E : ℕ → ℝ` (`E r` = the `2r`-th moment, `n`
= the variance proxy) so this file is self-contained and import-light; it is *definitionally* the
shape of `GaussPeriodMomentBound.GaussianEnergyBound`. -/
def WickEnergyBound (E : ℕ → ℝ) (n : ℝ) (r : ℕ) : Prop :=
  E r ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r

/-- **The hypercontractive / Bonami–Beckner degree-1 energy bound:** `E_r ≤ (2r−1)^r·n^r`, the
`r`-th moment shape coming from `‖f‖_{2r} ≤ (2r−1)^{1/2}‖f‖_2`. -/
def HypercontractiveEnergyBound (E : ℕ → ℝ) (n : ℝ) (r : ℕ) : Prop :=
  E r ≤ ((2 * r - 1 : ℕ) : ℝ) ^ r * n ^ r

/-- **Wick is the STRONGER hypothesis: Wick ⟹ Hypercontractive.** Because `(2r−1)‼ ≤ (2r−1)^r`
(`doubleFact_le_pow`), any energy family obeying the Wick bound a fortiori obeys the (looser)
hypercontractive bound. So the hypercontractive route asks for *strictly less* than the Wick route
(for `r ≥ 2`): it is a WEAKER target, and accordingly delivers a worse constant (Part III). There is
no free lunch — proving HC for the rank-1 phase family is no harder than, but also gives less than,
proving Wick. -/
theorem hyperc_energy_of_wick_energy {E : ℕ → ℝ} {n : ℝ} (hn : 0 ≤ n) {r : ℕ} (hr : 1 ≤ r)
    (hwick : WickEnergyBound E n r) : HypercontractiveEnergyBound E n r := by
  refine le_trans hwick ?_
  apply mul_le_mul_of_nonneg_right (doubleFact_le_pow r hr)
  positivity

/-! ## Part III — the optimisation: HC energy ⟹ prize SHAPE `M ≤ √(2e·n·(ln q + 1))` -/

/-- **The hypercontractive per-frequency power ceiling.** The energy bound `E_r ≤ (2r−1)^r·n^r`,
summed over the `q` frequencies and dominated for the worst `b`, gives `‖η_b‖^{2r} ≤ q·(2r−1)^r·n^r`.
We package the consequence abstractly: from a power bound `x^{2r} ≤ q·(2r−1)^r·n^r` (`x = ‖η_b‖ ≥ 0`)
we extract the squared bound `x² ≤ q^{1/r}·(2r)·n` by taking the `r`-th root of the square. -/
theorem sq_le_of_hyperc_pow {x q n : ℝ} (hx : 0 ≤ x) (hq : 0 < q) (hn : 0 ≤ n) {r : ℕ} (hr : 1 ≤ r)
    (hpow : x ^ (2 * r) ≤ q * (2 * (r : ℝ)) ^ r * n ^ r) :
    x ^ 2 ≤ q ^ ((r : ℝ)⁻¹) * (2 * (r : ℝ)) * n := by
  have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr
  -- (x²)^r = x^{2r} ≤ q·(2r·n)^r, so x² ≤ (q·(2r·n)^r)^{1/r} = q^{1/r}·(2r·n).
  have hsq : (x ^ 2) ^ r ≤ q * (2 * (r : ℝ) * n) ^ r := by
    rw [← pow_mul]
    refine le_trans hpow (le_of_eq ?_)
    rw [mul_pow]; ring
  have hroot : x ^ 2 ≤ (q * (2 * (r : ℝ) * n) ^ r) ^ ((r : ℝ)⁻¹) := by
    calc x ^ 2
        = ((x ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (by positivity) (Nat.one_le_iff_ne_zero.mp hr)).symm
      _ ≤ (q * (2 * (r : ℝ) * n) ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hsq (by positivity)
  refine le_trans hroot (le_of_eq ?_)
  -- (q·A^r)^{1/r} = q^{1/r}·A  for A = 2r·n ≥ 0.
  rw [Real.mul_rpow hq.le (by positivity), ← Real.rpow_natCast (2 * (r : ℝ) * n) r,
      ← Real.rpow_mul (by positivity), mul_inv_cancel₀ hrne, Real.rpow_one]
  ring

/-- **The hypercontractive prize-shape bound.** Choosing the depth `r = ⌈ln q⌉` makes `q^{1/r} ≤ e`
(since `r ≥ ln q ⟹ (ln q)/r ≤ 1`), so the squared ceiling becomes `x² ≤ e·(2r)·n ≤ 2e·n·(ln q + 1)`,
i.e. `M ≤ √(2e·n·(ln q + 1))` — the prize FLOOR shape with constant `√(2e) ≈ 2.33` (vs Wick `√2`).

We land the *core arithmetic step* of that optimisation: given a real `x ≥ 0` and a depth
`r ≥ 1` with `r ≥ ln q` (the choice `r = ⌈ln q⌉`) and `q ≥ 1`, the hypercontractive squared ceiling
`x² ≤ q^{1/r}·(2r)·n` implies `x² ≤ Real.exp 1 · (2·r)·n`, the per-frequency `2e·n·r` ceiling. -/
theorem hyperc_sq_le_exp {x q n : ℝ} (hx : 0 ≤ x) (hq : 1 ≤ q) (hn : 0 ≤ n) {r : ℕ} (hr : 1 ≤ r)
    (hrlog : Real.log q ≤ (r : ℝ))
    (hsq : x ^ 2 ≤ q ^ ((r : ℝ)⁻¹) * (2 * (r : ℝ)) * n) :
    x ^ 2 ≤ Real.exp 1 * (2 * (r : ℝ)) * n := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  -- q^{1/r} = exp((ln q)/r) ≤ exp 1.
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hqr : q ^ ((r : ℝ)⁻¹) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hqpos]
    apply Real.exp_le_exp.mpr
    rw [mul_inv_le_iff₀ hrpos, one_mul]
    exact hrlog
  calc x ^ 2
      ≤ q ^ ((r : ℝ)⁻¹) * (2 * (r : ℝ)) * n := hsq
    _ ≤ Real.exp 1 * (2 * (r : ℝ)) * n := by
        apply mul_le_mul_of_nonneg_right _ hn
        exact mul_le_mul_of_nonneg_right hqr (by positivity)

/-- **The hypercontractive sup-norm bound, assembled into prize shape.** Combining the squared
ceiling `x² ≤ 2e·n·r` (at `r = ⌈ln q⌉`, so `r ≤ ln q + 1`) gives `x ≤ √(2e·n·(ln q + 1))`. This is
the prize FLOOR `M ≤ √(c·n·ln q)` with `c = 2e ≈ 5.44` (constant `√(2e) ≈ 2.33`), the *same shape*
as the Wick route's `√(2·n·ln q)` but a strictly worse constant — exactly the `(2r−1)^r ≥ (2r−1)‼`
slack from Part I, paid back. -/
theorem hyperc_supnorm_bound {x q n : ℝ} (hx : 0 ≤ x) (hq : 1 ≤ q) (hn : 0 ≤ n) {r : ℕ} (hr : 1 ≤ r)
    (hrlog : Real.log q ≤ (r : ℝ)) (hrle : (r : ℝ) ≤ Real.log q + 1)
    (hsq : x ^ 2 ≤ q ^ ((r : ℝ)⁻¹) * (2 * (r : ℝ)) * n) :
    x ≤ Real.sqrt (2 * Real.exp 1 * n * (Real.log q + 1)) := by
  have hexp : x ^ 2 ≤ Real.exp 1 * (2 * (r : ℝ)) * n :=
    hyperc_sq_le_exp hx hq hn hr hrlog hsq
  have hbound : x ^ 2 ≤ 2 * Real.exp 1 * n * (Real.log q + 1) := by
    refine le_trans hexp ?_
    -- exp 1 · 2r · n ≤ 2·exp 1·n·(ln q + 1)  since r ≤ ln q + 1 and the prefactors ≥ 0.
    have he : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    nlinarith [hrle, hn, he, mul_nonneg he hn]
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt (2 * Real.exp 1 * n * (Real.log q + 1)) := Real.sqrt_le_sqrt hbound

/-! ## Part IV — the verdict object: HC is strictly weaker than Wick (no escape) -/

/-- **No-escape, stated as a `Prop` relation.** The hypercontractive route's hypothesis is implied by
the Wick route's hypothesis (for `r ≥ 2`, strictly weaker). Concretely: for any energy family and any
`n ≥ 0`, `r ≥ 1`, `WickEnergyBound → HypercontractiveEnergyBound`. So the functional-inequality route
cannot be a *free* shortcut around the open core: it asks for less (hence is no harder), and—by Part
III—delivers a `√(2e)` constant rather than Wick's `√2`. Bounding the rank-1 phase family by *either*
is the same low-order-equidistribution / BGK obligation; HC merely has more slack. -/
theorem hyperc_route_is_weaker {E : ℕ → ℝ} {n : ℝ} (hn : 0 ≤ n) {r : ℕ} (hr : 1 ≤ r) :
    WickEnergyBound E n r → HypercontractiveEnergyBound E n r :=
  fun hwick => hyperc_energy_of_wick_energy hn hr hwick

end ProximityGap.Frontier.PhaseHypercontractive

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.PhaseHypercontractive.doubleFact_eq_prod
#print axioms ProximityGap.Frontier.PhaseHypercontractive.doubleFact_le_pow
#print axioms ProximityGap.Frontier.PhaseHypercontractive.hyperc_energy_of_wick_energy
#print axioms ProximityGap.Frontier.PhaseHypercontractive.sq_le_of_hyperc_pow
#print axioms ProximityGap.Frontier.PhaseHypercontractive.hyperc_sq_le_exp
#print axioms ProximityGap.Frontier.PhaseHypercontractive.hyperc_supnorm_bound
#print axioms ProximityGap.Frontier.PhaseHypercontractive.hyperc_route_is_weaker
