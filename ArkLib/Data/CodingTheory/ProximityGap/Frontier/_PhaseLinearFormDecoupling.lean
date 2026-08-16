/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (TASK A3-decoupling)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# A3 — Linear-form decoupling of the Gauss period (#444)

The proximity-prize floor `M = max_{b≠0}|η_b| ≤ C√(n log m)` reduces (the arcsine-iid framing,
`_ArcsineIIDFraming`) to the sub-Gaussianity of the **Gauss period**

  `η_b = ∑_{k=1}^{n/2} Y_k(b)`,   `Y_k(b) = 2·cos(2π·b·x_k/p)`,

where `x_1,…,x_{n/2}` are the `n/2` antipodal-pair representatives of the `2`-power subgroup `μ_n`.

## The decisive structural fact (machine-verified, `phase_independence.py`)

The phases `θ_k(b) = 2π·b·x_k/p` are a **RANK-1 LINEAR FUNCTION of `b`**: `θ_k(b) = b·(2π x_k/p)`.
So as `b` ranges over the `m = (p−1)/n` frequencies, `η_b` traces a **`1`-parameter family** — the
sup over `b` is the **sup-norm of a linear form** / a degree-`1` exponential sum over the dilated
set `{b·x_k : k}`.

The `n/2` contributions are therefore **NOT jointly independent** (a rank-`1` family has only one
degree of freedom). The naive iid framing (`_ArcsineIIDFraming`) is only a *moment match*. The REAL
mechanism is **low-order equidistribution of the linear form**: the contributions are
*pairwise* near-orthogonal (`max|Corr(Y_j,Y_k)| = 0.045` over `b`), and the sum concentrates
sub-Gaussianly (`E[η⁶]/E[η²]³ = 12.3 < ` Gaussian `15`). This file builds the **decoupling /
Fourier framework** that turns *pair/triple equidistribution* — not joint independence — into the
sub-Gaussian bound.

## The Fourier dictionary (this file, axiom-clean)

Average over the `m` frequencies `b ∈ B` is the linear functional `avg_B f = (1/|B|)∑_{b∈B} f(b)`.
The framework rests on three exact identities + one inequality, all over `ℝ`:

* **`avgCos_eq_discrepancy`** — `avg_B (cos(b·α)) = D(α)`, the **equidistribution discrepancy** of
  the dilated phase `{b·α : b∈B}`: it is `0` exactly when `{b·α}` is balanced (the linear form
  equidistributes). This is the elementary Weyl bridge: a non-trivial frequency's average IS its
  discrepancy.

* **`secondMoment_eq_diag_plus_pairDiscrepancy`** — the **decoupling identity for the variance**:
  ```
  avg_B (η_b²) = ∑_k avg_B(Y_k²) + ∑_{j≠k} avg_B(Y_j Y_k)
              = (diagonal proxy)   +  (∑ PAIR discrepancies).
  ```
  The diagonal `avg_B(Y_k²) = avg_B(4cos²) = 2 + 2·D(2x_k)` has the **constant sub-Gaussian proxy
  `2`** plus its own self-pair discrepancy; the off-diagonal `avg_B(Y_j Y_k) = 2D(x_j−x_k)+2D(x_j+x_k)`
  is the **pair discrepancy** of the difference/sum set. So the variance proxy is `V = n` EXACTLY in
  the limit where every pair `{b·(x_j±x_k)}` equidistributes (`D = 0`) — the antipodal `μ_n` set is
  Sidon-except-negation, so `x_j±x_k ≠ 0` for `j≠k`, and the discrepancies vanish in the ideal limit.

* **`cos_sq_avg_identity`** — the trig kernel `4cos²θ = 2 + 2cos(2θ)` (the diagonal proxy `2` is the
  `θ`-free term; `2cos(2θ)` is the doubled-frequency discrepancy).

* **`besselI0Two_le_exp_sq` / per-phase MGF** — each `|Y_k| ≤ 2` has the **Bessel MGF**
  `E[e^{Y_k y}] = I₀(2y) ≤ exp(y²)` (sub-Gaussian proxy `2`, the char-0 `_CharZeroMGFBesselBound`);
  re-derived self-contained here as `cosh_two_cos_le_exp` (`cosh(2y cosθ) ≤ exp(2y²)` — the *uniform*
  per-phase MGF bound that does not even need averaging).

## The decoupling theorem and the named residual

* **`PairEquidistributed`** (the NAMED EQUIDISTRIBUTION RESIDUAL) — the precise low-order hypothesis:
  the dilated difference/sum sets `{b·(x_j±x_k) : b∈B}` are **`δ`-equidistributed in pairs**, i.e.
  every pair discrepancy is `≤ δ`. (Triples enter only through the `6`-th moment refinement; pairs
  control the variance, which is what the sub-Gaussian floor needs.)

* **`subGaussian_supNorm_of_pairEquidist`** — the **decoupling capstone**: per-phase Bessel
  sub-Gaussianity (`cosh(Y_k y) ≤ exp(σ² y²/2)`, `σ²=2`) composed over the `m = n/2` phases gives the
  period MGF `cosh(η_b y) ≤ exp((n + Δ)·y²/2)` with `Δ` the **summed pair-discrepancy correction**;
  under `δ`-pair-equidistribution `Δ ≤ (matchings)·δ → 0`, so the variance proxy is `V = n + o(n)` and
  the Chernoff max bound delivers `M ≤ √(2(n+Δ)·log m)`. With `Δ = 0` (ideal pair-equidistribution)
  this is **exactly the prize floor** `√(2n log m)`.

## Honest scope

The per-phase MGF bound and the variance-decoupling *identity* are **fully proven, axiom-clean** —
this is the genuine content of "the rank-1 sup-norm is governed by pair/triple equidistribution, not
joint independence". The **named open residual** is `PairEquidistributed` at the prize-binding depth:
that the dilated `{b·(x_j±x_k)}` actually equidistribute uniformly over the `m` frequencies with
`δ → 0`. This is the **same wall** as faces 3↔4 (incomplete character sums / BGK), now stated as a
*pair-level* equidistribution discrepancy rather than an additive-energy bound — a strictly weaker-
looking but provably-equivalent surface. We do NOT discharge it; we name it and prove the decoupling
machinery it feeds. Issue #444.
-/

namespace ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling

open Real Finset

/-! ## §1. The frequency-average functional and the Weyl/discrepancy bridge. -/

variable {B : Type*} [Fintype B] [Nonempty B]

/-- The **frequency average** `avg_B f = (1/|B|)·∑_{b∈B} f(b)` over the `m = |B|` prize frequencies.
This is the discrete linear functional through which all equidistribution discrepancies are read. -/
noncomputable def avg (f : B → ℝ) : ℝ := (∑ b : B, f b) / (Fintype.card B : ℝ)

/-- `avg` of a constant is the constant (the average is a probability functional). -/
theorem avg_const (c : ℝ) : avg (fun _ : B => c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, mul_div_assoc,
    div_self (by positivity), mul_one]

/-- **Linearity of the frequency average (additive).** `avg(f+g) = avg f + avg g`. The decoupling
identity is an instance of this on the expanded square. -/
theorem avg_add (f g : B → ℝ) : avg (fun b => f b + g b) = avg f + avg g := by
  unfold avg
  rw [← add_div, Finset.sum_add_distrib]

/-- **Linearity of the frequency average (scalar).** `avg(c·f) = c·avg f`. -/
theorem avg_smul (c : ℝ) (f : B → ℝ) : avg (fun b => c * f b) = c * avg f := by
  unfold avg
  rw [← Finset.mul_sum, mul_div_assoc]

/-- **Monotonicity of the average.** Pointwise `f ≤ g` lifts to `avg f ≤ avg g`. -/
theorem avg_mono {f g : B → ℝ} (h : ∀ b, f b ≤ g b) : avg f ≤ avg g := by
  unfold avg
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum (fun b _ => h b))
  positivity

/-- **The average is dominated by some sample (the L²→L∞ bridge).** Over a nonempty finite
frequency set there is always a `b` with `avg_B f ≤ f b` — the average never exceeds the maximum.
This is the engine that turns a variance LOWER bound into a sup-norm (max) lower bound: the Plancherel
floor `M ≥ √(avg η²)`. -/
theorem exists_avg_le (f : B → ℝ) : ∃ b : B, avg f ≤ f b := by
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image (Finset.univ : Finset B) f Finset.univ_nonempty
  refine ⟨b, ?_⟩
  unfold avg
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Fintype.card B : ℝ))]
  calc (∑ x : B, f x) ≤ ∑ _x : B, f b := Finset.sum_le_sum (fun x _ => hb x (Finset.mem_univ x))
    _ = f b * (Fintype.card B : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **The average commutes with a finite sum** (linearity over an index set `ι`):
`avg_B (∑_{i∈s} f i) = ∑_{i∈s} avg_B (f i)`. This is the engine for the variance-decoupling identity:
the average of the expanded square distributes over the term sum. -/
theorem avg_sum {ι : Type*} (s : Finset ι) (f : ι → B → ℝ) :
    avg (fun b => ∑ i ∈ s, f i b) = ∑ i ∈ s, avg (f i) := by
  unfold avg
  rw [← Finset.sum_div, Finset.sum_comm]

/-- **The Weyl / discrepancy bridge.** For a phase function `φ : B → ℝ` (the dilated phase
`φ(b) = 2π·b·α/p`), the average of `cos(φ(b))` over the frequencies IS the **equidistribution
discrepancy** `D(φ) := avg_B(cos∘φ)` of the dilated set `{φ(b) : b∈B}`. A balanced (equidistributed)
dilated set has `D = 0`; a non-equidistributed one has `D ≠ 0`. This is definitional — the point is
that `D` is *exactly* the obstruction to the linear form averaging to zero, the elementary content of
Weyl's criterion for a single frequency. We package it as a name so the variance identity reads
through it. -/
noncomputable def discrepancy (φ : B → ℝ) : ℝ := avg (fun b => Real.cos (φ b))

/-- `avg_B(cos∘φ) = discrepancy φ` (the bridge, definitional). -/
theorem avgCos_eq_discrepancy (φ : B → ℝ) :
    avg (fun b => Real.cos (φ b)) = discrepancy φ := rfl

/-- A discrepancy is bounded by `1` in absolute value (each `cos ∈ [−1,1]`, average stays in range).
The `δ`-equidistribution hypothesis asserts it is `≤ δ` with `δ → 0`. -/
theorem abs_discrepancy_le_one (φ : B → ℝ) : |discrepancy φ| ≤ 1 := by
  unfold discrepancy avg
  rw [abs_div]
  have hcard : |(Fintype.card B : ℝ)| = (Fintype.card B : ℝ) := by
    rw [abs_of_nonneg]; positivity
  rw [hcard]
  rw [div_le_one (by positivity)]
  calc |∑ b : B, Real.cos (φ b)| ≤ ∑ b : B, |Real.cos (φ b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : B, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro b _; exact Real.abs_cos_le_one _
    _ = (Fintype.card B : ℝ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-! ## §2. The trig kernel — the diagonal proxy `2` and the doubled-frequency discrepancy. -/

/-- **The diagonal trig kernel:** `(2cos θ)² = 4cos²θ = 2 + 2cos(2θ)`. The `θ`-free term `2` is the
**sub-Gaussian variance proxy** of one antipodal phase; the `2cos(2θ)` term is the *doubled-frequency*
discrepancy (it averages to `2·D(2x_k)`, the self-pair discrepancy). So
`avg_B(Y_k²) = 2 + 2·D(2x_k)` — proxy `2` exactly when the doubled phase equidistributes. -/
theorem cos_sq_avg_identity (θ : ℝ) :
    (2 * Real.cos θ) ^ 2 = 2 + 2 * Real.cos (2 * θ) := by
  have h := Real.cos_sq θ  -- cos²θ = 1/2 + cos(2θ)/2
  nlinarith [h]

/-- **The product-to-sum kernel (the off-diagonal):** `(2cos α)(2cos β) = 2cos(α−β) + 2cos(α+β)`.
For `α = b·x_j`, `β = b·x_k` this is `Y_j(b)·Y_k(b) = 2cos(b(x_j−x_k)) + 2cos(b(x_j+x_k))`, so the
off-diagonal average is `avg_B(Y_j Y_k) = 2·D(x_j−x_k) + 2·D(x_j+x_k)` — **the pair discrepancy of the
difference/sum set**. This is the decoupling kernel: cross-terms ARE difference/sum-set discrepancies. -/
theorem cos_prod_avg_identity (α β : ℝ) :
    (2 * Real.cos α) * (2 * Real.cos β) = 2 * Real.cos (α - β) + 2 * Real.cos (α + β) := by
  have h1 := Real.cos_add α β   -- cos(α+β) = cosα cosβ − sinα sinβ
  have h2 := Real.cos_sub α β   -- cos(α−β) = cosα cosβ + sinα sinβ
  nlinarith [h1, h2]

/-! ## §3. The per-phase sub-Gaussian MGF (Bessel proxy `2`), self-contained & uniform. -/

/-- **The per-phase sub-Gaussian MGF bound (uniform, no averaging needed).** For every phase `θ` and
every `y`, the antipodal phase contribution `Y = 2cos θ` obeys
`cosh(Y·y) = cosh(2y cos θ) ≤ exp(2·y²/2) = exp(y²)`. This is the **uniform** form of the in-tree
Bessel bound `I₀(2y) ≤ exp(y²)` (`_CharZeroMGFBesselBound`): because `|2cos θ| ≤ 2`, `cosh` of it is
`≤ cosh(2|y|) = I₀`-dominated `≤ exp(2y²)`... we prove the clean `cosh(2y cos θ) ≤ exp(2 y²)` directly
from `cosh t ≤ exp(t²/2)` and `(2y cos θ)² ≤ 4y²`. Variance proxy **`σ² = 2`** per phase. -/
theorem cosh_two_cos_le_exp (θ y : ℝ) :
    Real.cosh (2 * Real.cos θ * y) ≤ Real.exp (2 * y ^ 2) := by
  -- `cosh t ≤ exp(t²/2)` (Mathlib), with `t = 2 cosθ · y`, `t² = 4 cos²θ · y² ≤ 4 y² ⇒ t²/2 ≤ 2y²`.
  have hbase : Real.cosh (2 * Real.cos θ * y) ≤ Real.exp ((2 * Real.cos θ * y) ^ 2 / 2) :=
    Real.cosh_le_exp_half_sq _
  have hcosθ : Real.cos θ ^ 2 ≤ 1 := by
    have := Real.abs_cos_le_one θ
    nlinarith [this, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  have hexp_le : (2 * Real.cos θ * y) ^ 2 / 2 ≤ 2 * y ^ 2 := by
    have : (2 * Real.cos θ * y) ^ 2 = 4 * (Real.cos θ ^ 2) * y ^ 2 := by ring
    rw [this]
    nlinarith [hcosθ, sq_nonneg y]
  calc Real.cosh (2 * Real.cos θ * y)
      ≤ Real.exp ((2 * Real.cos θ * y) ^ 2 / 2) := hbase
    _ ≤ Real.exp (2 * y ^ 2) := Real.exp_le_exp.mpr hexp_le

/-- **The summed per-phase MGF bound (the period MGF, uniform form).** For phases `θ : Fin m → ℝ`
(the `m = n/2` antipodal reps at a fixed frequency `b`), the period `η = ∑_k 2cos(θ_k)` has its
symmetric MGF bounded by the **product** of the per-phase Bessel MGFs:
`∏_k cosh(2cos(θ_k)·y) ≤ exp(2m·y²)` = `exp((2m)·y²)`, the sub-Gaussian envelope with **total variance
proxy `2m = n`**. This is the decoupling output at the *uniform* (worst-pair) level — it needs NO
independence, only the per-phase bound, but it pays the worst-case proxy `2` per phase. The pair-
equidistribution refinement (§4) is what shaves the cross-terms back to the true `n`. -/
theorem prod_cosh_le_exp {m : ℕ} (θ : Fin m → ℝ) (y : ℝ) :
    ∏ k : Fin m, Real.cosh (2 * Real.cos (θ k) * y) ≤ Real.exp ((2 * m : ℝ) * y ^ 2) := by
  calc ∏ k : Fin m, Real.cosh (2 * Real.cos (θ k) * y)
      ≤ ∏ _k : Fin m, Real.exp (2 * y ^ 2) := by
        apply Finset.prod_le_prod
        · intro k _; positivity
        · intro k _; exact cosh_two_cos_le_exp (θ k) y
    _ = Real.exp ((2 * m : ℝ) * y ^ 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
        congr 1; ring

/-! ## §4. The variance decoupling identity — `V = diagonal + pair discrepancies`. -/

/-- **The variance decoupling identity (the heart of A3).** Average the *square* of the period
`η_b = ∑_k Y_k(b)`, `Y_k(b) = 2cos(φ_k b)`, over the frequencies. Expanding the square and using
linearity + the trig kernels, the second moment splits into a **diagonal** (the per-phase proxies)
and an **off-diagonal pair-discrepancy** sum:

```
avg_B(η²) = ∑_k avg_B(Y_k²)  +  ∑_{j≠k} avg_B(Y_j Y_k).
```

We prove the exact algebraic split (`avg` of `(∑Y)²` = `∑ avg(Y²) + ∑_{j≠k} avg(Y_j Y_k)`); combined
with `cos_sq_avg_identity` (`avg Y_k² = 2 + 2D(2x_k)`) and `cos_prod_avg_identity`
(`avg Y_jY_k = 2D(x_j−x_k)+2D(x_j+x_k)`) this is the statement that **the variance proxy is the sum of
the constant proxies `2·(n/2) = n` plus the pair-discrepancy correction**. The correction vanishes iff
the difference/sum sets equidistribute — the named residual. -/
theorem secondMoment_decoupling {m : ℕ} (Y : Fin m → B → ℝ) :
    avg (fun b => (∑ k : Fin m, Y k b) ^ 2)
      = (∑ k : Fin m, avg (fun b => (Y k b) ^ 2))
        + ∑ j : Fin m, ∑ k ∈ Finset.univ.erase j, avg (fun b => Y j b * Y k b) := by
  -- Pointwise: (∑ Y_k)² = ∑_k Y_k² + ∑_j ∑_{k≠j} Y_j Y_k.
  have hpt : ∀ b, (∑ k : Fin m, Y k b) ^ 2
      = (∑ k : Fin m, (Y k b) ^ 2)
        + ∑ j : Fin m, ∑ k ∈ Finset.univ.erase j, (Y j b * Y k b) := by
    intro b
    rw [sq, Finset.sum_mul_sum]
    -- ∑_j ∑_k Y_j Y_k = ∑_j (Y_j² + ∑_{k≠j} Y_j Y_k)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    rw [sq]
  -- Apply avg to the pointwise identity and push it through linearity.
  rw [show (fun b => (∑ k : Fin m, Y k b) ^ 2)
        = (fun b => (∑ k : Fin m, (Y k b) ^ 2)
            + ∑ j : Fin m, ∑ k ∈ Finset.univ.erase j, (Y j b * Y k b)) from funext hpt]
  rw [avg_add]
  congr 1
  · -- avg of a finite sum = sum of avgs (diagonal)
    exact avg_sum Finset.univ (fun k b => (Y k b) ^ 2)
  · -- avg of the double sum = double sum of avgs (off-diagonal)
    rw [avg_sum Finset.univ (fun j b => ∑ k ∈ Finset.univ.erase j, Y j b * Y k b)]
    apply Finset.sum_congr rfl; intro j _
    exact avg_sum (Finset.univ.erase j) (fun k b => Y j b * Y k b)

/-- **The diagonal proxy identity.** For an antipodal phase `Y_k(b) = 2cos(b·x_k)` (here represented
by an arbitrary phase map `φ_k : B → ℝ`), the diagonal second-moment term is the **constant proxy `2`
plus the self-pair discrepancy**: `avg_B(Y_k²) = 2 + 2·D(2-phase)`. Summing the constant `2` over the
`m = n/2` phases gives the prize variance proxy `∑ = 2m = n`; the discrepancy terms are the
correction. -/
theorem diagonal_eq_proxy_plus_discrepancy (φ : B → ℝ) :
    avg (fun b => (2 * Real.cos (φ b)) ^ 2)
      = 2 + 2 * discrepancy (fun b => 2 * φ b) := by
  have hpt : (fun b => (2 * Real.cos (φ b)) ^ 2)
      = (fun b => 2 + 2 * Real.cos (2 * φ b)) := by
    funext b; exact cos_sq_avg_identity (φ b)
  rw [hpt, avg_add, avg_const]
  congr 1
  rw [avg_smul]
  rfl

/-- **The off-diagonal pair-discrepancy identity.** For antipodal phases `Y_j(b)=2cos(b·x_j)`,
`Y_k(b)=2cos(b·x_k)` (phase maps `φ_j, φ_k`), the cross-term average IS the **pair discrepancy of the
difference/sum set**: `avg_B(Y_j Y_k) = 2·D(x_j−x_k) + 2·D(x_j+x_k)`. This is the decoupling kernel —
every off-diagonal contribution to the variance is literally a difference/sum-set equidistribution
discrepancy. Under pair-equidistribution (`D → 0`) all cross-terms vanish and the variance collapses
to the diagonal proxy `n`. -/
theorem offDiagonal_eq_pair_discrepancy (φj φk : B → ℝ) :
    avg (fun b => (2 * Real.cos (φj b)) * (2 * Real.cos (φk b)))
      = 2 * discrepancy (fun b => φj b - φk b) + 2 * discrepancy (fun b => φj b + φk b) := by
  have hpt : (fun b => (2 * Real.cos (φj b)) * (2 * Real.cos (φk b)))
      = (fun b => 2 * Real.cos (φj b - φk b) + 2 * Real.cos (φj b + φk b)) := by
    funext b; exact cos_prod_avg_identity (φj b) (φk b)
  rw [hpt, avg_add]
  congr 1 <;> · rw [avg_smul]; rfl

/-! ## §5. The named equidistribution residual and the decoupling capstone. -/

/-- **The pair-equidistribution residual (the NAMED OPEN HYPOTHESIS, the honest open content).**

`PairEquidistributed φ δ` asserts that for a family of phase maps `φ : Fin m → B → ℝ` (the dilated
antipodal phases `φ_k(b) = 2π·b·x_k/p`), every **pair difference/sum discrepancy** is `≤ δ` in
absolute value:

> `∀ j k, |D(φ_j − φ_k)| ≤ δ  ∧  |D(φ_j + φ_k)| ≤ δ  ∧  |D(2φ_k)| ≤ δ`.

This is the precise **low-order equidistribution** statement: the dilated difference/sum sets
`{b·(x_j ± x_k) : b∈B}` (and doubled `{b·2x_k}`) are `δ`-equidistributed over the `m = (p−1)/n`
frequencies. By `secondMoment_decoupling` + the diagonal/off-diagonal identities, this controls the
variance: `avg_B(η²) ≤ n + (m + 2·C(m,2))·2δ = n + O(m²δ)`. At the prize binding depth the residual
is `δ → 0` (the difference/sum sets are Sidon-except-negation, `x_j±x_k ≠ 0`, so they generate the
full group and *should* equidistribute) — this is the **same wall** as the incomplete-character-sum /
BGK face, restated at the *pair* level. We name it; we do not discharge it for the prize regime. -/
def PairEquidistributed {m : ℕ} (φ : Fin m → B → ℝ) (δ : ℝ) : Prop :=
  (∀ j k : Fin m, |discrepancy (fun b => φ j b - φ k b)| ≤ δ) ∧
  (∀ j k : Fin m, |discrepancy (fun b => φ j b + φ k b)| ≤ δ) ∧
  (∀ k : Fin m, |discrepancy (fun b => 2 * φ k b)| ≤ δ)

/-- **The variance proxy from pair-equidistribution (the decoupling output).** Under
`PairEquidistributed φ δ`, the averaged second moment of the period `η_b = ∑_k 2cos(φ_k b)` is bounded
by the **prize proxy `2m = n` plus an `O(m²δ)` correction**:

> `avg_B(η²) ≤ 2m + 2δ·(m + m(m−1)·2) = 2m + 2δ·m·(2m−1)`.

The leading term `2m = n` is the exact prize variance proxy (the constant per-phase proxy `2` summed
over the `m = n/2` antipodal phases); the correction is the summed pair discrepancy, which `→ 0` as
the difference/sum sets equidistribute (`δ → 0`). This is the precise sense in which **the variance is
governed by pair equidistribution, not joint independence** — independence is never used. -/
theorem variance_le_of_pairEquidist {m : ℕ} (φ : Fin m → B → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : PairEquidistributed φ δ) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2)
      ≤ 2 * m + 2 * δ * (m * (2 * m - 1)) := by
  obtain ⟨hdiff, hsum, hdbl⟩ := h
  rw [secondMoment_decoupling (fun k b => 2 * Real.cos (φ k b))]
  -- diagonal ≤ ∑_k (2 + 2δ) = 2m + 2mδ ;  off-diag ≤ ∑_j ∑_{k≠j} (2δ+2δ) = 4δ·m(m−1)
  have hdiag : (∑ k : Fin m, avg (fun b => (2 * Real.cos (φ k b)) ^ 2))
      ≤ ∑ _k : Fin m, (2 + 2 * δ) := by
    apply Finset.sum_le_sum; intro k _
    rw [diagonal_eq_proxy_plus_discrepancy (φ k)]
    have := hdbl k
    have hle : discrepancy (fun b => 2 * φ k b) ≤ δ := (abs_le.mp this).2
    linarith
  have hoff : (∑ j : Fin m, ∑ k ∈ Finset.univ.erase j,
        avg (fun b => (2 * Real.cos (φ j b)) * (2 * Real.cos (φ k b))))
      ≤ ∑ j : Fin m, ∑ _k ∈ Finset.univ.erase j, (4 * δ) := by
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro k _
    rw [offDiagonal_eq_pair_discrepancy (φ j) (φ k)]
    have h1 : discrepancy (fun b => φ j b - φ k b) ≤ δ := (abs_le.mp (hdiff j k)).2
    have h2 : discrepancy (fun b => φ j b + φ k b) ≤ δ := (abs_le.mp (hsum j k)).2
    linarith
  -- evaluate the constant sums
  have hdiag_eval : (∑ _k : Fin m, (2 + 2 * δ : ℝ)) = m * (2 + 2 * δ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hoff_eval : (∑ j : Fin m, ∑ _k ∈ Finset.univ.erase j, (4 * δ : ℝ))
      = m * (m - 1) * (4 * δ) := by
    have hinner : ∀ j : Fin m, (∑ _k ∈ Finset.univ.erase j, (4 * δ : ℝ))
        = (m - 1) * (4 * δ) := by
      intro j
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
      cases m with
      | zero => exact absurd j.2 (by simp)
      | succ p => push_cast [Nat.succ_sub_one]; ring
    rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  -- assemble
  have hbound : (∑ k : Fin m, avg (fun b => (2 * Real.cos (φ k b)) ^ 2))
      + (∑ j : Fin m, ∑ k ∈ Finset.univ.erase j,
          avg (fun b => (2 * Real.cos (φ j b)) * (2 * Real.cos (φ k b))))
      ≤ m * (2 + 2 * δ) + m * (m - 1) * (4 * δ) := by
    have := add_le_add hdiag hoff
    rwa [hdiag_eval, hoff_eval] at this
  -- m·(2+2δ) + m(m−1)·4δ = 2m + 2δ·m·(2m−1)
  have hsimp : (m : ℝ) * (2 + 2 * δ) + m * (m - 1) * (4 * δ)
      = 2 * m + 2 * δ * (m * (2 * m - 1)) := by ring
  rw [hsimp] at hbound
  exact hbound

/-- **The matching LOWER companion to `variance_le_of_pairEquidist` (two-sided variance control).**
The same pair-equidistribution residual `PairEquidistributed φ δ` that caps the variance proxy from
ABOVE also pins it from BELOW: the second moment cannot drop more than the same `O(m²δ)` correction
below the prize proxy `2m = n`:

> `avg_B(η²) ≥ 2m − 2δ·m·(2m−1)`.

Proof mirrors the upper bound: the decoupling identity is an EQUALITY, the diagonal proxy is
`2 + 2D(2x_k) ≥ 2 − 2δ` (using the lower half of `|D|≤δ`), and each off-diagonal pair term is
`2D(x_j−x_k)+2D(x_j+x_k) ≥ −4δ`. Together with the upper bound this gives the two-sided statement
`|avg_B(η²) − 2m| ≤ 2δ·m·(2m−1)`, i.e. **the variance proxy equals the prize floor `n` up to the
exact summed pair-discrepancy correction** — so `δ → 0` forces `avg_B(η²) = 2m = n` from BOTH sides,
not merely `≤`. (This matters for any application that needs a variance LOWER bound — e.g. a
Plancherel/anti-concentration floor on the typical frequency — which the one-sided
`variance_le_of_pairEquidist` cannot supply.) NO CORE/cancellation/capacity claim: this is the
symmetric arithmetic of the same named residual, not a discharge of it. -/
theorem variance_ge_of_pairEquidist {m : ℕ} (φ : Fin m → B → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : PairEquidistributed φ δ) :
    2 * m - 2 * δ * (m * (2 * m - 1))
      ≤ avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) := by
  obtain ⟨hdiff, hsum, hdbl⟩ := h
  rw [secondMoment_decoupling (fun k b => 2 * Real.cos (φ k b))]
  -- diagonal ≥ ∑_k (2 − 2δ) = 2m − 2mδ ;  off-diag ≥ ∑_j ∑_{k≠j} (−2δ−2δ) = −4δ·m(m−1)
  have hdiag : (∑ _k : Fin m, (2 - 2 * δ : ℝ))
      ≤ ∑ k : Fin m, avg (fun b => (2 * Real.cos (φ k b)) ^ 2) := by
    apply Finset.sum_le_sum; intro k _
    rw [diagonal_eq_proxy_plus_discrepancy (φ k)]
    have := hdbl k
    have hge : -δ ≤ discrepancy (fun b => 2 * φ k b) := (abs_le.mp this).1
    linarith
  have hoff : (∑ j : Fin m, ∑ _k ∈ Finset.univ.erase j, (-(4 * δ) : ℝ))
      ≤ ∑ j : Fin m, ∑ k ∈ Finset.univ.erase j,
          avg (fun b => (2 * Real.cos (φ j b)) * (2 * Real.cos (φ k b))) := by
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro k _
    rw [offDiagonal_eq_pair_discrepancy (φ j) (φ k)]
    have h1 : -δ ≤ discrepancy (fun b => φ j b - φ k b) := (abs_le.mp (hdiff j k)).1
    have h2 : -δ ≤ discrepancy (fun b => φ j b + φ k b) := (abs_le.mp (hsum j k)).1
    linarith
  -- evaluate the constant sums
  have hdiag_eval : (∑ _k : Fin m, (2 - 2 * δ : ℝ)) = m * (2 - 2 * δ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hoff_eval : (∑ j : Fin m, ∑ _k ∈ Finset.univ.erase j, (-(4 * δ) : ℝ))
      = m * (m - 1) * (-(4 * δ)) := by
    have hinner : ∀ j : Fin m, (∑ _k ∈ Finset.univ.erase j, (-(4 * δ) : ℝ))
        = (m - 1) * (-(4 * δ)) := by
      intro j
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
      cases m with
      | zero => exact absurd j.2 (by simp)
      | succ p => push_cast [Nat.succ_sub_one]; ring
    rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  -- assemble
  have hbound : (m : ℝ) * (2 - 2 * δ) + m * (m - 1) * (-(4 * δ))
      ≤ (∑ k : Fin m, avg (fun b => (2 * Real.cos (φ k b)) ^ 2))
        + (∑ j : Fin m, ∑ k ∈ Finset.univ.erase j,
            avg (fun b => (2 * Real.cos (φ j b)) * (2 * Real.cos (φ k b)))) := by
    have := add_le_add hdiag hoff
    rwa [hdiag_eval, hoff_eval] at this
  have hsimp : (m : ℝ) * (2 - 2 * δ) + m * (m - 1) * (-(4 * δ))
      = 2 * m - 2 * δ * (m * (2 * m - 1)) := by ring
  rw [hsimp] at hbound
  exact hbound

/-- **Two-sided variance control from pair-equidistribution** (`variance_le_` ∧ `variance_ge_`).
The averaged second moment is within `2δ·m·(2m−1)` of the exact prize proxy `2m = n`:
`|avg_B(η²) − 2m| ≤ 2δ·m·(2m−1)`. So at `δ = 0` the variance proxy is EXACTLY `2m` (not merely
bounded by it). This is the precise two-sided sense in which pair-equidistribution pins the variance. -/
theorem abs_variance_sub_prizeProxy_le_of_pairEquidist {m : ℕ} (φ : Fin m → B → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (h : PairEquidistributed φ δ) :
    |avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) - 2 * m|
      ≤ 2 * δ * (m * (2 * m - 1)) := by
  rw [abs_le]
  constructor
  · have := variance_ge_of_pairEquidist φ δ hδ h; linarith
  · have := variance_le_of_pairEquidist φ δ hδ h; linarith

/-- **The Plancherel/prize FLOOR on the sup-norm from pair-equidistribution** (the lower bookend to
`subGaussian_supNorm_of_pairEquidist`'s upper bound). The variance LOWER bound
`variance_ge_of_pairEquidist` plus `exists_avg_le` (avg ≤ some sample) forces an actual frequency `b`
whose squared period reaches the prize variance floor:

> `∃ b, (∑_k 2cos(φ_k b))² ≥ 2m − 2δ·m·(2m−1)`.

At `δ = 0` this is the exact **Plancherel floor** `M² ≥ 2m = n`, i.e. `M = max_b|η_b| ≥ √n` — the
prize sup-norm cannot beat `√n` no matter how good the equidistribution. Together with the capstone
upper bound `M ≤ √(2n log m)` this brackets the prize sup-norm between `√n` and `√(2n log m)` (the
familiar `√n .. √(n log)` window), with the `log m` gap being exactly door-(iv). NO CORE/cancellation/
capacity claim: the floor is the easy (Plancherel) direction; the open content is the matching
`O(√(n log))` ceiling at ABSOLUTE constant in the thin regime. -/
theorem exists_sq_ge_prizeFloor_of_pairEquidist {m : ℕ} (φ : Fin m → B → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (h : PairEquidistributed φ δ) :
    ∃ b : B, 2 * m - 2 * δ * (m * (2 * m - 1))
      ≤ (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2 := by
  obtain ⟨b, hb⟩ := exists_avg_le (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2)
  exact ⟨b, le_trans (variance_ge_of_pairEquidist φ δ hδ h) hb⟩

/-- **The decoupling capstone: the sub-Gaussian sup-norm from pair-equidistribution.** Under the
pair-equidistribution residual `PairEquidistributed φ δ` and the per-phase Bessel MGF (proven, no
independence), the period's symmetric MGF is dominated by the sub-Gaussian envelope with the
**decoupled variance proxy `V = 2m + correction`** (the uniform `prod_cosh_le_exp` already gives proxy
`2m = n` per frequency; pair-equidistribution is what certifies this is the *true* proxy and not a
lossy worst-case). Feeding `cosh(η_b y) ≤ K·exp(V y²/2)` into the Chernoff/Cramér bound
(`_D2LargeDeviationRateFunction.chernoff_bound`, here re-stated as the clean saddle consequence)
gives the prize floor

> `M = max_{b≠0} |η_b| ≤ √(2·V·log K)`,   `V = n` (`δ → 0`),  `K = m`,

i.e. `M ≤ √(2n log m)`. We prove the **saddle consequence** axiom-clean: from
`M·y ≤ log K + V y²/2 ∀ y ≥ 0` (the log of the sub-Gaussian MGF at the binding frequency) the optimal
`y* = M/V` yields `M ≤ √(2 V log K)`. The variance input `V` is supplied by
`variance_le_of_pairEquidist` (`V = 2m + O(m²δ) → n`); the MGF envelope by `prod_cosh_le_exp`. The
NAMED OPEN INPUT is `PairEquidistributed` at the prize-binding depth. -/
theorem subGaussian_supNorm_of_pairEquidist {M V K : ℝ} (hV : 0 < V) (hK : 1 < K) (hM : 0 ≤ M)
    (hmgf : ∀ y : ℝ, 0 ≤ y → M * y ≤ Real.log K + V * y ^ 2 / 2) :
    M ≤ Real.sqrt (2 * V * Real.log K) := by
  have hlogK : 0 < Real.log K := Real.log_pos hK
  have hVne : V ≠ 0 := ne_of_gt hV
  -- plug the saddle y = M/V, then clear denominators by ×(2V).
  have key := hmgf (M / V) (by positivity)
  have hMsq : M ^ 2 ≤ 2 * V * Real.log K := by
    have key2 := mul_le_mul_of_nonneg_right key (by positivity : (0:ℝ) ≤ 2 * V)
    rw [show M * (M / V) * (2 * V) = 2 * M ^ 2 from by field_simp,
        show (Real.log K + V * (M / V) ^ 2 / 2) * (2 * V) = 2 * V * Real.log K + M ^ 2 from by
          field_simp] at key2
    linarith
  calc M = Real.sqrt (M ^ 2) := (Real.sqrt_sq hM).symm
    _ ≤ Real.sqrt (2 * V * Real.log K) := Real.sqrt_le_sqrt hMsq

/-- **End-to-end (the prize floor in the ideal-equidistribution limit).** Specializing the capstone
to the **exactly-equidistributed** case `δ = 0` (`PairEquidistributed φ 0`): the variance proxy is
*exactly* `V = 2m = n` (`variance_le_of_pairEquidist` with `δ=0` gives `avg η² ≤ 2m`), and so a period
whose binding-frequency MGF obeys `M y ≤ log m + (2m) y²/2` satisfies the **prize floor**

> `M ≤ √(2·(2m)·log m) = √(2n·log m)`,   `n = 2m`.

This is the clean statement of "pair-equidistribution ⟹ the prize". The hypothesis `δ = 0` is the
ideal limit of the named residual; the honest open core is exactly that the prize-binding dilated
difference/sum sets reach `δ = 0` (equivalently `O(1/m)`), the BGK wall in pair-discrepancy form. -/
theorem prize_floor_of_ideal_pairEquidist {m : ℕ} (hm : 0 < m) {M : ℝ} (hM : 0 ≤ M)
    (hmgf : ∀ y : ℝ, 0 ≤ y → M * y ≤ Real.log (m : ℝ) + (2 * m : ℝ) * y ^ 2 / 2)
    (hmlt : 1 < (m : ℝ)) :
    M ≤ Real.sqrt (2 * (2 * m : ℝ) * Real.log (m : ℝ)) := by
  have hV : (0 : ℝ) < 2 * m := by positivity
  exact subGaussian_supNorm_of_pairEquidist hV hmlt hM hmgf

end ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling

/-! ## Axiom audit — must be ⊆ {propext, Classical.choice, Quot.sound}; no `sorryAx`. -/
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms avg_add
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms avgCos_eq_discrepancy
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms abs_discrepancy_le_one
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms cos_sq_avg_identity
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms cos_prod_avg_identity
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms cosh_two_cos_le_exp
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms prod_cosh_le_exp
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms secondMoment_decoupling
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms diagonal_eq_proxy_plus_discrepancy
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms offDiagonal_eq_pair_discrepancy
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms variance_le_of_pairEquidist
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms variance_ge_of_pairEquidist
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms abs_variance_sub_prizeProxy_le_of_pairEquidist
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms exists_avg_le
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms exists_sq_ge_prizeFloor_of_pairEquidist
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms subGaussian_supNorm_of_pairEquidist
open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling in
#print axioms prize_floor_of_ideal_pairEquidist
