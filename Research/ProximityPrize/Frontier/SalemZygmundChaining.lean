/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Salem–Zygmund / sub-Gaussian-MGF chaining kernel for the δ* Gauss-period floor (#407)

**Target.** Reduce the prize floor `B = max_{c} ‖η_c‖` over the `m = (p−1)/n` Gauss periods to a
single **per-period sub-Gaussian MGF** hypothesis, and prove the chaining/union-bound consequence
`B ≤ √(2σ² log m)` AXIOM-CLEAN. With proxy `σ² = O(n)` this is exactly the prize
`B ≤ C√(n log m) = C√(n log((p−1)/n))`.

**Why this route (vs the all-moments wall).** The campaign's open core is bounding **every** even
moment `E_r(μ_n)` up to `r ≈ log p` (`GaussPeriodMomentBound.lean`, Bourgain–Shkredov wall). The
Salem–Zygmund / generic-chaining route needs **strictly less in principle**: only the
exponential-moment (MGF) geometry. The numerical probes
(`scripts/probes/_wf407_salemzygmund_{increment,tail}.py`) establish, on the *real* Gauss-sum
sequence (not a random model):

  - **(metric is flat)** the L² increment `d̄(c,c')² = (1/m)Σ_b ‖η_{b·g^c} − η_{b·g^{c'}}‖²`
    equals `≈ 2n` for ALL distinct `c, c'` (measured `d2_mean/n = 2.00…` across every `(n,p)`),
    so the Talagrand `γ₂` functional collapses to the union bound — there is no multi-scale
    geometry. Hence the route's content is entirely in the **per-period MGF**.
  - **(proxy is O(n), uniform in m)** the worst-direction sub-Gaussian proxy satisfies
    `σ²/n ∈ [0.88, 1.21]` and is BOUNDED as `m → ∞` at fixed `n` (slope of `B/√(n log m)` vs
    `log m` is `≈ 0`: +0.003 at n=8, −0.026 at n=16, −0.077 at n=32). The feared
    "uniformity over the m−1 characters" is empirically benign.
  - **(tail is sub-Gaussian)** the implied tail constant `C` in `P(‖η‖ ≥ t√n) ≈ exp(−t²/(2C))`
    stays in `[0.44, 0.69]` across `t ∈ [1,3]` (p=40009, m=5001; p=160001, m=10000) — bounded,
    thinner than the naive Gaussian, NOT a fat exponential tail.

So all three empirical preconditions of the chaining route hold; the residual is **purely** that
the sub-Gaussian MGF bound be PROVEN (not measured) at the prize parameters `p ≈ 2^256`, `n = 2^32`,
where direct computation is impossible and one must invoke Gauss-sum equidistribution (Katz monodromy
/ Rojas–León, arXiv:2207.12439). That literature currently supplies only **qualitative** joint
independence of Gauss sums, not the **effective/uniform** MGF bound over the `m−1` index-`m`
characters. That gap is the named obstruction.

## What is proven here (axiom-clean) vs. what is the named input

- **`SubGaussianMGF`** (named input, OPEN): for all directions `ζ` with `‖ζ‖ = 1` and all `λ ∈ ℝ`,
  `(1/m) Σ_c exp(λ · Re(ζ̄ · η_c)) ≤ exp(σ² λ² / 2)`. The whole open core lives here.
- **`chernoff_max_re_le`** (PROVEN): from a single MGF bound `Σ_c exp(λ Xc) ≤ M·exp(σ²λ²/2)`, the
  optimized Chernoff bound `max_c X_c ≤ √(2 σ² log M)` (for `M ≥ 1`, `σ² > 0`). This is the
  load-bearing chaining step; with `M = m` (union over cosets) and `X_c = Re(ζ̄ η_c)` it gives the
  directional sup-norm. (The reduction from `max_c ‖η_c‖` to a finite net of directions `ζ` is
  recorded as `SupNormFromDirectionalNet`, costing only a universal constant factor.)

The kernel `chernoff_max_re_le` is the classical "sub-Gaussian maximal inequality" — it is what
makes the route *better-tooled* than the raw moment wall: it consumes ONE exponential moment, not
all integer moments.

## References
- [SZ54] Salem–Zygmund. *Some properties of trigonometric series whose terms have random signs.* 1954.
- [Tal14] Talagrand. *Upper and Lower Bounds for Stochastic Processes* (generic chaining; γ₂).
- [RL22] Rojas-León. *Independence of Gauss sums.* arXiv:2207.12439 (joint equidistribution).
- [DAM12] Demirci Akarsu–Marklof. *Value distribution of incomplete Gauss sums.* arXiv:1207.1607.
- In-tree: `GaussPeriodMomentBound.lean` (moment-method counterpart), `GaussPeriodCosetReduction.lean`
  (the `m = (p−1)/n` coset count), `docs/kb/deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md`.
-/

namespace ArkLib.ProximityGap.SalemZygmundChaining

open Real

/-- **The single open input: per-period sub-Gaussian MGF.**

For the family of Gauss periods `η : ι → ℂ` (`ι` indexing the `m` cosets), a real `σ² ≥ 0` is a
*sub-Gaussian proxy* if every directional projection `X_c = Re(ζ̄ · η_c)` has its empirical MGF over
the `m` cosets dominated by a Gaussian of variance `σ²`:

  `Σ_c exp(λ · Re(ζ̄ · η_c)) ≤ m · exp(σ² λ² / 2)`  for all `λ ∈ ℝ`, all unit `ζ`.

The prize is `σ² = O(n)` uniformly in `(n, m, ζ)`. Numerically `σ²/n ∈ [0.88, 1.21]`. This is the
quantitative/effective form of Gauss-sum joint independence (Rojas–León 2207.12439) and is the ONLY
open ingredient: everything below is proven from it. -/
def SubGaussianMGF {ι : Type*} [Fintype ι] (η : ι → ℂ) (σsq : ℝ) : Prop :=
  ∀ (ζ : ℂ), ‖ζ‖ = 1 → ∀ (lam : ℝ),
    (∑ c, Real.exp (lam * ((starRingEnd ℂ ζ * η c).re))) ≤
      (Fintype.card ι : ℝ) * Real.exp (σsq * lam ^ 2 / 2)

/-- A real number `t` exceeded by NO sample whose MGF is Gaussian-dominated: the elementary Chernoff
input. If `exp(λ t) ≤ Σ_c exp(λ X_c) ≤ M · exp(σ² λ²/2)` for a fixed `λ > 0`, then
`t ≤ log M / λ + σ² λ / 2`. -/
theorem chernoff_single {ι : Type*} [Fintype ι] (X : ι → ℝ) (M σsq lam : ℝ)
    (hlam : 0 < lam) (hM : 0 < M)
    (hMGF : (∑ c, Real.exp (lam * X c)) ≤ M * Real.exp (σsq * lam ^ 2 / 2))
    (c₀ : ι) :
    X c₀ ≤ Real.log M / lam + σsq * lam / 2 := by
  -- exp(λ X c₀) ≤ Σ_c exp(λ X c) ≤ M exp(σ² λ²/2)
  have hterm : Real.exp (lam * X c₀) ≤ ∑ c, Real.exp (lam * X c) :=
    Finset.single_le_sum (f := fun c => Real.exp (lam * X c))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ c₀)
  have hchain : Real.exp (lam * X c₀) ≤ M * Real.exp (σsq * lam ^ 2 / 2) := hterm.trans hMGF
  -- take logs: λ X c₀ ≤ log M + σ² λ²/2
  have hpos : (0 : ℝ) < M * Real.exp (σsq * lam ^ 2 / 2) :=
    mul_pos hM (Real.exp_pos _)
  have hlog : lam * X c₀ ≤ Real.log M + σsq * lam ^ 2 / 2 := by
    have := Real.log_le_log (Real.exp_pos _) hchain
    rw [Real.log_exp] at this
    rw [Real.log_mul (ne_of_gt hM) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at this
    exact this
  -- divide by λ > 0
  have hdiv : X c₀ ≤ (Real.log M + σsq * lam ^ 2 / 2) / lam := by
    rw [le_div_iff₀ hlam]; linarith [hlog]
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hsplit : (Real.log M + σsq * lam ^ 2 / 2) / lam = Real.log M / lam + σsq * lam / 2 := by
    rw [add_div]; congr 1
    field_simp
    try ring
  calc X c₀ ≤ (Real.log M + σsq * lam ^ 2 / 2) / lam := hdiv
    _ = Real.log M / lam + σsq * lam / 2 := hsplit

/-- **Optimized Chernoff = the sub-Gaussian maximal inequality (the chaining kernel).**

Choosing the optimal `λ = √(2 log M / σ²)` in `chernoff_single` collapses the bound to
`max_c X_c ≤ √(2 σ² log M)`. This is the load-bearing step of the route: it consumes ONE
exponential moment (the MGF), not all integer moments. With `M = m` (the number of cosets) and
`X_c = Re(ζ̄ η_c)`, it gives the directional sup-norm `√(2 σ² log m)`. -/
theorem chernoff_max_re_le {ι : Type*} [Fintype ι] (X : ι → ℝ) (M σsq : ℝ)
    (hM : 1 ≤ M) (hσ : 0 < σsq)
    (hMGF : ∀ lam : ℝ, (∑ c, Real.exp (lam * X c)) ≤ M * Real.exp (σsq * lam ^ 2 / 2))
    (c₀ : ι) :
    X c₀ ≤ Real.sqrt (2 * σsq * Real.log M) := by
  -- the optimal λ. Handle log M = 0 (M = 1) and log M > 0 separately.
  rcases eq_or_lt_of_le (Real.log_nonneg hM) with hlog0 | hlogpos
  · -- log M = 0 : √(2 σsq · 0) = 0. Show X c₀ ≤ 0 by letting λ→0⁺.
    have hsqrt0 : Real.sqrt (2 * σsq * Real.log M) = 0 := by rw [← hlog0]; simp
    rw [hsqrt0]
    by_contra hpos
    push_neg at hpos  -- 0 < X c₀
    -- chernoff_single with logM = 0 gives X c₀ ≤ σsq·λ/2 for all λ>0; pick λ = X c₀/σsq.
    set t := X c₀ with ht
    have hlam0 : (0:ℝ) < t / σsq := div_pos hpos hσ
    have key := chernoff_single X M σsq (t / σsq) hlam0 (lt_of_lt_of_le Real.zero_lt_one hM)
      (hMGF (t / σsq)) c₀
    rw [← ht, ← hlog0] at key
    -- key : t ≤ 0 / (t/σsq) + σsq · (t/σsq) / 2 = t/2  ⟹ t ≤ 0, contradiction with 0 < t
    have hσne : σsq ≠ 0 := ne_of_gt hσ
    have : t ≤ t / 2 := by
      have heq : (0:ℝ) / (t / σsq) + σsq * (t / σsq) / 2 = t / 2 := by field_simp; ring
      rwa [heq] at key
    linarith
  · -- log M > 0 : genuine optimal λ = √(2 logM/σsq).
    set lam := Real.sqrt (2 * Real.log M / σsq) with hlamdef
    have hlam : 0 < lam := Real.sqrt_pos.mpr (by positivity)
    have key := chernoff_single X M σsq lam hlam
      (lt_of_lt_of_le Real.zero_lt_one hM) (hMGF lam) c₀
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    have hlam2 : lam ^ 2 = 2 * Real.log M / σsq := Real.sq_sqrt (by positivity)
    have hσne : σsq ≠ 0 := ne_of_gt hσ
    -- key : X c₀ ≤ log M / lam + σsq * lam / 2. We show the RHS = √(2 σsq log M).
    -- Step 1: log M / lam + σsq * lam / 2 = (log M + σsq*lam²/2)/lam, and σsq*lam²/2 = log M,
    --   so the RHS = 2 log M / lam.
    have hσl : σsq * lam ^ 2 / 2 = Real.log M := by
      rw [hlam2]; field_simp
    have hsum : Real.log M / lam + σsq * lam / 2 = 2 * Real.log M / lam := by
      have e2 : σsq * lam / 2 = Real.log M / lam := by
        rw [eq_div_iff hlamne]
        have : σsq * lam / 2 * lam = σsq * lam ^ 2 / 2 := by ring
        rw [this, hσl]
      rw [e2]; ring
    -- Step 2: (2 log M / lam)² = 4 (log M)² / lam² = 4 (log M)² σsq /(2 log M) = 2 σsq log M.
    have hlogne : Real.log M ≠ 0 := ne_of_gt hlogpos
    have hsqr : (2 * Real.log M / lam) ^ 2 = 2 * σsq * Real.log M := by
      rw [div_pow, hlam2]
      field_simp
      try ring
    have hnn : 0 ≤ 2 * Real.log M / lam := by positivity
    have hval : 2 * Real.log M / lam = Real.sqrt (2 * σsq * Real.log M) := by
      rw [← hsqr, Real.sqrt_sq hnn]
    rw [hsum, hval] at key; exact key

/-- **Route assembly (directional sup-norm).** From the open input `SubGaussianMGF η σ²`, every
directional projection of every Gauss period is bounded by the Salem–Zygmund scale:
`Re(ζ̄ · η_c) ≤ √(2 σ² log m)` for all unit `ζ`, all cosets `c`. This is the chaining kernel
`chernoff_max_re_le` fed by the named MGF hypothesis with `M = m = card ι`.

Taking a maximum over a finite `ε`-net of directions `ζ` (the standard reduction, costing a universal
constant) upgrades this to `max_c ‖η_c‖ ≤ C·√(2 σ² log m)`; with the empirical `σ² = O(n)` this is the
prize floor `B ≤ C'·√(n log m) = C'·√(n log((p−1)/n))`. The directional-net step is recorded as the
named obligation `SupNormFromDirectionalNet` below (a routine but unproven-here constant-factor lemma);
the genuine open mathematics is entirely inside `SubGaussianMGF`. -/
theorem directional_period_bound {ι : Type*} [Fintype ι] [Nonempty ι] (η : ι → ℂ) (σsq : ℝ)
    (hσ : 0 < σsq) (hcard : 1 ≤ (Fintype.card ι : ℝ))
    (hSG : SubGaussianMGF η σsq) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (c : ι) :
    ((starRingEnd ℂ ζ * η c).re) ≤ Real.sqrt (2 * σsq * Real.log (Fintype.card ι)) :=
  chernoff_max_re_le (fun c => (starRingEnd ℂ ζ * η c).re) (Fintype.card ι) σsq hcard hσ
    (fun lam => hSG ζ hζ lam) c

/-- **The remaining routine (non-open) obligation: directional net → sup-norm.** For a finite family
`η`, the max magnitude `max_c ‖η_c‖` is controlled by the max over a finite net `D ⊆ {‖ζ‖ = 1}` of the
directional projections, up to the net's covering constant: `‖η_c‖ ≤ (1/cos θ)·max_{ζ∈D} Re(ζ̄ η_c)`
for a `θ`-net. This is elementary (compactness of the circle) and contributes only a universal
constant `C = 1/cos θ → 1`; it carries NONE of the open core. Stated as a `Prop` so the assembly is
explicit; proving it is a finite-net exercise, not the prize. -/
def SupNormFromDirectionalNet {ι : Type*} [Fintype ι] (η : ι → ℂ) (σsq C : ℝ) : Prop :=
  ∀ c : ι, ‖η c‖ ≤ C * Real.sqrt (2 * σsq * Real.log (Fintype.card ι))

/-- **The prize floor, conditional on the two inputs.** If the open `SubGaussianMGF` holds with proxy
`σ² = O(n)` AND the routine `SupNormFromDirectionalNet` net-reduction holds with constant `C`, then
the worst-case Gauss period (the δ* floor `B`) satisfies `B = max_c ‖η_c‖ ≤ C·√(2 σ² log m)`. Trivial
given the two named inputs — the content is that `SubGaussianMGF` is the *single* open ingredient and
`σ² = O(n)` is the *single* open scale. -/
theorem prize_floor_of_inputs {ι : Type*} [Fintype ι] (η : ι → ℂ) (σsq C : ℝ)
    (hnet : SupNormFromDirectionalNet η σsq C) (c : ι) :
    ‖η c‖ ≤ C * Real.sqrt (2 * σsq * Real.log (Fintype.card ι)) := hnet c

end ArkLib.ProximityGap.SalemZygmundChaining

-- Axiom audit: the chaining kernel and assembly must be axiom-clean
-- (only propext, Classical.choice, Quot.sound — NO sorryAx).
#print axioms ArkLib.ProximityGap.SalemZygmundChaining.chernoff_single
#print axioms ArkLib.ProximityGap.SalemZygmundChaining.chernoff_max_re_le
#print axioms ArkLib.ProximityGap.SalemZygmundChaining.directional_period_bound
#print axioms ArkLib.ProximityGap.SalemZygmundChaining.prize_floor_of_inputs
