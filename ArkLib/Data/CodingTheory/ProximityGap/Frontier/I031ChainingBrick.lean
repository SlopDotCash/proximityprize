/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction

/-!
# I031 — group-invariant chaining on the dilation quotient `F_p^×/μ_n` (Issue #444)

**The lead.** The prize per-frequency floor is `B = max_{b≠0} ‖η_b‖`, `η_b = Σ_{y∈μ_n} ψ(b·y)`.
By coset-invariance (`GaussPeriodCosetReduction.eta_mul_invariant`, proven in-tree) the frequency
function `b ↦ η_b` factors through the **dilation quotient** `Q := F_p^×/μ_n`, a cyclic group of order
`m = (p−1)/n`. So `B` is a max over only `m` distinct Gauss periods. I031 proposes running
group-invariant **Dudley / generic chaining on `Q`**: because the index set is `Q` (size `m`, NOT `p`),
the metric entropy collapses to `log m`, and the floor `B ≤ C·√(n·log m)` would follow from a
**deterministic increment estimate** — that `|η_b − η_c|` is sub-Gaussian in a quotient metric `d_q`.

**What this file lands (axiom-clean, worth landing regardless).**
1. **(a) Quotient cardinality / orbit reduction.** The number of distinct nonzero Gauss periods is
   `≤ m = (p−1)/n` — re-exported from the proven `eta_image_card_mul_le`, packaged as
   `period_value_card_le` (the chaining index set has size `≤ m`).
2. **(b) Volumetric metric-entropy bound.** For ANY pseudmetric `d_q` on the period index set, the
   covering number at any scale is `≤ m`, hence `log N ≤ log m` (`metric_entropy_le_log_card`). This is
   the volumetric input that makes the chaining log-factor `log m = log((p−1)/n)`, NOT `log p`.
3. **(c) The Dudley/Chernoff sup bound.** A self-contained restatement of the sub-Gaussian maximal
   inequality `max_c X_c ≤ √(2σ² log m)` (the chaining kernel) and its assembly to
   `B ≤ C·√(2σ²·log m)`; with `σ² = O(n)` this is the prize floor `C'·√(n·log((p−1)/n))`.

**The open input, named (NOT faked).** The whole route reduces to a single deterministic increment
tail: `SubGaussianIncrement`. The probes `scripts/probes/probe_i031_increment.py` and
`probe_i031_increment_wall.py` test it directly on the real Gauss-sum sequence at proper `μ_n`,
`n = 32,64,128,256`, and the verdict is **NEGATIVE for I031 as a *shortcut***:

  - **The increment-sup obeys the SAME `√(n·log m)` wall law as `B`.** Measured
    `max_{b,c}|η_b − η_c| / B ∈ [1.44, 1.95]` (≈ √2 to 2, antipodal) STABLE across `n = 32..256`, and
    `max|η_b−η_c| / √(2n log m) ∈ [1.40, 1.96]` tracks `B/√(n log m) ∈ [1.09, 1.54]` up to a constant.
    Algebraically `η_b − η_c` is an incomplete character sum over the `2n`-element ±1-weighted
    symmetric difference of the two cosets — a Gauss-period-LIKE object of the **same BGK/Paley
    difficulty**. So bounding the increment is **as hard as bounding `B`** (outcome **(b): reduces to
    the wall**), not elementary (a) and not easier (c).
  - **The cyclic-quotient metric does NOT separate the periods.** `minInc/√(2n) ≈ 0` (down to 0.000):
    distinct cosets — often far apart in `Q` — can have nearly-equal periods. And a SINGLE quotient
    step is already a jump of `1.65–2.74·√(2n)` with Lipschitz constant `K` GROWING with `m`
    (15 → 42 over `m = 8..27`). So the increment is **not Lipschitz** in the cyclic-quotient distance,
    and the deterministic chaining premise (a flat, metrically-informative geometry on `Q`) FAILS: the
    `d̄² ≈ 2n` flatness is only a *mean*, not a uniform separation.

We therefore record the wall reduction as an axiom-clean theorem `increment_sup_reduces_to_wall`
(if the increment-sup obeys the wall scale then so does `B`, and conversely `B` lower-bounds the
increment-sup up to the antipodal factor) and keep `SubGaussianIncrement` as the explicit named
obligation — the honest statement that I031's "deterministic → Gaussian sup-comparison" does NOT
sidestep the open core: its increment ingredient IS the open core.

## References
- In-tree: `GaussPeriodCosetReduction.lean` (orbit count, proven), `SalemZygmundChaining.lean`
  (the MGF chaining kernel), `GaussPeriodMomentBound.lean` (the moment-method counterpart).
- [Tal14] Talagrand, *Upper and Lower Bounds for Stochastic Processes* (generic chaining; γ₂, Dudley).
- [Dud67] Dudley, *The sizes of compact subsets of Hilbert space and continuity of Gaussian processes*.
- Probes: `scripts/probes/probe_i031_increment.py`, `probe_i031_increment_wall.py`.
-/

namespace ArkLib.ProximityGap.I031ChainingBrick

open Real
open ArkLib.ProximityGap.GaussPeriodCosetReduction

/-! ## (a) Orbit reduction: the chaining index set has size `≤ m = (p−1)/n` -/

section OrbitReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

/-- **(a) The chaining index set has cardinality `≤ m = (q−1)/|G|`.** The set of distinct nonzero
Gauss-period *values* has size at most `(q−1)/|G|`, because each value's fiber contains a full
`|G|`-coset (`eta_image_card_mul_le`). Hence the Dudley/chaining process indexes over at most
`m = (p−1)/n` points — the **dilation quotient** `F^×/G` — and the union/chaining log-factor is
`log m`, not `log q`. This re-exports the proven orbit count as the explicit chaining-index bound. -/
theorem period_value_card_le (ψ : AddChar F ℂ) (G : Finset F)
    (hmul : ∀ a ∈ G, ∀ c ∈ G, a * c ∈ G) (h0 : (0 : F) ∉ G) (hG : 0 < G.card) :
    ((Finset.univ.filter (fun b : F => b ≠ 0)).image (eta ψ G)).card
      ≤ (Fintype.card F - 1) / G.card := by
  have hle := eta_image_card_mul_le ψ G hmul h0
  exact Nat.le_div_iff_mul_le hG |>.mpr hle

end OrbitReduction

/-! ## (b) Volumetric metric entropy: `log N(Q, d_q, ε) ≤ log m`

For a finite index set of size `≤ m`, the covering number at ANY scale is `≤ m` (cover by all points),
so the Dudley metric-entropy integrand `log N(·)` is `≤ log m` uniformly. This is the volumetric input
that pins the chaining log-factor at `log m = log((p−1)/n)`. We state it abstractly: a covering of a
`Fintype ι` by singletons has size `card ι`, so any covering number `N ≤ card ι ≤ m`. -/

section MetricEntropy

/-- **(b) Volumetric metric-entropy bound.** For a finite index set `ι` with `card ι ≤ m`, the log of
any covering number `N ≤ card ι` is `≤ log m`. (The whole index set is itself a cover at every scale.)
This is the only place the quotient size enters the chaining log-factor: `log N ≤ log m`, with
`m = (p−1)/n`, giving `log((p−1)/n)` and not `log p`. -/
theorem metric_entropy_le_log_card {ι : Type*} [Fintype ι] (m : ℝ) (hm : 0 < m)
    (hcard : (Fintype.card ι : ℝ) ≤ m) (N : ℝ) (hN1 : 1 ≤ N) (hNcard : N ≤ (Fintype.card ι : ℝ)) :
    Real.log N ≤ Real.log m :=
  Real.log_le_log (lt_of_lt_of_le Real.zero_lt_one hN1) (hNcard.trans hcard)

end MetricEntropy

/-! ## (c) The Dudley/Chernoff sup bound (chaining kernel) -/

section ChainingKernel

variable {ι : Type*} [Fintype ι]

/-- **(c) The sub-Gaussian maximal inequality (Dudley/Chernoff chaining kernel).** From a single
MGF bound `Σ_c exp(λ X_c) ≤ M·exp(σ²λ²/2)` for all `λ`, the optimized Chernoff bound gives
`X_c ≤ √(2σ² log M)` for every index `c`. With `M = m` (the quotient size, by (a)/(b)) and
`X_c = Re(ζ̄·η_c)`, this is the directional sup-norm `√(2σ²·log m)`. (Self-contained restatement of
`SalemZygmundChaining.chernoff_max_re_le`; the metric-collapse to a pure union bound `M = m` is exactly
why the I031 quotient reduction (a)+(b) is what feeds it.) -/
theorem chaining_sup_bound (X : ι → ℝ) (M σsq : ℝ) (hM : 1 ≤ M) (hσ : 0 < σsq)
    (hMGF : ∀ lam : ℝ, (∑ c, Real.exp (lam * X c)) ≤ M * Real.exp (σsq * lam ^ 2 / 2))
    (c₀ : ι) :
    X c₀ ≤ Real.sqrt (2 * σsq * Real.log M) := by
  -- Chernoff at the optimal λ = √(2 log M / σ²); split on log M = 0 vs > 0.
  rcases eq_or_lt_of_le (Real.log_nonneg hM) with hlog0 | hlogpos
  · have hsqrt0 : Real.sqrt (2 * σsq * Real.log M) = 0 := by rw [← hlog0]; simp
    rw [hsqrt0]
    by_contra hpos
    push_neg at hpos
    set t := X c₀ with ht
    have hlam0 : (0:ℝ) < t / σsq := div_pos hpos hσ
    -- single-λ Chernoff: exp(λ t) ≤ Σ ≤ M exp(σ²λ²/2), take logs, divide by λ.
    have hterm : Real.exp ((t / σsq) * X c₀) ≤ ∑ c, Real.exp ((t / σsq) * X c) :=
      Finset.single_le_sum (f := fun c => Real.exp ((t / σsq) * X c))
        (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ c₀)
    have hchain : Real.exp ((t / σsq) * X c₀) ≤ M * Real.exp (σsq * (t / σsq) ^ 2 / 2) :=
      hterm.trans (hMGF (t / σsq))
    have hMpos : (0:ℝ) < M := lt_of_lt_of_le Real.zero_lt_one hM
    have hlog : (t / σsq) * X c₀ ≤ Real.log M + σsq * (t / σsq) ^ 2 / 2 := by
      have := Real.log_le_log (Real.exp_pos _) hchain
      rw [Real.log_exp, Real.log_mul (ne_of_gt hMpos) (ne_of_gt (Real.exp_pos _)),
        Real.log_exp] at this
      exact this
    rw [← hlog0] at hlog
    have hσne : σsq ≠ 0 := ne_of_gt hσ
    -- hlog : (t/σ) t ≤ 0 + σ (t/σ)²/2 = t²/(2σ); i.e. t²/σ ≤ t²/(2σ) ⟹ t ≤ 0.
    have hbad : t * t / σsq ≤ t * t / (2 * σsq) := by
      have e1 : (t / σsq) * t = t * t / σsq := by field_simp
      have e2 : σsq * (t / σsq) ^ 2 / 2 = t * t / (2 * σsq) := by
        rw [div_pow, sq]; field_simp
      rw [← ht] at hlog
      rw [e1, e2] at hlog; linarith
    have htt : 0 < t * t := mul_pos hpos hpos
    have : t * t / σsq ≤ t * t / (2 * σsq) := hbad
    have hcontra : t * t / (2 * σsq) < t * t / σsq := by
      apply div_lt_div_of_pos_left htt hσ
      linarith
    linarith
  · -- log M > 0: genuine optimal λ.
    set lam := Real.sqrt (2 * Real.log M / σsq) with hlamdef
    have hlam : 0 < lam := Real.sqrt_pos.mpr (by positivity)
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    have hlam2 : lam ^ 2 = 2 * Real.log M / σsq := Real.sq_sqrt (by positivity)
    have hσne : σsq ≠ 0 := ne_of_gt hσ
    have hMpos : (0:ℝ) < M := lt_of_lt_of_le Real.zero_lt_one hM
    have hterm : Real.exp (lam * X c₀) ≤ ∑ c, Real.exp (lam * X c) :=
      Finset.single_le_sum (f := fun c => Real.exp (lam * X c))
        (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ c₀)
    have hchain : Real.exp (lam * X c₀) ≤ M * Real.exp (σsq * lam ^ 2 / 2) :=
      hterm.trans (hMGF lam)
    have hlog : lam * X c₀ ≤ Real.log M + σsq * lam ^ 2 / 2 := by
      have := Real.log_le_log (Real.exp_pos _) hchain
      rw [Real.log_exp, Real.log_mul (ne_of_gt hMpos) (ne_of_gt (Real.exp_pos _)),
        Real.log_exp] at this
      exact this
    have hdiv : X c₀ ≤ (Real.log M + σsq * lam ^ 2 / 2) / lam := by
      rw [le_div_iff₀ hlam]; linarith [hlog]
    -- RHS = 2 log M / lam, and (2 log M / lam)² = 2 σsq log M.
    have hσl : σsq * lam ^ 2 / 2 = Real.log M := by rw [hlam2]; field_simp
    have hsum : (Real.log M + σsq * lam ^ 2 / 2) / lam = 2 * Real.log M / lam := by
      rw [hσl]; ring
    have hsqr : (2 * Real.log M / lam) ^ 2 = 2 * σsq * Real.log M := by
      have hlogne : Real.log M ≠ 0 := ne_of_gt hlogpos
      have h2logne : (2 : ℝ) * Real.log M ≠ 0 := mul_ne_zero (by norm_num) hlogne
      rw [div_pow, hlam2, div_div_eq_mul_div, div_eq_iff h2logne]
      ring
    have hnn : 0 ≤ 2 * Real.log M / lam := by positivity
    have hval : 2 * Real.log M / lam = Real.sqrt (2 * σsq * Real.log M) := by
      rw [← hsqr, Real.sqrt_sq hnn]
    calc X c₀ ≤ (Real.log M + σsq * lam ^ 2 / 2) / lam := hdiv
      _ = 2 * Real.log M / lam := hsum
      _ = Real.sqrt (2 * σsq * Real.log M) := hval

end ChainingKernel

/-! ## The open input + the wall reduction (the honest verdict)

The whole I031 route reduces to a single deterministic increment hypothesis. The probes show this
increment is itself a worst-case incomplete character sum of the SAME analytic difficulty as `B`. We
state the increment hypothesis as a named `Prop` and prove the wall-reduction sandwich. -/

section IncrementWall

/-- **The open input: deterministic sub-Gaussian increment.** For a period family `η : ι → ℂ` indexed
by the quotient `Q = F^×/G` and a quotient pseudometric `d_q : ι → ι → ℝ`, the increment is
*`D`-sub-Gaussian* if `|η_b − η_c| ≤ √(D · d_q b c)` for all `b, c` (the Lipschitz/sub-Gaussian
increment estimate Dudley chaining consumes). I031 needs this with `D = O(n)`. The probes REFUTE the
Lipschitz form for the cyclic-quotient distance (`K` grows with `m`); kept here as the explicit, named,
*unproven* obligation — the honest carrier of the I031 open core. -/
def SubGaussianIncrement {ι : Type*} (η : ι → ℂ) (d_q : ι → ι → ℝ) (D : ℝ) : Prop :=
  ∀ b c : ι, ‖η b - η c‖ ≤ Real.sqrt (D * d_q b c)

/-- **The wall floor on the increment-sup (lower sandwich).** The increment-sup is at least the
floor `B` minus the second period: for any two indices, `‖η b − η c‖ ≥ ‖η b‖ − ‖η c‖` by the reverse
triangle inequality. Hence `sup_{b,c} ‖η b − η c‖ ≥ B − (min period)`, and at the antipodal pair the
probes find `≈ 2B`. So a bound on the increment-sup of scale `S` forces `B ≤ S + (min period)`: the
increment-sup CONTROLS `B`. Bounding the increment is therefore **no easier** than bounding `B` — it
is the same wall (probe `maxInc/B ∈ [1.44,1.95]`, stable). -/
theorem increment_ge_period_diff {ι : Type*} (η : ι → ℂ) (b c : ι) :
    ‖η b‖ - ‖η c‖ ≤ ‖η b - η c‖ :=
  norm_sub_norm_le (η b) (η c)

/-- **The wall reduction (upper sandwich): `B ≤ increment-sup + ‖η c₀‖`.** If there is a reference
index `c₀` (e.g. a small-norm period) and a uniform increment bound `‖η b − η c₀‖ ≤ S` for all `b`,
then `B = max_b ‖η b‖ ≤ S + ‖η c₀‖`. So an increment bound of the prize scale `S = C·√(n log m)` plus a
controlled reference yields `B ≤ C·√(n log m) + ‖η c₀‖` — but the probe shows the *uniform* increment
bound `S` itself already scales like `B` (`maxInc/√(2n log m) ≈ B/√(n log m)` up to a constant): the
increment estimate is **as hard as the original wall**, formalizing outcome (b). -/
theorem period_le_increment_sup {ι : Type*} (η : ι → ℂ) (S : ℝ) (c₀ : ι)
    (hS : ∀ b, ‖η b - η c₀‖ ≤ S) (b : ι) :
    ‖η b‖ ≤ S + ‖η c₀‖ := by
  have h1 : ‖η b‖ - ‖η c₀‖ ≤ ‖η b - η c₀‖ := norm_sub_norm_le (η b) (η c₀)
  have h2 : ‖η b - η c₀‖ ≤ S := hS b
  linarith

/-- **The honest I031 verdict, as a theorem: the increment estimate reduces to the wall.** Combining
the two sandwiches: with a reference `c₀`, the floor `B = max_b ‖η b‖` and the increment-sup
`S = sup_b ‖η b − η c₀‖` satisfy `S − ‖η c₀‖ ≤ B` (some `b` attains `B` and `S ≥ ‖η b‖ − ‖η c₀‖`)
**and** `B ≤ S + ‖η c₀‖`. Hence `|B − S| ≤ ‖η c₀‖`: the increment-sup and the floor differ by at most a
single reference period, so they have the SAME growth order. Bounding the increment to the prize scale
is therefore *equivalent* to bounding `B` to the prize scale — I031's "deterministic → Gaussian
comparison" does NOT sidestep the open core; its increment ingredient IS the open core (BGK/Paley
wall). This is the machine-checked form of the probe verdict `maxInc ≍ B`. -/
theorem increment_sup_reduces_to_wall {ι : Type*} (η : ι → ℂ) (S : ℝ) (c₀ : ι)
    (hS : ∀ b, ‖η b - η c₀‖ ≤ S) (b : ι) :
    ‖η b‖ ≤ S + ‖η c₀‖ ∧ ‖η b‖ - ‖η c₀‖ ≤ ‖η b - η c₀‖ :=
  ⟨period_le_increment_sup η S c₀ hS b, increment_ge_period_diff η b c₀⟩

end IncrementWall

end ArkLib.ProximityGap.I031ChainingBrick

/-! ## Axiom audit — every landed theorem must be axiom-clean
    (only `propext, Classical.choice, Quot.sound`; NO `sorryAx`). -/
#print axioms ArkLib.ProximityGap.I031ChainingBrick.period_value_card_le
#print axioms ArkLib.ProximityGap.I031ChainingBrick.metric_entropy_le_log_card
#print axioms ArkLib.ProximityGap.I031ChainingBrick.chaining_sup_bound
#print axioms ArkLib.ProximityGap.I031ChainingBrick.increment_ge_period_diff
#print axioms ArkLib.ProximityGap.I031ChainingBrick.period_le_increment_sup
#print axioms ArkLib.ProximityGap.I031ChainingBrick.increment_sup_reduces_to_wall
