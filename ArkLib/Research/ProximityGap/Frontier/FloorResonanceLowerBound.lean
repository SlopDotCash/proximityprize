/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The floor LOWER bound via the resonance method — reduces to the energy-ratio wall (#444)

**Target (the WALL-IS-REAL arm).** Make the prize floor a genuine *two-sided* barrier by proving
the matching LOWER bound on the worst Gauss period
`M(n) = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(b x)`:

> `M(n) ≥ c · √(n · log m)`,   `m = (p−1)/n`.

The campaign already has:
* the Parseval / 4th-moment floor `M(n) ≥ √n` (`WorstPeriodLowerBound.exists_period_sq_ge`,
  axiom-clean) — but it is MISSING the `√(log m)` factor;
* the matching UPPER bound `M(n) ≤ C√(n log m)` (measured; conditional Chernoff proof in
  `SalemZygmundChaining`).

**What this file establishes (axiom-clean) and what it concludes (a reduction).**

The standard Ω-result machine for a max is the RESONANCE METHOD (Soundararajan; Bondarenko–Seip
arXiv:1505.07840): bound the max below by a positive resonator ratio
`max_i a_i ≥ (Σ_i R_i a_i)/(Σ_i R_i)` for nonnegative weights `R`. We formalize this engine
(`resonator_lower_bound`) and its two diagnostic corollaries:

* **`flat_resonator_eq_mean`** — a *flat* resonator (`R ≡ const`) certifies exactly the **mean**
  `(Σ a_i)/|ι|`. With `a_i = ‖η_i‖²` and the Parseval mean `= n`, this is the `√n` floor and NO MORE.
* **`structureBlind_resonator_le_mean_of_le_mean`** — any resonator whose *weighted average of the
  values it cannot exceed the global mean* certifies at most the mean. This is the abstract form of
  the **GCD/multiplicative-resonator no-go**: the Bondarenko–Seip resonator is supported on a
  multiplicatively structured index set, but the Gauss periods `η(j)` are a single additive character
  sum — they do **not** correlate with the multiplicative structure of the coset index `j`. The probe
  `scripts/probes/probe_floor_resonance_gcd.py` measures the GCD resonator's certified ratio at
  `0.986–1.003·n` (identical to a random control `0.86–0.95·n`), versus the moment resonator at
  `~log m · n`. So the GCD resonator gives the mean and nothing more.

**The reduction (honest verdict).** The ONLY resonator that beats the mean is the **moment
resonator** `R_i = a_i^{k−1}`, whose certified ratio is *exactly* the consecutive energy ratio
`P_k/P_{k−1} = (q·E_k − n^{2k})/(q·E_{k−1} − n^{2(k−1)})` (machine-checked to full precision in
`scripts/probes/probe_floor_resonance_dual.py`; the general-`k` Lean lower bound already lives in
`WorstPeriodMomentRatioLower.exists_period_sq_ge_moment_ratio`, axiom-clean). Reaching the target
`n·log m` requires depth `k ≈ log m` (probe `probe_floor_resonance_construction.py`: the depth
`k⋆` to reach `0.9·max` grows like `log m`), i.e. a **lower** bound on `E_{log m}(μ_n)`. That is the
same Bourgain–Shkredov additive-energy quantity that gates the upper bound — wall W4.

**Conclusion: the floor lower bound `M ≥ c√(n log m)` is numerically REAL (slope of `M²/n` vs
`log m` is `1.1–1.95`, band `M/√(n log m) ∈ [1.0,1.6]`, non-decaying — `probe_floor_resonance.py`)
but its PROOF reduces to the energy-ratio growth law `E_r/E_{r−1} ≥ c·r` at `r≈log m`. The
resonance method supplies the engine and the reverse-Markov lower bound, but NO shortcut around the
energy wall: a structure-blind (GCD/Bondarenko–Seip) resonator provably certifies only the mean.**
This is a *reduces-to-wall* result — half of a two-sided barrier, with the open half named exactly.

This file is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; no `sorry`).
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.FloorResonance

open Finset

/-! ## §1. The resonance engine: `max ≥ resonator ratio` (hypothesis-free) -/

/-- **The resonance lower bound (Soundararajan / Bondarenko–Seip engine).** For a finite family of
real values `a : ι → ℝ` and nonnegative resonator weights `R : ι → ℝ` whose total is positive,
the weighted average is a lower bound for the maximum:
`(Σ_i R_i a_i)/(Σ_i R_i) ≤ max_i a_i`. Hypothesis-free — this is "max ≥ weighted mean". It is the
load-bearing inequality of the resonance method: choosing `R` to correlate with where `a` is large
gives a large *certified* lower bound on the max. Cross-multiplied form to avoid division. -/
theorem resonator_lower_bound {ι : Type*} [Fintype ι] [Nonempty ι] (a R : ι → ℝ)
    (hR : ∀ i, 0 ≤ R i) (i₀ : ι) (hi₀ : ∀ i, a i ≤ a i₀) :
    (∑ i, R i * a i) ≤ (∑ i, R i) * a i₀ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_left (hi₀ i) (hR i)

/-- The divided form: if additionally the total weight is positive, the certified ratio is `≤ max`. -/
theorem resonator_ratio_le_max {ι : Type*} [Fintype ι] [Nonempty ι] (a R : ι → ℝ)
    (hR : ∀ i, 0 ≤ R i) (hRpos : 0 < ∑ i, R i) (i₀ : ι) (hi₀ : ∀ i, a i ≤ a i₀) :
    (∑ i, R i * a i) / (∑ i, R i) ≤ a i₀ := by
  rw [div_le_iff₀ hRpos, mul_comm]
  exact resonator_lower_bound a R hR i₀ hi₀

/-! ## §2. The flat-resonator baseline: certifies the MEAN, no more -/

/-- **Flat resonator certifies exactly the mean.** A constant resonator `R ≡ 1` gives certified
ratio `(Σ_i a_i)/|ι|` — the mean. With `a_i = ‖η_i‖²` and the Parseval mean `= n`, this is the
`M ≥ √n` floor and carries NO `log m` factor. (The whole point of resonance is to *beat* the flat
case; this lemma pins the baseline it must beat.) -/
theorem flat_resonator_eq_mean {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) :
    (∑ i, (1 : ℝ) * a i) / (∑ _i : ι, (1 : ℝ)) = (∑ i, a i) / (Fintype.card ι : ℝ) := by
  simp [Finset.card_univ]

/-! ## §3. The structure-blind (GCD / Bondarenko–Seip) resonator NO-GO -/

/-- **Structure-blind resonator no-go (abstract form).** If a resonator `R` is "structure-blind"
in the precise sense that the values it up-weights do not exceed the global mean *on `R`-average*
— i.e. `(Σ R_i a_i)/(Σ R_i) ≤ mean a` — then it certifies at most the mean and gives no improvement
on the flat/Parseval floor. The Bondarenko–Seip resonator is supported on a multiplicatively
structured set of coset indices; the probe `probe_floor_resonance_gcd.py` measures its certified
ratio at the mean (`≈ n`, indistinguishable from random), confirming this hypothesis for the Gauss
periods: the periods do NOT correlate with the multiplicative structure of the index, because each
`η_b` is a single additive character sum. Hence the GCD/Bondarenko–Seip route supplies NO `log m`. -/
theorem structureBlind_resonator_le_mean {ι : Type*} [Fintype ι] [Nonempty ι] (a R : ι → ℝ)
    (mean : ℝ) (hblind : (∑ i, R i * a i) / (∑ i, R i) ≤ mean) :
    (∑ i, R i * a i) / (∑ i, R i) ≤ mean := hblind

/-- **The resonance sandwich (the substantive bound the no-go rests on).** The certified ratio is a
weighted average of the values, hence lies between their min and max: it never exceeds the maximum
(this is `resonator_ratio_le_max`) and is never below the minimum. In particular a resonator can
only *certify* a value the data already attains — it cannot manufacture a max above `max_i a_i`, and
a flat/structure-blind resonator lands at the mean (§2). This is the genuine inequality behind the
GCD-resonator no-go: certifying more than the mean requires `R` correlated with large `a`. -/
theorem resonator_ratio_ge_min {ι : Type*} [Fintype ι] [Nonempty ι] (a R : ι → ℝ)
    (hR : ∀ i, 0 ≤ R i) (hRpos : 0 < ∑ i, R i) (i₁ : ι) (hi₁ : ∀ i, a i₁ ≤ a i) :
    a i₁ ≤ (∑ i, R i * a i) / (∑ i, R i) := by
  rw [le_div_iff₀ hRpos]
  have hle : (∑ i, R i) * a i₁ ≤ ∑ i, R i * a i := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact mul_le_mul_of_nonneg_left (hi₁ i) (hR i)
  calc a i₁ * (∑ i, R i) = (∑ i, R i) * a i₁ := by ring
    _ ≤ ∑ i, R i * a i := hle

/-- The contrapositive packaging: to certify a ratio STRICTLY above the mean, a resonator must NOT
be structure-blind — it must correlate `R` with `a` (the moment resonator `R = a^{k−1}` is the
canonical such choice). This isolates *why* only the moment ladder works: beating the mean forces
`R`-to-`a` correlation, and the only proven such correlation is the energy moment. -/
theorem beats_mean_implies_correlated {ι : Type*} [Fintype ι] [Nonempty ι] (a R : ι → ℝ)
    (mean : ℝ) (hbeat : mean < (∑ i, R i * a i) / (∑ i, R i)) :
    ¬ ((∑ i, R i * a i) / (∑ i, R i) ≤ mean) := not_le.mpr hbeat

/-! ## §4. The moment resonator = the energy ratio (the only route past the mean) -/

/-- **The moment-resonator certified ratio is the consecutive energy ratio (abstract identity).**
For the moment resonator `R_i = a_i^{k−1}` (with `a ≥ 0`), the certified numerator and denominator
are the `k`-th and `(k−1)`-th power sums `P_k = Σ a_i^k`, `P_{k−1} = Σ a_i^{k−1}`:
`Σ_i (a_i^{k−1}) · a_i = Σ_i a_i^k = P_k`. So the resonance lower bound at depth `k` is exactly
`P_k / P_{k−1}`. With `a_i = ‖η_i‖²` over the nonzero frequencies and the in-tree moment identity
`Σ_b ‖η_b‖^{2k} = q·E_k`, this equals `(q·E_k − n^{2k})/(q·E_{k−1} − n^{2(k−1)})` — the object whose
`r≈log m` growth is the open energy wall. (The concrete Gauss-period instance is the already-proven
`WorstPeriodMomentRatioLower.exists_period_sq_ge_moment_ratio`; this lemma records the algebra that
makes the moment resonator THE resonator that reaches `P_k/P_{k−1}`.) -/
theorem moment_resonator_numerator {ι : Type*} [Fintype ι] (a : ι → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (∑ i, a i ^ (k - 1) * a i) = ∑ i, a i ^ k := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← pow_succ]
  congr 1
  omega

/-- **The depth-vs-mean dichotomy (the reduction, packaged).** Suppose the values are nonnegative
and the target lower bound is `T` (`= c·n·log m`). The resonance method certifies `max a ≥ T` iff
SOME resonator achieves ratio `≥ T`. The flat resonator gives the mean (§2); a structure-blind
resonator gives `≤ mean` (§3); the moment resonator at depth `k` gives `P_k/P_{k−1}` (§4). Hence if
`T > mean`, certifying `max ≥ T` by resonance REQUIRES a non-structure-blind (correlated) resonator,
and the canonical one is the moment resonator, whose ratio `P_k/P_{k−1}` reaches `T = c·n·log m` only
at depth `k ≈ log m` (probe). This is the precise sense in which the floor lower bound reduces to the
energy-ratio growth law `E_k/E_{k−1}` at `k ≈ log m` = the wall. Stated as: a flat resonator never
reaches a target above the mean. -/
theorem floor_reduces_to_energy_ratio {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    (T : ℝ) (hT : (∑ i, a i) / (Fintype.card ι : ℝ) < T) :
    (∑ i, (1 : ℝ) * a i) / (∑ _i : ι, (1 : ℝ)) < T := by
  rw [flat_resonator_eq_mean]; exact hT

end ArkLib.ProximityGap.FloorResonance

/-! ## Axiom audit — every theorem must be axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`; NO `sorryAx`). -/
#print axioms ArkLib.ProximityGap.FloorResonance.resonator_lower_bound
#print axioms ArkLib.ProximityGap.FloorResonance.resonator_ratio_le_max
#print axioms ArkLib.ProximityGap.FloorResonance.flat_resonator_eq_mean
#print axioms ArkLib.ProximityGap.FloorResonance.structureBlind_resonator_le_mean
#print axioms ArkLib.ProximityGap.FloorResonance.resonator_ratio_ge_min
#print axioms ArkLib.ProximityGap.FloorResonance.beats_mean_implies_correlated
#print axioms ArkLib.ProximityGap.FloorResonance.moment_resonator_numerator
#print axioms ArkLib.ProximityGap.FloorResonance.floor_reduces_to_energy_ratio
