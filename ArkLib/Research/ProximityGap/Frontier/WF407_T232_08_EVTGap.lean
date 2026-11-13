/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# WF407_T232_08_EVTGap — the EVT route to the δ* floor is WALLED at the bulk-vs-tail gap

**Thread 232-T08 / 407-T17.** The Gauss-period floor is
`B(μ_n) = max_{c} ‖η_c‖`, the max over the `m = (p−1)/n` distinct periods. The proposed EVT
route (Salem–Zygmund / sub-Gaussian maximal inequality, in-tree
`Frontier/SalemZygmundChaining.lean`) would give `B ≤ √(2 σ² log m)` with `σ² = O(n)`, i.e. the
prize floor `B ≲ √(n log m)`. The route's PROVEN structural inputs (407-T17,
`WorstPeriodLowerBound.lean`) are exactly that the period family is **exchangeable white-noise**:

  * one linear constraint    `Σ_c η_c = −1`         (mean `μ = −1/m`),
  * the second-moment law    `Σ_c ‖η_c‖² = p − n`   (per-coordinate variance `v ≈ n/2`),
  * the exchangeable covariance fingerprint `Cov(η_c, η_{c'}) = −Var/(m−1)` for `c ≠ c'`.

**The question this file settles (DEFINITIVELY): are those three facts SUFFICIENT to prove the EVT
floor `max ≤ √(2 v log m)`?**  Answer: **NO.** The route is *walled* exactly at the gap between
bulk Gaussianity (the two moments + covariance, all proven) and tail control (the sub-Gaussian
MGF, which is the *unproven* Gauss-sum joint-equidistribution input).

## The two algebraic facts that wall the route (both proven below, axiom-clean)

For a real sample `Y : Fin m → ℝ` (`m ≥ 2`) write `μ = (1/m) Σ Y`, `v = (1/m) Σ (Y−μ)²`
(empirical mean and variance). The empirical off-diagonal sum of centered products is
`Σ_{i,j} (Yᵢ−μ)(Yⱼ−μ) − Σ_i (Yᵢ−μ)²`.

1. **`emp_offdiag_sum` — the covariance fingerprint is VACUOUS.** For *every* sample,
   that off-diagonal sum equals `−Σ(Yᵢ−μ)²` identically (forced by `Σ(Yᵢ−μ) = 0`), i.e. the
   empirical off-diagonal covariance is `−v/(m−1)`. So the "exchangeable white-noise covariance"
   that 407-T17 measured is an *automatic algebraic identity*, carrying **zero** information beyond
   the variance. (The sharp form of "bulk Gaussianity ≠ tail".)

2. **`evt_route_walled` — a spike sample matches every proven moment yet has a huge max.** The
   two-value "spike" sample (one coordinate `= a`, the rest `= b`) with
   `a = μ − √(v(m−1))`, `b = μ + √(v/(m−1))` has empirical mean exactly `μ` and variance exactly
   `v`, hence (by fact 1) the exchangeable covariance `−v/(m−1)` too — it matches ALL three proven
   inputs — yet `|a − μ| = √(v(m−1))`. As `m → ∞` (fixed `v`) this is `Θ(√(v·m))`, exceeding the
   EVT scale `√(2 v log m)` by the unbounded factor `√((m−1)/(2 log m)) → ∞`.

**Conclusion (the verdict).** No theorem whose hypotheses are only (mean, variance, exchangeable
covariance) can bound `max` by `√(2 v log m)`: the spike countermodel satisfies the hypotheses and
violates the conclusion by an arbitrarily large factor. The EVT floor therefore *requires* the
sub-Gaussian MGF (all higher moments = Gauss-sum joint equidistribution, Rojas–León 2207.12439 /
the BGK/Paley wall), the project's standing open core. The route is **walled at the bulk-vs-tail
gap**, precisely as 407-T17 anticipated, and now machine-checked.

Numerical companions (exact, real Gauss periods): `scripts/probes/wf407_T232-08-evt_periods.py`
(cov-ratio `= 1.0000` exactly, the fingerprint), `..._mgf_tail.py` (the real periods ARE
sub-Gaussian: `k(t) ≥ 1`, `σ²/n` bounded in `m`), `..._definetti_gap.py` (the spike countermodel,
`max/√(2v log m) → ∞`).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`.
-/

namespace ArkLib.ProximityGap.WF407_T232_08_EVTGap

open Finset

/-- Empirical mean of a real sample `Y : Fin m → ℝ`. -/
noncomputable def emean {m : ℕ} (Y : Fin m → ℝ) : ℝ := (∑ i, Y i) / m

/-- Empirical (population) variance of a real sample. -/
noncomputable def evar {m : ℕ} (Y : Fin m → ℝ) : ℝ :=
  (∑ i, (Y i - emean Y) ^ 2) / m

/-- The centered coordinates sum to zero — the single algebraic fact behind everything. -/
theorem sum_centered_eq_zero {m : ℕ} (hm : 0 < m) (Y : Fin m → ℝ) :
    ∑ i, (Y i - emean Y) = 0 := by
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [emean, mul_div_assoc']
  rw [mul_comm, mul_div_assoc, div_self hmne, mul_one, sub_self]

/-- **Fact 1 — the exchangeable-covariance fingerprint is an automatic identity.**

The total off-diagonal sum of centered products is `−Σ(Yᵢ−μ)²`, because `(Σ(Yᵢ−μ))² = 0` splits
into the diagonal `Σ(Yᵢ−μ)²` plus the off-diagonal. Hence the empirical off-diagonal covariance
equals `−v/(m−1)` for *every* sample — it is NOT an independent structural property of the Gauss
periods, only a restatement of the variance. (`Σ_{i≠j} cᵢcⱼ = −Σ cᵢ²` when `Σcᵢ = 0`.) -/
theorem emp_offdiag_sum {m : ℕ} (hm : 0 < m) (Y : Fin m → ℝ) :
    (∑ i, ∑ j, (Y i - emean Y) * (Y j - emean Y)) - (∑ i, (Y i - emean Y) ^ 2) =
      - (∑ i, (Y i - emean Y) ^ 2) := by
  set c : Fin m → ℝ := fun i => Y i - emean Y with hc
  have hsum0 : ∑ i, c i = 0 := sum_centered_eq_zero hm Y
  have hfull : (∑ i, ∑ j, c i * c j) = (∑ i, c i) * (∑ j, c j) := by
    rw [Finset.sum_mul_sum]
  rw [hfull, hsum0]
  ring

/-- The distinguished spike index `0 ∈ Fin m` (needs `m ≥ 1`). -/
def i0 {m : ℕ} (hm : 0 < m) : Fin m := ⟨0, hm⟩

/-- The two-value "spike" sample on `Fin m` (`m ≥ 1`): index `i0` carries `spikeVal`, every other
index carries `baseVal`. -/
def spike {m : ℕ} (hm : 0 < m) (spikeVal baseVal : ℝ) : Fin m → ℝ :=
  fun i => if i = i0 hm then spikeVal else baseVal

/-- The chosen spike parameters realizing prescribed mean `μ` and variance `v ≥ 0` on `Fin m`,
`m ≥ 2`: `spikeVal = μ − √(v(m−1))`, `baseVal = μ + √(v/(m−1))`. -/
noncomputable def spikeVal (m : ℕ) (μ v : ℝ) : ℝ := μ - Real.sqrt (v * (m - 1))
noncomputable def baseVal (m : ℕ) (μ v : ℝ) : ℝ := μ + Real.sqrt (v / (m - 1))

private lemma sum_spike {m : ℕ} (hm : 0 < m) (s b : ℝ) :
    ∑ i, spike (m := m) hm s b i = s + (m - 1) * b := by
  classical
  have hmem : (i0 hm) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ hmem]
  have h0 : spike (m := m) hm s b (i0 hm) = s := by simp [spike]
  have hrest : ∀ i ∈ (Finset.univ : Finset (Fin m)).erase (i0 hm),
      spike (m := m) hm s b i = b := by
    intro i hi
    have : i ≠ i0 hm := (Finset.mem_erase.mp hi).1
    simp [spike, this]
  rw [Finset.sum_congr rfl hrest, h0]
  have hcard : ((Finset.univ : Finset (Fin m)).erase (i0 hm)).card = m - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
  ring

/-- The spike sample with parameters `spikeVal, baseVal` has empirical mean exactly `μ`. -/
theorem spike_emean {m : ℕ} (hm : 2 ≤ m) (μ v : ℝ) (hv : 0 ≤ v) :
    emean (spike (m := m) (by omega) (spikeVal m μ v) (baseVal m μ v)) = μ := by
  have hm0 : 0 < m := by omega
  have hm1pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hmne : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by linarith
    exact this.ne'
  rw [emean, sum_spike hm0]
  have hsqrt : (m - 1 : ℝ) * Real.sqrt (v / (m - 1)) = Real.sqrt (v * (m - 1)) := by
    rw [show ((m : ℝ) - 1) * Real.sqrt (v / (m - 1))
          = Real.sqrt (((m : ℝ) - 1) ^ 2) * Real.sqrt (v / (m - 1)) by
        rw [Real.sqrt_sq hm1pos.le]]
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [spikeVal, baseVal]
  rw [show (μ - Real.sqrt (v * (↑m - 1)) + (↑m - 1) * (μ + Real.sqrt (v / (↑m - 1))))
        = (↑m) * μ - Real.sqrt (v * (↑m - 1)) + (↑m - 1) * Real.sqrt (v / (↑m - 1)) by ring]
  rw [hsqrt]
  field_simp
  ring

/-- The spike sample has empirical variance exactly `v` (for `v ≥ 0`, `m ≥ 2`). -/
theorem spike_evar {m : ℕ} (hm : 2 ≤ m) (μ v : ℝ) (hv : 0 ≤ v) :
    evar (spike (m := m) (by omega) (spikeVal m μ v) (baseVal m μ v)) = v := by
  classical
  have hm0 : 0 < m := by omega
  have hm1pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hmne : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by linarith
    exact this.ne'
  have hm1ne : ((m : ℝ) - 1) ≠ 0 := hm1pos.ne'
  set s := spikeVal m μ v with hsdef
  set b := baseVal m μ v with hbdef
  have hmean : emean (spike (m := m) hm0 s b) = μ := spike_emean hm μ v hv
  have hsum : ∑ i, (spike (m := m) hm0 s b i - μ) ^ 2 = (s - μ) ^ 2 + (m - 1) * (b - μ) ^ 2 := by
    have hmem : (i0 hm0) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
    rw [← Finset.sum_erase_add _ _ hmem]
    have h0 : (spike (m := m) hm0 s b (i0 hm0) - μ) ^ 2 = (s - μ) ^ 2 := by simp [spike]
    have hrest : ∀ i ∈ (Finset.univ : Finset (Fin m)).erase (i0 hm0),
        (spike (m := m) hm0 s b i - μ) ^ 2 = (b - μ) ^ 2 := by
      intro i hi
      have : i ≠ i0 hm0 := (Finset.mem_erase.mp hi).1
      simp [spike, this]
    rw [Finset.sum_congr rfl hrest, h0]
    have hcard : ((Finset.univ : Finset (Fin m)).erase (i0 hm0)).card = m - 1 := by
      rw [Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  have hsμ : (s - μ) ^ 2 = v * (m - 1) := by
    rw [hsdef, spikeVal]
    rw [show (μ - Real.sqrt (v * (↑m - 1)) - μ) = -Real.sqrt (v * (↑m - 1)) by ring]
    rw [neg_pow, Real.sq_sqrt (by positivity)]
    ring
  have hbμ : (b - μ) ^ 2 = v / (m - 1) := by
    rw [hbdef, baseVal]
    rw [show (μ + Real.sqrt (v / (↑m - 1)) - μ) = Real.sqrt (v / (↑m - 1)) by ring]
    rw [Real.sq_sqrt (by positivity)]
  rw [evar, hmean, hsum, hsμ, hbμ]
  rw [show (m - 1 : ℝ) * (v / (m - 1)) = v by field_simp]
  field_simp
  ring

/-- The spike's centered deviation at `i0` equals `√(v(m−1))`. -/
theorem evt_gap_centered_dev {m : ℕ} (hm : 2 ≤ m) (μ v : ℝ) (hv : 0 ≤ v) :
    |spikeVal m μ v - μ| = Real.sqrt (v * (m - 1)) := by
  rw [spikeVal]
  rw [show (μ - Real.sqrt (v * (↑m - 1)) - μ) = -Real.sqrt (v * (↑m - 1)) by ring]
  rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- **The gap dominates the EVT scale.** The spike's centered deviation `√(v(m−1))` is
`≥ √(2 v log m)` whenever `2 log m ≤ m − 1` (true for all `m ≥ 7`, e.g. always in the prize regime
`m = 2^128`). So the gap is unbounded: ratio `√((m−1)/(2 log m)) → ∞`. -/
theorem evt_gap_exceeds_scale {m : ℕ} (hm : 2 ≤ m) (μ v : ℝ) (hv : 0 ≤ v)
    (hgap : 2 * Real.log m ≤ (m : ℝ) - 1) :
    Real.sqrt (2 * v * Real.log m) ≤ |spikeVal m μ v - μ| := by
  rw [evt_gap_centered_dev hm μ v hv]
  apply Real.sqrt_le_sqrt
  nlinarith [hgap, hv]

/-- **MAIN — the EVT route is WALLED at the bulk-vs-tail gap (assembled countermodel).**

For every `m ≥ 2`, `v > 0`, `μ ∈ ℝ` with the (always-true for `m ≥ 7`) spread hypothesis
`2 log m ≤ m − 1`, the spike sample `Y = spike (spikeVal) (baseVal)` simultaneously:
  * has empirical mean `= μ`              (`spike_emean`),
  * has empirical variance `= v`          (`spike_evar`),
  * has off-diagonal centered-product sum `= −Σ(Yᵢ−μ)²`, i.e. exchangeable covariance `−v/(m−1)`
    (`emp_offdiag_sum`, an automatic identity), and yet
  * has centered max deviation `|Y(i0) − μ| = √(v(m−1)) ≥ √(2 v log m)`,
the EVT/Salem–Zygmund scale.

Therefore the three PROVEN structural inputs (exchangeability + the two moments) do NOT imply the
EVT floor `max ≤ √(2 v log m)`; the implication fails by the factor `√((m−1)/(2 log m))`. The floor
needs strictly more — the sub-Gaussian MGF / Gauss-sum equidistribution (the open core). -/
theorem evt_route_walled {m : ℕ} (hm : 2 ≤ m) (μ v : ℝ) (hvpos : 0 < v)
    (hgap : 2 * Real.log m ≤ (m : ℝ) - 1) :
    let Y := spike (m := m) (by omega) (spikeVal m μ v) (baseVal m μ v)
    emean Y = μ ∧ evar Y = v ∧
    ((∑ i, ∑ j, (Y i - emean Y) * (Y j - emean Y)) - (∑ i, (Y i - emean Y) ^ 2)
        = - (∑ i, (Y i - emean Y) ^ 2)) ∧
    Real.sqrt (2 * v * Real.log m) ≤ |Y (i0 (by omega)) - emean Y| := by
  have hm0 : 0 < m := by omega
  refine ⟨spike_emean hm μ v hvpos.le, spike_evar hm μ v hvpos.le,
          emp_offdiag_sum hm0 _, ?_⟩
  rw [spike_emean hm μ v hvpos.le]
  have h0 : spike (m := m) hm0 (spikeVal m μ v) (baseVal m μ v) (i0 hm0) = spikeVal m μ v := by
    simp [spike]
  rw [h0]
  exact evt_gap_exceeds_scale hm μ v hvpos.le hgap

end ArkLib.ProximityGap.WF407_T232_08_EVTGap

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WF407_T232_08_EVTGap.emp_offdiag_sum
#print axioms ArkLib.ProximityGap.WF407_T232_08_EVTGap.spike_emean
#print axioms ArkLib.ProximityGap.WF407_T232_08_EVTGap.spike_evar
#print axioms ArkLib.ProximityGap.WF407_T232_08_EVTGap.evt_gap_exceeds_scale
#print axioms ArkLib.ProximityGap.WF407_T232_08_EVTGap.evt_route_walled
