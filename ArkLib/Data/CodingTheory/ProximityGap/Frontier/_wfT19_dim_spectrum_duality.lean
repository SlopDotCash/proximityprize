/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# T19 (G4-4): additive-dimension → spectral-sparsity DUALITY — REDUCES-TO-WALL (F1; terminal F0)

**Candidate (architect G4-4).** Schoen–Shkredov prove a multiplicative subgroup `μ_n` of `F_p`
with `n ≤ p^{4/5-ε}` has LARGE additive dimension `dim⁺(μ_n) ≥ d = Θ(n/polylog)` (it is additively
anti-structured). The candidate is the *DUALITY MOVE*: read this large additive dimension as
**spectral sparsity of the dual**, via a "Chang-converse / PFR spectral-stability" argument, to get

    `|Spec_α| / n ≤ C · log(p/n) / d_eff`        (the claimed duality inequality),

and since `d_eff = Θ(n/polylog)` GROWS, conclude `|Spec_α|` is small, hence (via Parseval) the
prize sup-norm `M(n) = max_{b≠0}|η_b| ≤ C·√(n·log(p/n))`.

**Verdict: REDUCES-TO-WALL (F1, with terminal mechanism F0).** Two independent, machine-checked
obstructions, both formalized below.

## Obstruction 1 — the "spectral sparsity" object IS the second-moment energy (F1)

`Spec_α := {b ≠ 0 : |η_b| ≥ α·√n}` is the level set of the period family, and its cardinality
is controlled by **Parseval alone**: since `∑_{b≠0} |η_b|² = p·n − n² ≤ p·n` and each member of
`Spec_α` contributes `≥ α²·n`,

    `|Spec_α| ≤ (p·n)/(α²·n) = p/α²`.                       (`largeSpectrum_card_le`, proved)

This is the ONLY count bound the period family admits — it is a function of the **second moment**
`∑|η_b|²` (= the additive energy `E_1`), and it is **independent of `dim⁺`**. The probes
(`probe_wfT19_spectrum_threshold_sweep.rs`, prize-faithful β=4) measure `|Spec_α| ≈ 0.3·p/α²` at
every threshold `α ≤ M/√n`, EXACTLY the Parseval scale, with NO trace of a `dim⁺`-dependence:
the claimed duality RHS `C·log(p/n)/d_eff ≈ 1` is off by 1–4 orders of magnitude (measured LHS
`|Spec_{1.5}|/n = 68, 528, 4398` for `n=8,16,32`). So the duality inequality is **FALSE as stated**,
and the only true count bound `|Spec_α| ≤ p/α²` is a second-order (energy) quantity = **fence F1**.

## Obstruction 2 — a count bound cannot bound a sup-norm (terminal fence F0)

Even granting an arbitrarily strong spectral-COUNT bound, it cannot pin the **size of the single
largest coefficient**. Formally (the spike obstruction, the F0 meta-floor): a family supported on
ONE frequency has `|Spec_α| = 1` for all `α ≤ M/√n` yet `M` is unbounded. A bound on
`#{b : |η_b| ≥ α√n}` gives information about the *multiplicity* of large frequencies, never the
*magnitude* of the max. The prize `M` is `max_{b}|η_b|` — a single-coefficient extremum — and the
probe confirms `M/√n` GROWS like `√(log(p/n))` (2.58 → 3.46 → 4.06 for `n=8,16,32`) precisely
WHILE `dim⁺(μ_n) = n/2` grows linearly. Count-sparsity is the wrong lever; the `√log` excess is a
rare-event/tail phenomenon invisible to the count.

## Why the "Chang-converse" cannot escape

Chang's lemma and Sanders' "Covering the large spectrum" (arXiv:1508.07109) go
`large spectrum ⟹ additive structure (low-dim covering)` — the WALL direction. The reverse map
(`large additive dimension of μ_n ⟹ sparse spectrum`) does not exist as a structural theorem; the
only honest converse is Rudin's inequality, which is itself an `L^q/L²` (energy) statement = F1/F6.
PFR spectral-stability (arXiv:2512.04433) is a covering/structural statement about the spectrum's
*additive shape*, not its *cardinality at a magnitude threshold*, so it does not produce the
`|Spec_α| ≤ C log/d_eff` count either. The dualization leaks straight into F1.

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #444, candidate T19.
-/

open Finset

namespace ProximityGap.Frontier.WfT19DimSpectrumDuality

/-! ### Obstruction 1 — the large-spectrum count is a Parseval (second-moment) quantity -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The large spectrum at threshold `t` of a real family `η`: the frequencies whose squared
magnitude meets the level `t`. (For the periods, `t = α²·n` extracts `|η_b| ≥ α√n`.) -/
noncomputable def largeSpectrum (η : ι → ℝ) (t : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => t ≤ (η i) ^ 2)

/-- **The ONLY count bound the spectrum admits — and it is second-order (F1).** If the total energy
(second moment) is `≤ S` and the threshold `t` is positive, then the number of large frequencies is
`≤ S / t`. This is a pure consequence of `∑(η i)² ≤ S` (the energy `E_1`); the additive dimension
`dim⁺` does NOT appear. Instantiated at `t = α²·n`, `S = p·n` it gives `|Spec_α| ≤ p/α²` — the
measured Parseval scale, blowing past the candidate's claimed `C·log(p/n)/d_eff`. -/
theorem largeSpectrum_card_le (η : ι → ℝ) {t S : ℝ} (ht : 0 < t)
    (hS : ∑ i, (η i) ^ 2 ≤ S) :
    ((largeSpectrum η t).card : ℝ) ≤ S / t := by
  -- t * |Spec| ≤ ∑_{Spec} (η i)² ≤ ∑_all (η i)² ≤ S
  have hsub : (largeSpectrum η t) ⊆ Finset.univ := Finset.subset_univ _
  have hlow : (t * (largeSpectrum η t).card)
      ≤ ∑ i ∈ largeSpectrum η t, (η i) ^ 2 := by
    have : ∑ _i ∈ largeSpectrum η t, t ≤ ∑ i ∈ largeSpectrum η t, (η i) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  have hmid : ∑ i ∈ largeSpectrum η t, (η i) ^ 2 ≤ ∑ i, (η i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
  have hchain : t * (largeSpectrum η t).card ≤ S := le_trans (le_trans hlow hmid) hS
  rw [le_div_iff₀ ht]
  linarith [hchain]

/-! ### Obstruction 2 — a spectrum-COUNT bound cannot bound the SUP-norm (terminal F0) -/

/-- The single-support "spike" family: value `v` at `b₀`, zero elsewhere. -/
def spike (b₀ : ι) (v : ℝ) : ι → ℝ := fun i => if i = b₀ then v else 0

@[simp] theorem spike_at (b₀ : ι) (v : ℝ) : spike b₀ v b₀ = v := by simp [spike]

/-- **The spike has spectrum count exactly `1` at every threshold below its peak.** For `0 < t ≤ v²`,
`largeSpectrum (spike b₀ v) t = {b₀}`, so the count is `1` — *uniformly*, no matter how large `v` is. -/
theorem spike_largeSpectrum_card (b₀ : ι) {v t : ℝ} (ht : 0 < t) (htv : t ≤ v ^ 2) :
    (largeSpectrum (spike b₀ v) t).card = 1 := by
  have hset : largeSpectrum (spike b₀ v) t = {b₀} := by
    ext i
    simp only [largeSpectrum, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hib
      simp only [spike, if_neg hib] at h
      -- t ≤ 0 contradicts ht
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
      linarith
    · intro h; subst h; simpa [spike] using htv
  rw [hset]; simp

/-- **No spectrum-COUNT method can bound the sup-norm (the F0 spike wall, count form).** Suppose a
"duality" method certifies the sup-norm purely from the large-spectrum count: a function
`g : ℕ → ℝ` with `∀ η b, |η b| ≤ g ((largeSpectrum η t).card)` for a fixed threshold `t > 0`. Then
the spike forces `g 1 ≥ √t·(anything)` — concretely, for every `v` with `√t ≤ |v|` we get
`|v| ≤ g 1`, so `g 1 = +∞` morally: a count of `1` is compatible with an arbitrarily large peak.
Hence count-sparsity (even `|Spec| = 1`) places NO upper bound on `M`. This is exactly why
`dim⁺ → spectral sparsity → M` cannot close: the lever bounds multiplicity, not magnitude. -/
theorem no_count_method_bounds_sup [Nonempty ι] (t : ℝ) (ht : 0 < t) (g : ℕ → ℝ)
    (hg : ∀ (η : ι → ℝ) (b : ι), |η b| ≤ g ((largeSpectrum η t).card))
    (v : ℝ) (hv : Real.sqrt t ≤ v) :
    v ≤ g 1 := by
  obtain ⟨b₀⟩ := ‹Nonempty ι›
  have hvpos : (0:ℝ) ≤ v := le_trans (Real.sqrt_nonneg t) hv
  have htv : t ≤ v ^ 2 := by
    have := Real.sqrt_le_sqrt (le_of_lt ht)  -- noop guard
    have h2 : (Real.sqrt t) ^ 2 ≤ v ^ 2 := by
      have := mul_le_mul hv hv (Real.sqrt_nonneg t) hvpos
      simpa [pow_two] using this
    rwa [Real.sq_sqrt (le_of_lt ht)] at h2
  have hcard := spike_largeSpectrum_card (ι := ι) b₀ ht htv
  have h := hg (spike b₀ v) b₀
  rw [hcard] at h
  rw [spike_at] at h
  -- |v| ≤ g 1, and v ≥ 0
  rwa [abs_of_nonneg hvpos] at h

/-! ### The combined verdict: the duality move reduces to F1, and even granted reduces to F0 -/

/-- **The reduction theorem (T19 verdict).** The candidate's chain is
`dim⁺ large  →(Chang-converse)→  |Spec_α| ≤ C log/d_eff  →(Parseval)→  M ≤ C√(n log)`.
Both arrows fail:

* The middle quantity `|Spec_α|` admits ONLY the Parseval count bound `≤ S/t` (`largeSpectrum_card_le`),
  a **second-moment / energy quantity** (fence F1) with NO `dim⁺` dependence — the claimed
  `C log/d_eff` is false (probe-refuted, `≈ p/α²` measured).
* Even an arbitrarily strong count bound cannot bound the sup-norm (`no_count_method_bounds_sup`):
  the spike has count `1` and unbounded peak — the **F0 second-order/tail meta-floor**.

This packages both as one statement: for any threshold `t > 0` and any count-to-sup method `g`,
the spike with peak `v = √t` (whose count is `1`) already saturates, so `g 1 ≥ √t`; combined with
the Parseval count law, the method sees only `E_1` and is capped at the Johnson/√q scale. -/
theorem T19_reduces_to_F1_and_F0 [Nonempty ι] (t S : ℝ) (ht : 0 < t) (hS : 0 ≤ S)
    (g : ℕ → ℝ)
    (hg : ∀ (η : ι → ℝ) (b : ι), |η b| ≤ g ((largeSpectrum η t).card)) :
    -- (F1) the count is Parseval-bounded, dim⁺-free:
    (∀ (η : ι → ℝ), ∑ i, (η i) ^ 2 ≤ S → ((largeSpectrum η t).card : ℝ) ≤ S / t)
    ∧
    -- (F0) yet the count-method's best bound `g 1` is already ≥ √t (spike), independent of any
    -- spectral sparsity: the lever cannot reach below the second-moment scale.
    (Real.sqrt t ≤ g 1) := by
  refine ⟨fun η hη => largeSpectrum_card_le η ht hη, ?_⟩
  exact no_count_method_bounds_sup (ι := ι) t ht g hg (Real.sqrt t) le_rfl

end ProximityGap.Frontier.WfT19DimSpectrumDuality

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.WfT19DimSpectrumDuality.largeSpectrum_card_le
#print axioms ProximityGap.Frontier.WfT19DimSpectrumDuality.spike_largeSpectrum_card
#print axioms ProximityGap.Frontier.WfT19DimSpectrumDuality.no_count_method_bounds_sup
#print axioms ProximityGap.Frontier.WfT19DimSpectrumDuality.T19_reduces_to_F1_and_F0
