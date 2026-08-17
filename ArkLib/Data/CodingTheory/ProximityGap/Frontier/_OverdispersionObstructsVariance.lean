/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
# Over-dispersion obstructs the family-variance route (#444)

This brick records, axiom-clean, a genuinely-new *negative* result discovered by continuing the
attack past the PhD thesis's first draft.

The thesis capstone `_ThesisCapstone.subPoisson_variance_implies_prizeFloor` reduces the prize to one
hypothesis: the wraparound `W_r` is **sub-Poisson** over the prime family, `Var_P(W_r) ≤ mean_P(W_r)`,
so that Chebyshev selects a good prime.  Direct computation
(`scripts/probes/probe_wraparound_overdispersion.py`) **refutes** this hypothesis everywhere in the
computable range: the variance-to-mean ratio is `14 … 407555`, not `≤ 1`.  The wraparound is heavily
**over-dispersed** — a sparse set of *structured* primes (Fermat-like, high `v₂(p-1)`) carries almost
all of the second-moment mass, and the typical prime contributes little.

The theorem below explains *why* this is fatal to the variance route as stated, and it is a clean
inequality (no number theory): **if even a single prime carries wraparound mass exceeding `√(total)`
above the mean, the family variance strictly exceeds the family mean** — the distribution is not
sub-Poisson, full stop.  So the capstone is a *true implication with a false hypothesis*: no
averaging argument over the prime family can deliver the good prime.

The honest consequence (recorded in the thesis §7.6): the prize must be attacked **per-prime** — show
the *specific* prize prime is "round" (its cyclotomic prime ideal `𝔭` has no anomalously short
vector), which is the lattice-point equidistribution wall — not via the variance of the family.  This
brick closes the family-variance route as a *closure path*: it is structurally incompatible with the
measured over-dispersion.

`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ProximityGap.OverdispersionObstruction

open Finset

variable {ι : Type*}

/-- Total mass of a weight `W` over a finite family `s` (here `W i = W_r` at the `i`-th prime). -/
noncomputable def total (s : Finset ι) (W : ι → ℝ) : ℝ := ∑ i ∈ s, W i

/-- Empirical mean of `W` over `s`. -/
noncomputable def mean (s : Finset ι) (W : ι → ℝ) : ℝ := total s W / s.card

/-- Empirical (population) variance of `W` over `s`. -/
noncomputable def variance (s : Finset ι) (W : ι → ℝ) : ℝ :=
  (∑ i ∈ s, (W i - mean s W) ^ 2) / s.card

/-- **Single-term variance floor.** The variance over a family is at least one term of its defining
sum, because every term is a square (`≥ 0`).  This is the lever: one heavy prime alone forces a
large spread. -/
theorem variance_card_ge_single
    (s : Finset ι) (W : ι → ℝ) {j : ι} (hj : j ∈ s) :
    (W j - mean s W) ^ 2 ≤ ∑ i ∈ s, (W i - mean s W) ^ 2 :=
  single_le_sum (f := fun i => (W i - mean s W) ^ 2)
    (fun i _ => sq_nonneg _) hj

/-- **Over-dispersion theorem (the honest obstruction).**  If *any single* prime `j` carries a
wraparound value whose squared deviation from the mean exceeds the total mass,
`(W j - mean)² > total`, then the family variance strictly exceeds the family mean:
`variance > mean`.  Equivalently, the distribution is **not sub-Poisson** — exactly the situation the
probe measures, where one structured prime dominates.

Consequence: the thesis capstone's hypothesis `Var_P(W_r) ≤ mean_P(W_r)` is violated, so no
Chebyshev/averaging argument over the prime family can select a good prime.  The variance route is a
*true implication with a false hypothesis*. -/
theorem overdispersed_of_single_heavy
    (s : Finset ι) (W : ι → ℝ) {j : ι} (hj : j ∈ s)
    (hcard : 0 < (s.card : ℝ))
    (hheavy : total s W < (W j - mean s W) ^ 2) :
    mean s W < variance s W := by
  -- `variance·card = ∑ (W i - mean)² ≥ (W j - mean)² > total = mean·card`.
  have hsum : total s W < ∑ i ∈ s, (W i - mean s W) ^ 2 :=
    lt_of_lt_of_le hheavy (variance_card_ge_single s W hj)
  have hne : (s.card : ℝ) ≠ 0 := ne_of_gt hcard
  -- `mean·card = total` and `variance·card = ∑ (…)²`.
  have hmean : mean s W * (s.card : ℝ) = total s W := by
    rw [mean]; exact div_mul_cancel₀ _ hne
  have hvar : variance s W * (s.card : ℝ) = ∑ i ∈ s, (W i - mean s W) ^ 2 := by
    rw [variance]; exact div_mul_cancel₀ _ hne
  -- Multiply the strict inequality through by the positive card.
  have : mean s W * s.card < variance s W * s.card := by
    rw [hmean, hvar]; exact hsum
  exact lt_of_mul_lt_mul_right (by linarith) (le_of_lt hcard)

/-- **Corollary — the dominant-prime form (matches the probe).**  If one prime carries at least the
whole mean again on top of the mean (`W j ≥ 2·mean`) and the excess squared beats the total
(`(W j - mean)² > total`, automatic once `W j ≈ total ≫ √total`), the family is over-dispersed.  This
is the exact configuration the probe finds: a Fermat-like prime with `W` of order `total`, every
other prime near zero. -/
theorem not_subPoisson_of_dominant
    (s : Finset ι) (W : ι → ℝ) {j : ι} (hj : j ∈ s)
    (hcard : 0 < (s.card : ℝ))
    (hdom : total s W < (W j - mean s W) ^ 2) :
    ¬ (variance s W ≤ mean s W) := by
  have h := overdispersed_of_single_heavy s W hj hcard hdom
  exact not_le.mpr h

/-! ## Over-dispersion is BENIGN — the variance route attacked the wrong statistic

The probe `thin_above_onset` measures the *first computable window that resembles the prize* —
`n=16`, depth `r=5` **above** the onset `r₀≈4`, thinness `β≈4` — and finds **every** prime good
(`W₅/E₀ ∈ [0, 0.0057]`, all `≪ 1`), *including the Fermat prime* `p=65537`.  Crucially the wraparound
is **still over-dispersed** there (values `0 … 2.9M`), yet every value is `≪ E₀`.

So over-dispersion does not threaten the prize: the prize asks for a **sup / pointwise** bound
(`W_r(p*) ≤ slack` at the chosen prime — an *existence*, since the prize is free to choose `p`), which
is a *different statistic* from the family variance.  A family can be arbitrarily over-dispersed and
still uniformly good.  The theorem below exhibits this explicitly: the two conditions are independent,
so the over-dispersion refutation kills only the *variance route*, not the prize.  This corrects the
thesis capstone's framing: the credible reduction is to a **uniform sup bound** (every thin
above-onset prime is good — which is what the data shows with `>99.4%` margin), not to sub-Poisson
variance. -/

/-- **Over-dispersion is benign.**  The concrete two-prime family `W = ![B, 0]` is uniformly bounded
by `B` (good against any slack `≥ B`) yet **over-dispersed** (`variance > mean`) once `B > 2`.  Hence
"uniformly good (sup bound)" and "sub-Poisson (variance bound)" are **independent**: over-dispersion
never forces a prime past the slack.  The prize's real requirement is the sup bound, which the measured
over-dispersion leaves completely untouched — exactly as the thin-above-onset probe shows (every prime
good, `W₅/E₀ ≪ 1`, despite over-dispersed `W`). -/
theorem overdispersion_is_benign (B : ℝ) (hB : 2 < B) :
    (∀ i : Fin 2, (![B, 0] : Fin 2 → ℝ) i ≤ B) ∧
      mean (univ : Finset (Fin 2)) ![B, 0] < variance (univ : Finset (Fin 2)) ![B, 0] := by
  have hB0 : (0 : ℝ) < B := by linarith
  have hcard : ((univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp <;> linarith
  · have hmean : mean (univ : Finset (Fin 2)) ![B, 0] = B / 2 := by
      rw [mean, total, hcard, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring
    have hvar : variance (univ : Finset (Fin 2)) ![B, 0] = B ^ 2 / 4 := by
      rw [variance, hmean, hcard, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring
    rw [hmean, hvar]
    have hpos : (0 : ℝ) < B * (B - 2) := mul_pos hB0 (by linarith)
    nlinarith [hpos]

end ProximityGap.OverdispersionObstruction
