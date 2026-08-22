/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Door refutation: the geometric mean (Mahler-measure / log-average) of the spectrum lies BELOW the
max, so the Mahler / murmuration "average" levers are on the wrong side of the prize max (#444)

## Motivation (rule-4 + rule-5: a refuted lever is a result; back the prose verdict with a kernel)

The #444 literature-mining record (`docs/kb/deltastar-444-latest-literature-mining-2026-06-21.md`,
commit `aeb9e8da9`) flags four genuinely-fresh 2024-26 clusters and gives the funnel verdicts in
PROSE.  Two of them — **(d) asymptotic Mahler measure of Gaussian periods** and **(b) murmurations of
Dirichlet characters** — are refuted by the SAME mechanism: they are AVERAGE phenomena (Mahler measure
is a GEOMETRIC mean / log-average of the conjugate magnitudes; a murmuration is a DENSITY), so they
control the TYPICAL `|η_b|`, not the WORST-CASE max `M(n) = max_{b≠0}|η_b|` that the prize is about.
"Average, the wrong side of `√n`."

This file makes that mechanism an EXACT, machine-checked constraint: the geometric mean of the
nonnegative spectrum is at most its maximum (entrywise upper bound).  Hence any Mahler-measure /
log-average / murmuration-density control of the spectrum is automatically a LOWER-resolution object
than `M`; it can never exceed (and so never certify a bound below) the max.  This kernels the
"average-not-max" half of the (b)/(d) cluster verdicts, complementing
`_DoorIVFractionalMomentNoMaxGain` (which kernels the same for fractional `ℓ^{2q}` moment roots).

## The load-bearing facts (this file, axiom-clean)

* **Geometric mean ≤ max.**  For a finset `s`, nonnegative `lam : ι → ℝ` with entrywise bound
  `lam i ≤ M`, the geometric mean `(∏_{i∈s} lam i)^{1/card s} ≤ M`.  (The Mahler-measure analogue:
  `exp(mean log lam) ≤ max lam`.)
* **Product ≤ max^card.**  The underlying un-rooted form `∏_{i∈s} lam i ≤ M ^ card s`.

NOT a CORE / cancellation / completion / moment-saving / anti-concentration / capacity claim: it
bounds nothing about `M(n)` itself.  It records why a geometric-mean / density lever cannot be the
prize lever — it lives strictly below the max it would need to control.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax

open scoped Real

variable {ι : Type*}

/-- **Product of a max-bounded nonnegative family ≤ max^card.**  If every `lam i ≤ M` on `s` with
`lam` nonnegative, then `∏_{i∈s} lam i ≤ M ^ (card s)`. -/
theorem prod_le_max_pow_card (s : Finset ι) (lam : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ lam i) {M : ℝ} (hM : ∀ i ∈ s, lam i ≤ M) :
    ∏ i ∈ s, lam i ≤ M ^ s.card := by
  calc
    ∏ i ∈ s, lam i ≤ ∏ _i ∈ s, M :=
      Finset.prod_le_prod hnn (fun i hi => hM i hi)
    _ = M ^ s.card := by rw [Finset.prod_const]

/-- **Sum of a max-bounded family ≤ card times max.**  If every `lam i ≤ M` on `s`, then
the additive average numerator is at most `card s * M`.  This is the arithmetic-mean analogue of
`prod_le_max_pow_card`. -/
theorem sum_le_card_mul_max (s : Finset ι) (lam : ι → ℝ) {M : ℝ}
    (hM : ∀ i ∈ s, lam i ≤ M) :
    ∑ i ∈ s, lam i ≤ (s.card : ℝ) * M := by
  calc
    ∑ i ∈ s, lam i ≤ ∑ _i ∈ s, M :=
      Finset.sum_le_sum (fun i hi => hM i hi)
    _ = (s.card : ℝ) * M := by simp [Finset.sum_const, nsmul_eq_mul]

/-- **Arithmetic mean ≤ max (the density / murmuration no-transfer constraint).**  For a nonempty
finset `s`, any additive average of values bounded entrywise by `M` is itself at most `M`.  Thus
a density or arithmetic-average control of Door-IV periods is a lower-resolution object than the
worst-case max; it does not by itself bound the adversarial `b`. -/
theorem arithMean_le_max (s : Finset ι) (hs : s.Nonempty) (lam : ι → ℝ) {M : ℝ}
    (hM : ∀ i ∈ s, lam i ≤ M) :
    (∑ i ∈ s, lam i) / (s.card : ℝ) ≤ M := by
  have hcardpos : (0 : ℝ) < s.card := by
    have : 0 < s.card := Finset.Nonempty.card_pos hs
    exact_mod_cast this
  have hsum : ∑ i ∈ s, lam i ≤ (s.card : ℝ) * M :=
    sum_le_card_mul_max s lam hM
  have hdiv : (∑ i ∈ s, lam i) / (s.card : ℝ) ≤
      ((s.card : ℝ) * M) / (s.card : ℝ) :=
    div_le_div_of_nonneg_right hsum (le_of_lt hcardpos)
  simpa [mul_comm, ne_of_gt hcardpos] using hdiv

/-- **An arithmetic mean above a threshold exposes a point above that threshold.**  Uniform density
excess cannot hide a worst-case upper-control certificate: if the average is strictly above `C`, at
least one entry already exceeds `C`. -/
theorem exists_gt_of_lt_arithMean (s : Finset ι) (hs : s.Nonempty) (lam : ι → ℝ)
    {C : ℝ} (hgt : C < (∑ i ∈ s, lam i) / (s.card : ℝ)) :
    ∃ i ∈ s, C < lam i := by
  by_contra hno
  have hC : ∀ i ∈ s, lam i ≤ C := by
    intro i hi
    exact le_of_not_gt (fun hlt => hno ⟨i, hi, hlt⟩)
  have hle : (∑ i ∈ s, lam i) / (s.card : ℝ) ≤ C :=
    arithMean_le_max s hs lam hC
  exact not_lt_of_ge hle hgt

/-- **Weighted average ≤ max.**  Any probability-weighted average of entries bounded by `M` is
bounded by the same `M`.  This is the exact finite form of the density/no-transfer obstruction:
changing the averaging measure (murmuration weights, sampled conjugacy classes, or a biased literature
statistic) still leaves the object below the adversarial worst-case maximum. -/
theorem weightedMean_le_max (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) = 1)
    {M : ℝ} (hM : ∀ i ∈ s, lam i ≤ M) :
    ∑ i ∈ s, w i * lam i ≤ M := by
  calc
    ∑ i ∈ s, w i * lam i ≤ ∑ i ∈ s, w i * M :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hM i hi) (hw_nonneg i hi))
    _ = (∑ i ∈ s, w i) * M := by rw [Finset.sum_mul]
    _ = M := by simp [hw_sum]

/-- **Subprobability weighted average ≤ max.**  If the nonnegative weights have total mass at most
one and `0 ≤ M`, a weighted density statistic is still bounded by `M`.  This covers truncated or
partial averaging windows: losing mass cannot turn an average-side lever into a worst-case max lever. -/
theorem weightedSubmean_le_max (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) ≤ 1)
    {M : ℝ} (hM_nonneg : 0 ≤ M) (hM : ∀ i ∈ s, lam i ≤ M) :
    ∑ i ∈ s, w i * lam i ≤ M := by
  have hweighted : ∑ i ∈ s, w i * lam i ≤ (∑ i ∈ s, w i) * M := by
    calc
      ∑ i ∈ s, w i * lam i ≤ ∑ i ∈ s, w i * M :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hM i hi) (hw_nonneg i hi))
      _ = (∑ i ∈ s, w i) * M := by rw [Finset.sum_mul]
  have hmass : (∑ i ∈ s, w i) * M ≤ 1 * M :=
    mul_le_mul_of_nonneg_right hw_sum hM_nonneg
  simpa using le_trans hweighted hmass

/-- **A weighted average beating a threshold exposes a point above that threshold.**  A density /
murmuration statistic cannot hide an adversarial frequency: if a probability-weighted average is
strictly larger than `C`, then some sampled value is strictly larger than `C`.  Thus an average-side
witness is only a lower witness for the worst-case max, not an upper-control mechanism. -/
theorem exists_gt_of_lt_weightedMean (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) = 1)
    {C : ℝ} (hgt : C < ∑ i ∈ s, w i * lam i) :
    ∃ i ∈ s, C < lam i := by
  by_contra hno
  have hC : ∀ i ∈ s, lam i ≤ C := by
    intro i hi
    exact le_of_not_gt (fun hlt => hno ⟨i, hi, hlt⟩)
  have hle : ∑ i ∈ s, w i * lam i ≤ C :=
    weightedMean_le_max s w lam hw_nonneg hw_sum hC
  exact not_lt_of_ge hle hgt

/-- **A subprobability average beating a nonnegative threshold still exposes a point above it.**
Truncating the averaging window does not create hidden upper control: any strict excess over `C ≥ 0`
comes from at least one entry already exceeding `C`. -/
theorem exists_gt_of_lt_weightedSubmean (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) ≤ 1)
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hgt : C < ∑ i ∈ s, w i * lam i) :
    ∃ i ∈ s, C < lam i := by
  by_contra hno
  have hC : ∀ i ∈ s, lam i ≤ C := by
    intro i hi
    exact le_of_not_gt (fun hlt => hno ⟨i, hi, hlt⟩)
  have hle : ∑ i ∈ s, w i * lam i ≤ C :=
    weightedSubmean_le_max s w lam hw_nonneg hw_sum hC_nonneg hC
  exact not_lt_of_ge hle hgt

/-- **Geometric mean ≤ max (the Mahler / log-average no-transfer constraint).**  For a nonempty
finset `s` and nonnegative `lam` with entrywise bound `lam i ≤ M` (so `0 ≤ M`), the geometric mean
satisfies `(∏_{i∈s} lam i)^{1/card s} ≤ M`.

This is the kerneled form of the (b)/(d) cluster verdict: a Mahler-measure (geometric mean) or
murmuration (density / average) control of the spectrum lies at or below the max `M`; it is the wrong
object for a worst-case max bound. -/
theorem geomMean_le_max (s : Finset ι) (hs : s.Nonempty) (lam : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ lam i) {M : ℝ} (hM : ∀ i ∈ s, lam i ≤ M) :
    (∏ i ∈ s, lam i) ^ ((1 : ℝ) / s.card) ≤ M := by
  obtain ⟨i₁, hi₁⟩ := hs
  have hMnn : 0 ≤ M := le_trans (hnn i₁ hi₁) (hM i₁ hi₁)
  have hcardpos : (0 : ℝ) < s.card := by
    have : 0 < s.card := Finset.Nonempty.card_pos ⟨i₁, hi₁⟩
    exact_mod_cast this
  have hprod_nn : 0 ≤ ∏ i ∈ s, lam i :=
    Finset.prod_nonneg hnn
  have hprod_le : ∏ i ∈ s, lam i ≤ M ^ s.card :=
    prod_le_max_pow_card s lam hnn hM
  -- raise to 1/card (monotone on nonnegatives), then collapse (M^card)^{1/card} = M
  have hmono : (∏ i ∈ s, lam i) ^ ((1 : ℝ) / s.card)
      ≤ (M ^ s.card) ^ ((1 : ℝ) / s.card) :=
    Real.rpow_le_rpow hprod_nn (by exact_mod_cast hprod_le) (by positivity)
  have hcollapse : (M ^ s.card) ^ ((1 : ℝ) / s.card) = M := by
    rw [← Real.rpow_natCast M s.card, ← Real.rpow_mul hMnn]
    rw [mul_one_div, div_self (ne_of_gt hcardpos), Real.rpow_one]
  rwa [hcollapse] at hmono

/-- **A geometric mean above a threshold exposes a point above that threshold.**  Mahler-measure /
log-average excess is a lower witness for the worst conjugate, not an upper-control mechanism: if the
geometric mean is strictly above `C`, then at least one entry is strictly above `C`. -/
theorem exists_gt_of_lt_geomMean (s : Finset ι) (hs : s.Nonempty) (lam : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ lam i) {C : ℝ}
    (hgt : C < (∏ i ∈ s, lam i) ^ ((1 : ℝ) / s.card)) :
    ∃ i ∈ s, C < lam i := by
  by_contra hno
  have hC : ∀ i ∈ s, lam i ≤ C := by
    intro i hi
    exact le_of_not_gt (fun hlt => hno ⟨i, hi, hlt⟩)
  have hle : (∏ i ∈ s, lam i) ^ ((1 : ℝ) / s.card) ≤ C :=
    geomMean_le_max s hs lam hnn hC
  exact not_lt_of_ge hle hgt

end ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax

#print axioms ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.prod_le_max_pow_card
#print axioms ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.sum_le_card_mul_max
#print axioms ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.arithMean_le_max
#print axioms ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_arithMean
#print axioms ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.weightedMean_le_max
#print axioms ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.weightedSubmean_le_max
#print axioms ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_weightedMean
#print axioms ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_weightedSubmean
#print axioms ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.geomMean_le_max
#print axioms ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_geomMean
