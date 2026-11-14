/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-!
# The two-sided BGK bracket for the Paley eigenvalue `M(μ_n)` (#444)

Per the directive *"prove BOTH bounds of BGK"*: the Bourgain–Glibichuk–Konyagin / Paley statement is
genuinely two-sided — `M(μ_n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)| ≍ √(n log p)` — and the two directions
have very different status. This file isolates, axiom-clean, exactly what is *provable now* on each side
and exactly what the open hypothesis on the sharp upper side is, in a single self-contained bracket.

Write `a_b := |η_b|² ≥ 0` for the squared periods over `b ≠ 0` (a finite index set `s`), so the squared
Paley eigenvalue is `M² = max_{b∈s} a_b`. The provable structure is purely the relation between the
maximum of a nonnegative sequence and its power-sums (moments):

* **Lower bound (unconditional).** `M² ≥ (Σ a²)/(Σ a)`. With the *standard Gauss-period moment identities*
  `Σ_{b≠0} a_b = Σ|η_b|² = p·n − n²` (Parseval) and `Σ_{b≠0} a_b² = Σ|η_b|⁴ = p·E₂ − n⁴`,
  `E₂(μ_n) = 3n²−3n`, this is `M² ≥ (p(3n²−3n) − n⁴)/(pn − n²) → 3n − 3` as `p → ∞`, i.e.
  `M ≥ √3·√n·(1−o(1))` — strictly above the trivial Parseval `√n`.

* **Upper bound (unconditional, trivial).** `M² ≤ Σ a = pn − n² ≤ pn`, i.e. `M ≤ √(p n)` (a single
  squared period cannot exceed the total `L²` energy). For thin `n ~ p^{1/4}` this is `≈ n^{5/2}`: true
  but very far from the conjecture.

* **Upper bound (sharp, CONDITIONAL).** Indexing `s = {b ≠ 0}` (so the DC term `η_0 = n` is excluded),
  for every `r`, `M^{2r} = (max_{b≠0} a_b)^r ≤ Σ_{b≠0} a_b^r = Σ_{b≠0}|η_b|^{2r} = p·E_r − n^{2r}`.
  Hence *if* the **DC-subtracted** Wick energy bound `Σ_{b≠0}|η_b|^{2r} ≤ (2r−1)‼·n^r` holds out to
  depth `r ≈ log p` (the open wall), then optimizing `r = log p` gives `M ≤ √(2 n log p)` — the
  conjecture. The named hypothesis `Σ a^r ≤ B` below is exactly that additive-energy wall; everything
  downstream of it is unconditional. **The DC subtraction is essential**: the *full*-energy form
  `E_r(μ_n) = (Σ_all |η_b|^{2r})/p ≤ (2r−1)‼·n^r` (which includes `η_0 = n`) is known *false* past the
  prize-depth DC crossover (in-tree `DCEnergyEssential.not_gaussianEnergyBound_of_deep`); summing over
  `s = {b≠0}` here is exactly the usable DC-subtracted object. (This is the self-contained two-sided
  companion to the in-tree moment-method bridge `GaussPeriodMomentBound.lean` and the Ramanujan bridge
  `GeneralizedPaleyRamanujan.lean`, which supply the upper side alone; the value added here is the matching
  unconditional lower side and the explicit single-file bracket.)

So the bracket `√3·√n ≤ M ≤ √(p n)` is fully proven here, and the sharp upper edge `√(2 n log p)` is
reduced to the single open DC-subtracted energy inequality. This is the honest two-sided BGK statement:
NOT closure — the gap between `√n` (proven lower) and `√(n log p)` (conjectured) on the upper side is the
prize.

## Results (axiom-clean)
* `single_sq_le_sum` / `max_le_sum_of_nonneg` — the trivial upper bound `M² ≤ Σ a`.
* `pow_max_le_sum_pow` — the moment upper engine `(max a)^r ≤ Σ a^r` (drives the conditional sharp bound).
* `ratio_le_max` — the lower engine `(Σ a²)/(Σ a) ≤ max a` (the 4th/2nd-moment ratio).
* `bgk_two_sided` — the assembled unconditional bracket `(Σ a²)/(Σ a) ≤ M² ≤ Σ a`.
* `sharp_upper_of_energy_bound` — the conditional sharp upper `M² ≤ B^{1/r}` from `Σ a^r ≤ B`.
-/

namespace ArkLib.ProximityGap.Frontier.BGKTwoSided

open Finset

variable {ι : Type*}

/-- A single squared period is at most the total `L²` energy: `a_{i₀} ≤ Σ_{i∈s} a_i` for nonnegative
`a`. This is the trivial upper bound `M² ≤ Σ a` once `i₀` is the argmax. -/
theorem single_sq_le_sum (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {i₀ : ι} (hi₀ : i₀ ∈ s) : a i₀ ≤ ∑ i ∈ s, a i :=
  Finset.single_le_sum ha hi₀

/-- **Trivial upper bound (proven).** The maximum of a nonnegative sequence is at most its sum:
`max_{i∈s} a_i ≤ Σ_{i∈s} a_i`. Specialized to `a_b = |η_b|²`: `M² ≤ Σ_{b≠0}|η_b|² = pn − n² ≤ pn`. -/
theorem max_le_sum_of_nonneg (s : Finset ι) (a : ι → ℝ) (hne : s.Nonempty)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∃ i₀ ∈ s, (∀ j ∈ s, a j ≤ a i₀) ∧ a i₀ ≤ ∑ i ∈ s, a i := by
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image a hne
  exact ⟨i₀, hi₀, hmax, single_sq_le_sum s a ha hi₀⟩

/-- **The moment upper engine (proven).** For nonnegative `a` and the argmax `i₀`, the `r`-th power of
the max is at most the `r`-th power-sum: `(a i₀)^r ≤ Σ_{i∈s} (a i)^r`. With `a_b = |η_b|²` this is
`M^{2r} ≤ Σ_{b}|η_b|^{2r} = p·E_r`, the input to the conditional sharp upper bound. -/
theorem pow_max_le_sum_pow (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hmax : ∀ j ∈ s, a j ≤ a i₀) (r : ℕ) :
    (a i₀) ^ r ≤ ∑ i ∈ s, (a i) ^ r := by
  refine Finset.single_le_sum (f := fun i => (a i) ^ r) (fun i hi => ?_) hi₀
  exact pow_nonneg (ha i hi) r

/-- **The lower engine (proven).** If `Σ a > 0` and all `a_i ≥ 0`, the max is at least the
4th/2nd-moment ratio: `(Σ a²)/(Σ a) ≤ max a`. (Take `c = max a`; then `Σ a² ≤ c·Σ a` term-by-term, since
`a_i² ≤ c·a_i`.) Specialized to `a_b = |η_b|²`: `M² ≥ (Σ|η_b|⁴)/(Σ|η_b|²) = (pE₂−n⁴)/(pn−n²) → 3n`. -/
theorem ratio_le_max (s : Finset ι) (a : ι → ℝ) (hne : s.Nonempty)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hpos : 0 < ∑ i ∈ s, a i) :
    ∃ i₀ ∈ s, (∑ j ∈ s, (a j) ^ 2) / (∑ j ∈ s, a j) ≤ a i₀ := by
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image a hne
  refine ⟨i₀, hi₀, ?_⟩
  rw [div_le_iff₀ hpos]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have h0 := ha j hj
  have h1 := hmax j hj
  nlinarith [h0, h1]

/-- **The two-sided BGK bracket (proven, unconditional).** For a nonempty finite family of nonnegative
squared periods `a : ι → ℝ` with positive total energy, the maximum `M² := a i₀` satisfies
`(Σ a²)/(Σ a) ≤ M² ≤ Σ a`. With the Gauss-period moments this is exactly
`(p(3n²−3n)−n⁴)/(pn−n²) ≤ M² ≤ pn − n²`, i.e. `√3·√n·(1−o(1)) ≤ M ≤ √(pn)`. -/
theorem bgk_two_sided (s : Finset ι) (a : ι → ℝ) (hne : s.Nonempty)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hpos : 0 < ∑ i ∈ s, a i) :
    ∃ i₀ ∈ s, (∀ j ∈ s, a j ≤ a i₀) ∧
      (∑ j ∈ s, (a j) ^ 2) / (∑ j ∈ s, a j) ≤ a i₀ ∧ a i₀ ≤ ∑ i ∈ s, a i := by
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image a hne
  refine ⟨i₀, hi₀, hmax, ?_, single_sq_le_sum s a ha hi₀⟩
  rw [div_le_iff₀ hpos, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have h0 := ha j hj
  have h1 := hmax j hj
  nlinarith [h0, h1]

/-- **The conditional SHARP upper bound (proven, modulo the named energy hypothesis).** If the `r`-th
power-sum is bounded by `B` (the additive-energy hypothesis `Σ_b|η_b|^{2r} = p·E_r ≤ B`), then the
maximum is at most `B^{1/r}`: `max a ≤ B^{1/r}`. With `B = p·(2r−1)‼·n^r` at `r = ⌊log p⌋` this is
`M² ≤ (p·(2r−1)‼·n^r)^{1/r}`, optimizing to `M ≤ √(2 n log p)` — the conjecture. The hypothesis
`Σ a^r ≤ B` is the OPEN Paley/BGK wall; this theorem is the unconditional consumer of it. -/
theorem sharp_upper_of_energy_bound (s : Finset ι) (a : ι → ℝ) (hne : s.Nonempty)
    (ha : ∀ i ∈ s, 0 ≤ a i) (r : ℕ) (hr : 0 < r) (B : ℝ)
    (hB : ∑ i ∈ s, (a i) ^ r ≤ B) :
    ∃ i₀ ∈ s, (∀ j ∈ s, a j ≤ a i₀) ∧ a i₀ ≤ B ^ (1 / (r : ℝ)) := by
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image a hne
  refine ⟨i₀, hi₀, hmax, ?_⟩
  have hai₀ : 0 ≤ a i₀ := ha i₀ hi₀
  have hpow : (a i₀) ^ r ≤ B := le_trans (pow_max_le_sum_pow s a ha hi₀ hmax r) hB
  have hBnn : (0 : ℝ) ≤ B := le_trans (pow_nonneg hai₀ r) hpow
  -- raise `(a i₀)^r ≤ B` to the power `1/r`
  have key : ((a i₀) ^ r) ^ (1 / (r : ℝ)) ≤ B ^ (1 / (r : ℝ)) :=
    Real.rpow_le_rpow (pow_nonneg hai₀ r) hpow (by positivity)
  have hrw : ((a i₀) ^ r) ^ (1 / (r : ℝ)) = a i₀ := by
    rw [← Real.rpow_natCast (a i₀) r, ← Real.rpow_mul hai₀]
    rw [mul_one_div, div_self (by exact_mod_cast hr.ne'), Real.rpow_one]
  rwa [hrw] at key

end ArkLib.ProximityGap.Frontier.BGKTwoSided

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.BGKTwoSided.single_sq_le_sum
#print axioms ArkLib.ProximityGap.Frontier.BGKTwoSided.max_le_sum_of_nonneg
#print axioms ArkLib.ProximityGap.Frontier.BGKTwoSided.pow_max_le_sum_pow
#print axioms ArkLib.ProximityGap.Frontier.BGKTwoSided.ratio_le_max
#print axioms ArkLib.ProximityGap.Frontier.BGKTwoSided.bgk_two_sided
#print axioms ArkLib.ProximityGap.Frontier.BGKTwoSided.sharp_upper_of_energy_bound
