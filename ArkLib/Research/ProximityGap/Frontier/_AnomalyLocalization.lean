/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Anomaly localization — the moment method CANNOT beat the sup-norm (BRICK L3b, #444)

**Adversarial classification of the char-`p` additive-energy anomaly.**

## The measured object (probe `scripts/probes/probe_anomaly_localization.py`)

The proximity-prize δ* floor reduces (moment method) to a char-`p` Gauss-period sup-norm
`M(n) = max_{b≠0} ‖η_b‖`, `η_b = ∑_{x∈μ_n} e_p(bx)`, over the 2-power subgroup `μ_n ⊊ 𝔽_p^*`.
The EXACT moment identity (Parseval) is

      p · E_r(μ_n)  =  ∑_b ‖η_b‖^{2r}  =  n^{2r}  +  S_r,    S_r := ∑_{b≠0} ‖η_b‖^{2r},

so the per-frequency masses `‖η_b‖^{2r}` are a nonnegative finite spectrum and `E_r` is their
(scaled) `r`-th power sum.  Writing `λ_b := ‖η_b‖²` (nonnegative), `S_r = ∑_{b≠0} λ_b^r`.

## The L3b question and the MEASURED verdict (`(b)` CONCENTRATES ⇒ REDUCES-TO-WALL)

Decompose `E_r = Wick_r + Excess_r`, `Wick_r = (2r-1)‼·n^r` (char-0 Gaussian baseline).
Does the off-DC excess EQUIDISTRIBUTE over the `m=(p-1)/n` frequencies `b≠0` (then per-freq it
is `≤ S_r/(p-1)` and `M` is unaffected — a real lead, answer (a)), or CONCENTRATE on a few `b`
(then `M` is raised — answer (b), reduces-to-wall)?  The probe settles it with exact numbers at
`β=4`, `n∈{16,32,64}` (`E_r` cross-checked to ~1e-15 against int64-exact convolution counts):

  * **`{b≠0 : ‖η_b‖ = M}` is EXACTLY ONE coset `b₀·μ_n` of size `n`** — a single Galois/Frobenius
    conjugate orbit.  This is the **BGK conjugate-norm structure** (the wall object).
  * **The off-DC mass `S_r` is increasingly carried by that single orbit as `r` grows**:
    M-orbit-fraction climbs `0.07 → 0.86` (n=16) / `0.03 → 0.61` (n=32) / `0.01 → 0.79` (n=64)
    from `r=4` to `r=16`, vs the EQUIDISTRIBUTION value `orbit/(p-1) ≈ 1e-4 … 1e-6` (4–6 orders
    too small).  The top 1% of frequencies carry ≈100% of `S_r` at deep `r`.  NOT equidistributed.
  * **MECHANISM — moment-method M-orbit concentration.**  Because `S_r` is M-orbit dominated,
    both the floored bound `A=(p E_r)^{1/2r}` and the DC-dropped bound `B=(p E_r-n^{2r})^{1/2r}`
    converge DOWN to the single magnitude `M` (`B/M → 1`); dropping DC barely helps (`A/B = 1.00…1.45`)
    and `B` still fails to deliver the floor with any scale-uniform margin.  No moment depth `r`
    yields an upper bound below `M`.  The moment route is bounded below by `M` = the BCHKS/BGK-Paley
    char-`p` Gauss-period sup-norm itself.  **REDUCES-TO-WALL.**

## What is PROVEN here (axiom-clean `{propext, Classical.choice, Quot.sound}`)

The Lean obstruction is the EXACT structural reason the verdict is (b): on ANY nonnegative finite
spectrum, the `r`-th-root power-sum bound is **always ≥ the maximum**, with the DC-dropped variant
just as binding.  This is precisely "the moment method cannot beat `M`" — the quantitative content
the probe sees as `B/M → 1`.

* `moment_root_ge_max` (HEADLINE, full spectrum):  for nonnegative `λ : ι → ℝ` on a finset `s`,
  `i₀ ∈ s`, `r ≥ 1`:   `λ i₀  ≤  (∑_{i∈s} (λ i)^r)^{(1/r)}`.   Hence `(∑ λ^r)^{1/r} ≥ max λ`.
  (The single peak is a summand of the power-sum, and `x ↦ x^{1/r}` is monotone.)
* `moment_root_ge_max_offDC` (PRIZE-RELEVANT, DC-dropped):  restrict to `s = {b≠0}` and the same
  bound holds with the maximizer `i₀ = b*` (the M-orbit).  So `B = (∑_{b≠0} λ_b^r)^{1/r} ≥ M²`,
  i.e. dropping the DC term `n^{2r}` does NOT let the moment root dip below the off-DC max `M²`.
  The off-DC moment root is bounded BELOW by the wall, for every depth `r`.
* `moment_no_improvement_over_max` (the L3b corollary):  combining with the matching UPPER bound
  `(∑_{i∈s} (λ i)^r)^{1/r} ≤ (card s)^{1/r} · max` (also proven here), the moment root is pinned to
  `max` up to the depth-vanishing factor `(card s)^{1/r}`.  Formally: NO finite depth `r` produces a
  certificate strictly below `max λ`.  The "anomaly" mass cannot do better than the extreme `M`.

These are the field-universal, char-free, EASY/honest direction (a LOWER bound on what the moment
method can certify).  They do NOT close the wall (the wall is the matching analytic UPPER bound on
`M(n)` itself, `M(n) ≤ C√(n log m)`, untouched).  Per the §6 contract this brick proves the
obstruction, NOT the prize: it certifies that the moment route is structurally pinned to `M`, which
is exactly why the L3b verdict is "reduces-to-wall" rather than a lead.

## References
- `scripts/probes/probe_anomaly_localization.py` (the exact measurement; `0 fails`, reproducible).
- `EnergyRatioSupNormLower.lean` (the ratio-form companion: `E_{r+1}/E_r ≤ M²`, lower-bracketing
  `M²` from the energies; this brick adds the matching ROOT-form pinning that nails concentration).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
-/

open Finset

set_option autoImplicit false

namespace ProximityGap.Frontier.AnomalyLocalization

variable {ι : Type*}

/-- **HEADLINE — the moment power-sum root dominates the maximum (full spectrum).**
For a nonnegative spectrum `lam : ι → ℝ` on a finset `s`, any `i₀ ∈ s`, and depth `r ≥ 1`,
the single peak is at most the `r`-th root of the `r`-th power sum:

    `lam i₀ ≤ (∑_{i∈s} (lam i)^r) ^ (1/r)`.

Specialising `lam = ‖η_b‖²`, this is `M² ≤ (p E_r)^{1/r}` (taking `s = 𝔽_p`, `i₀ = DC`), i.e. the
moment bound can NEVER dip below the largest per-frequency mass.  The quantitative content of the
probe's `B/M → 1`: the moment method is pinned from below by the extreme `M`. -/
theorem moment_root_ge_max (s : Finset ι) (lam : ι → ℝ) (hnn : ∀ i ∈ s, 0 ≤ lam i)
    {i₀ : ι} (hi₀ : i₀ ∈ s) {r : ℕ} (hr : 1 ≤ r) :
    lam i₀ ≤ (∑ i ∈ s, (lam i) ^ r) ^ ((1 : ℝ) / r) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  -- the peak's r-th power is a single summand of the (nonneg) power sum
  have hterm : (lam i₀) ^ r ≤ ∑ i ∈ s, (lam i) ^ r :=
    Finset.single_le_sum (f := fun i => (lam i) ^ r)
      (fun i hi => pow_nonneg (hnn i hi) r) hi₀
  have hsum_nn : 0 ≤ ∑ i ∈ s, (lam i) ^ r :=
    Finset.sum_nonneg (fun i hi => pow_nonneg (hnn i hi) r)
  have hlam0 : 0 ≤ lam i₀ := hnn i₀ hi₀
  -- raise both sides to the (1/r) power (monotone on nonnegatives), then simplify (x^r)^{1/r}=x
  have hmono : ((lam i₀) ^ r) ^ ((1 : ℝ) / r) ≤ (∑ i ∈ s, (lam i) ^ r) ^ ((1 : ℝ) / r) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hterm) (by positivity)
  have hcollapse : ((lam i₀) ^ r) ^ ((1 : ℝ) / r) = lam i₀ := by
    rw [← Real.rpow_natCast (lam i₀) r, ← Real.rpow_mul hlam0]
    rw [mul_one_div, div_self (ne_of_gt hrpos), Real.rpow_one]
  rwa [hcollapse] at hmono

/-- **Matching UPPER bound — the moment root exceeds the max by at most `(card s)^{1/r}`.**
For nonnegative `lam` with entrywise upper bound `M` on `s`:

    `(∑_{i∈s} (lam i)^r) ^ (1/r) ≤ (card s)^{1/r} · M`.

Combined with `moment_root_ge_max`, the moment root is squeezed into `[max, (card s)^{1/r}·max]`,
and the multiplier `(card s)^{1/r} → 1` as `r → ∞`.  So as depth grows the moment bound converges
DOWN to `max` (the probe's `B/M → 1`); it cannot certify anything below the wall value `max`. -/
theorem moment_root_le_card_root_mul_max (s : Finset ι) (lam : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ lam i) {M : ℝ} (hM : ∀ i ∈ s, lam i ≤ M) {r : ℕ} (hr : 1 ≤ r) :
    (∑ i ∈ s, (lam i) ^ r) ^ ((1 : ℝ) / r) ≤ (s.card : ℝ) ^ ((1 : ℝ) / r) * M := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  -- empty case: both sides are 0; nonempty case gives `0 ≤ M` for the rpow algebra
  rcases Finset.eq_empty_or_nonempty s with hs | ⟨i₁, hi₁⟩
  · subst hs
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    rw [Real.zero_rpow (by positivity), zero_mul]
  have hMnn : 0 ≤ M := le_trans (hnn i₁ hi₁) (hM i₁ hi₁)
  -- each (lam i)^r ≤ M^r, so the sum ≤ card·M^r
  have hbound : ∑ i ∈ s, (lam i) ^ r ≤ (s.card : ℝ) * M ^ r := by
    have : ∑ i ∈ s, (lam i) ^ r ≤ ∑ _i ∈ s, M ^ r :=
      Finset.sum_le_sum (fun i hi => pow_le_pow_left₀ (hnn i hi) (hM i hi) r)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hsum_nn : 0 ≤ ∑ i ∈ s, (lam i) ^ r :=
    Finset.sum_nonneg (fun i hi => pow_nonneg (hnn i hi) r)
  -- raise to (1/r); RHS (card·M^r)^{1/r} = card^{1/r}·M
  have hmono : (∑ i ∈ s, (lam i) ^ r) ^ ((1 : ℝ) / r)
      ≤ ((s.card : ℝ) * M ^ r) ^ ((1 : ℝ) / r) :=
    Real.rpow_le_rpow hsum_nn hbound (by positivity)
  have hcardnn : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  have hMr_nn : (0 : ℝ) ≤ M ^ r := pow_nonneg hMnn r
  have hsplit : ((s.card : ℝ) * M ^ r) ^ ((1 : ℝ) / r)
      = (s.card : ℝ) ^ ((1 : ℝ) / r) * M := by
    rw [Real.mul_rpow hcardnn hMr_nn]
    congr 1
    rw [← Real.rpow_natCast M r, ← Real.rpow_mul hMnn, mul_one_div, div_self (ne_of_gt hrpos),
      Real.rpow_one]
  rwa [hsplit] at hmono

/-- **PRIZE-RELEVANT (DC-dropped) form — the off-DC moment root is bounded below by the off-DC max.**
This is `moment_root_ge_max` applied with `s` the NON-principal frequency set (intended `{b≠0}`) and
`i₀` the maximizer (the M-orbit).  With `lam_b = ‖η_b‖²` and `i₀ = b*` achieving `M² = max_{b≠0}λ_b`:

    `M²  ≤  (∑_{b≠0} ‖η_b‖^{2r}) ^ (1/r)  =  B²`,

i.e. the DC-dropped bound `B = (p E_r - n^{2r})^{1/2r}` satisfies `B ≥ M`.  Dropping the DC term does
NOT let the moment root sink below `M`.  This is the EXACT formal obstruction the probe measures:
even after removing the principal `n^{2r}`, the off-DC moment mass `S_r` is pinned from below by its
own extreme summand (the BGK M-orbit), so the moment route cannot beat the wall. -/
theorem moment_root_ge_max_offDC (s : Finset ι) (lam : ι → ℝ) (hnn : ∀ i ∈ s, 0 ≤ lam i)
    {bstar : ι} (hb : bstar ∈ s) (hmax : ∀ i ∈ s, lam i ≤ lam bstar) {r : ℕ} (hr : 1 ≤ r) :
    lam bstar ≤ (∑ i ∈ s, (lam i) ^ r) ^ ((1 : ℝ) / r) :=
  moment_root_ge_max s lam hnn hb hr

/-- **The L3b corollary — NO finite moment depth certifies below the max (the "no improvement"
sandwich).**  On a nonempty nonnegative spectrum with maximizer `bstar` (`M := lam bstar`), every
moment-root bound is squeezed:

    `M  ≤  (∑_{i∈s} (lam i)^r)^{(1/r)}  ≤  (card s)^{(1/r)} · M`.

The lower side says the moment method can never certify a value `< M`; the upper side says the only
slack is the depth-vanishing factor `(card s)^{1/r}`.  Specialising to `s = {b≠0}`, `M = max_{b≠0}‖η_b‖²`,
this is the analytic statement of the probe verdict: the off-DC moment route is pinned to the BGK
sup-norm `M` (concentration ⇒ reduces-to-wall), not to any spread-out `S_r/(p-1)`. -/
theorem moment_no_improvement_over_max (s : Finset ι) (lam : ι → ℝ) (hnn : ∀ i ∈ s, 0 ≤ lam i)
    {bstar : ι} (hb : bstar ∈ s) (hmax : ∀ i ∈ s, lam i ≤ lam bstar) {r : ℕ} (hr : 1 ≤ r) :
    lam bstar ≤ (∑ i ∈ s, (lam i) ^ r) ^ ((1 : ℝ) / r) ∧
    (∑ i ∈ s, (lam i) ^ r) ^ ((1 : ℝ) / r) ≤ (s.card : ℝ) ^ ((1 : ℝ) / r) * lam bstar := by
  refine ⟨moment_root_ge_max s lam hnn hb hr, ?_⟩
  exact moment_root_le_card_root_mul_max s lam hnn hmax hr

end ProximityGap.Frontier.AnomalyLocalization

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.AnomalyLocalization.moment_root_ge_max
#print axioms ProximityGap.Frontier.AnomalyLocalization.moment_root_le_card_root_mul_max
#print axioms ProximityGap.Frontier.AnomalyLocalization.moment_root_ge_max_offDC
#print axioms ProximityGap.Frontier.AnomalyLocalization.moment_no_improvement_over_max
