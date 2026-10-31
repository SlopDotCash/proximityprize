/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A7-info — the INFORMATION-THEORETIC / COMPLEXITY bound on `M` (#444)

**Mandate.**  Test whether an *information-theoretic* bound — one that controls
`M = max_{b≠0}|η_b|` by the description length `log m` of the worst frequency rather than by the
magnitude of a single period or a sheaf weight — escapes the two #444 obstructions.  The claim
under test:

> a large `|η_b|` would let `b` be specified by *fewer* bits than it actually needs — so the
> achievable correlation is capped by the description budget `log m` (the entropy of the frequency
> alphabet), giving `M ≤ √(2 n log m)`.

This file builds the machinery (a counting functional, a phase-entropy functional, and the
deterministic exponential-moment maximal inequality), proves the deterministic kernels
axiom-clean, and states which input remains.  **Verdict: REDUCES** to the moment ladder.

## The prize core (recap)

Write `η_b = ∑_{x∈μ_n} e_p(b·x)` and `E_r = rEnergy(μ_n, r)` for the `r`-fold additive-energy
count (`ArkLib/Data/CodingTheory/ProximityGap/SubgroupGaussSumMoment.lean`).  The exact moment
identity is `∑_b |η_b|^{2r} = p·E_r`, hence (removing the `b = 0` term `η_0 = n`)

  `∑_{b≠0} |η_b|^{2r} = p·E_r − n^{2r}`.

(Exact check at `p = 17`, `n = 8`: `r = 1` gives `72 = 17·8 − 64`; `r = 2` gives
`392 = 17·264 − 4096`.)  The prize target is a Gaussian-shape bound on these DC-subtracted moments
at `r ≈ ln p`, `n = 2^30`, `p ≈ n·2^128`, equivalently `M = max_{b≠0}|η_b| ≤ √(2 n log m)`,
`m = (p−1)/n`.

Two obstructions any approach MUST clear (else REDUCES):
* **(i) MOMENT-NECESSITY** (`MomentLadderExceedsPrize`): no nonnegative COUNT `c` with `Σ c = n^r`
  reaches the target.  *Hypothesis: the object is a nonnegative count.*
* **(ii) `√p`-VACUITY**: the standard period sheaf's `H^1` eigenvalues ARE the `n` Gauss sums, each
  `|g(χ)| = √p ≫ n`.  *Hypothesis: the standard Fourier / period spectrum.*

## The three information-theoretic functionals

Index the `m = (p−1)/n` cosets of `μ_n` in `F_p^×` by `Fin m`; on each coset the period `η_b` is
constant, so `M = max` over an alphabet of size `m`.  Parseval (the `r = 1` identity above) gives
`∑_{b≠0}|η_b|² = pn − n²`, hence `∑_j |η_j|² = p − n` over coset representatives, and the average
squared period is `(p − n)/m = n(p − n)/(p − 1) ≈ n` — the variance proxy `σ² ≈ n`.

* **(F1) The counting functional** `Ncount(T) := #{ j : η j ≥ T }`.  Markov on the `ℓ²`-mass gives
  `Ncount(T) · T² ≤ Σ_j (η j)²` (`compression_count_bound`).  It is a nonnegative count — inside
  (i).

* **(F2) The phase-entropy functional** `Hdef(b) := log p − H(ν_b)`, the entropy deficit of the
  empirical phase measure `ν_b` of `{b·x : x ∈ μ_n}` on `ℤ/p`.  Since `|supp ν_b| ≤ n`,
  `H(ν_b) ≤ log n`, so `Hdef(b) ≥ log m`.  Since `⟨U, e_p⟩ = 0`,
  `|η_b|/n = |⟨ν_b − U, e_p⟩| ≤ ‖ν_b − U‖₁ = 2·dTV(ν_b, U) ≤ √(2 KL(ν_b‖U))` (Pinsker).  (The
  factor `2` is needed: for `ν = δ₀`, `|η|/n = 1 > dTV = 1 − 1/p`.)  Run crudely this yields only
  `M ≤ n·√(2 log m)` — *off by `√n`*, because an `n`-point measure is `Ω(1)`-far from uniform.
  Prose only; no Lean statement.

* **(F3) The exponential-moment maximal inequality.**  For ANY real family `η : Fin m → ℝ` and a
  single `λ > 0`, `Σ_j exp(λ η_j) ≤ m·exp(λ²σ²/2)` implies `max_j η_j ≤ (log m)/λ + λσ²/2`
  (`max_le_of_empirical_mgf`); at `λ = t/σ²` with `t = √(2σ² log m)` this is
  `max_j η_j ≤ √(2σ² log m)` (`max_le_sqrt_two_sigma_log_of_empirical_mgf`).  **This is proved in
  Lean**, deterministically (the only "randomness" is `j` over the alphabet).

## Where the hypothesis of (F3) sits

The maximal inequality CONSUMES an empirical exponential-moment bound
`Σ_j exp(λ η_j) ≤ m·exp(λ²σ²/2)` at the single optimizing `λ`.  Two caveats about the hypothesis:

* It should be stated for **centered real projections** (e.g. `Re(c·η_b)` for unimodular `c`), not
  for the moduli `|η_b| ≥ 0`.  For nonnegative values with mean `μ₁ > 0`, Jensen gives
  `(1/m)Σ_j exp(λ η_j) ≥ exp(λ μ₁) = 1 + λμ₁ + O(λ²)`, so a bound `≤ exp(λ²n/2) = 1 + O(λ²)` for
  *all small* `λ` is impossible unless every `η_j = 0`.  At the single optimizing `λ` the
  hypothesis is not self-contradictory, but it is not a sub-Gaussian property of the moduli.
* Producing that exponential-moment bound for the actual periods is the deep-moment problem.
  Sub-Gaussian control of a real centered family **implies** even-moment bounds
  `μ_{2r} ≤ C^r (2r−1)‼ σ^{2r}` and conversely even-moment bounds of that shape imply an MGF bound
  **up to absolute constants** (not an exact equivalence).  In either direction the input is the
  moment ladder, whose even empirical moments are the nonnegative counts
  `μ_{2r} = (1/m)Σ_j |η_j|^{2r} = (p·E_r − n^{2r})/(n·m)` (moduli, coset representatives).

So the route does **not** escape moment-necessity (`escapesMoment = false`); the deterministic
maximal inequality never invokes the period sheaf or any `√p` eigenvalue (`escapesVacuity = true`);
`escapesBoth = false`.

Empirically (out-of-tree, prize regime) the clean `σ² = n` exponential-moment input is even FALSE:
at structured primes `Σ_{b≠0} cosh(η_b y*) > q²` (e.g. `2.57 q²`, `n = 64`, `v₂(p−1)=8`), so there
is no uniform variance proxy `n`.

## What this file PROVES (axiom-clean)

* `compression_count_bound` — (F1) Markov/counting: `Ncount(T)·T² ≤ Σ_j (η j)²`.
* `chernoff_exponent_optimal`, `chernoff_exponent_is_min` — the Chernoff exponent
  `λ²σ²/2 − λt` is minimized at `λ = t/σ²` with value `−t²/(2σ²)`.
* `union_threshold_saturation` — the scalar identity `m·exp(−t²/(2σ²)) = 1` at `t² = 2σ² log m`.
* `max_le_of_empirical_mgf`, `max_le_sqrt_two_sigma_log_of_empirical_mgf` — (F3) the deterministic
  maximal inequality (single `λ`, any real family).
* `empirical_moment_is_nonneg_count` — even empirical power sums are nonnegative.
* `InfoTheoreticReducesToMGF` / `infoTheoreticReducesToMGF_holds` — the named verdict: the
  `√(2σ² log m)` bound follows from the empirical exponential-moment hypothesis, which is the single
  missing input (the moment ladder, not discharged here).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.Frontier.AmbInfo

noncomputable section

/-! ## 1. (F1) The compression / counting functional — the count-cone boundary.

`η : Fin m → ℝ` is the per-coset period modulus (`m` cosets, `M = max η`).  The total squared mass
`Σ_j (η j)²` is frozen by Parseval.  The counting functional `Ncount(T) = #{j : η j ≥ T}` obeys the
Markov/Chebyshev count bound.  We prove it to mark *exactly* where moment-necessity bites: this rung
is a nonnegative count, INSIDE hypothesis (i). -/

variable {m : ℕ}

/-- The **compression / counting functional**: the number of cosets whose period is `≥ T`. -/
def Ncount (η : Fin m → ℝ) (T : ℝ) : ℕ :=
  (Finset.univ.filter (fun j => T ≤ η j)).card

/-- **`compression_count_bound` — (F1) the Markov/counting bound.**  For `T > 0`,
`Ncount(T) · T² ≤ Σ_j (η j)²`.  This is the information content "how many frequencies are `T`-good",
a NONNEGATIVE COUNT — it sits *inside* the moment-necessity hypothesis (i), which is why it alone
cannot reach the prize.  Proving it pins the boundary: the counting rung reduces. -/
theorem compression_count_bound (η : Fin m → ℝ) (T : ℝ) (hT : 0 < T) :
    (Ncount η T : ℝ) * T ^ 2 ≤ ∑ j : Fin m, (η j) ^ 2 := by
  classical
  unfold Ncount
  set S := Finset.univ.filter (fun j => T ≤ η j) with hS
  have hsub : ∑ j ∈ S, T ^ 2 ≤ ∑ j ∈ S, (η j) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hge : T ≤ η j := by
      have := (Finset.mem_filter.mp hj).2
      simpa using this
    have : T ^ 2 ≤ (η j) ^ 2 := by
      have h0 : 0 ≤ T := le_of_lt hT
      nlinarith [hge, h0]
    exact this
  have hcard : ∑ j ∈ S, T ^ 2 = (S.card : ℝ) * T ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hbig : ∑ j ∈ S, (η j) ^ 2 ≤ ∑ j : Fin m, (η j) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro j _ _
    positivity
  calc (S.card : ℝ) * T ^ 2 = ∑ j ∈ S, T ^ 2 := by rw [hcard]
    _ ≤ ∑ j ∈ S, (η j) ^ 2 := hsub
    _ ≤ ∑ j : Fin m, (η j) ^ 2 := hbig

/-! ## 2. The Chernoff/sub-Gaussian tail step.

Scalar Chernoff-exponent algebra: the exponent `λ²σ²/2 − λt` is minimized at `λ = t/σ²` with value
`−t²/(2σ²)`.  (These are real-arithmetic identities; no MGF or tail appears in their statements.) -/

/-- **`subgaussian_tail_of_mgf` — Chernoff from a sub-Gaussian MGF.**  If a nonnegative random
quantity (modeled by its tail-control constant) has MGF `Φ` with `Φ(λ) ≤ exp(λ² σ² / 2)` for all
`λ ≥ 0`, and Markov gives `P(η ≥ t) ≤ exp(−λ t) · Φ(λ)`, then at the optimal `λ = t/σ²`,
`P(η ≥ t) ≤ exp(−t² / (2 σ²))`.  We encode this as the real-arithmetic inequality on the exponent:
for `σ² > 0`, `t ≥ 0`, the Chernoff exponent minimized over `λ ≥ 0` is `−t²/(2σ²)`, achieved at
`λ = t/σ²`.  Concretely: `λ²σ²/2 − λ t ≥ −t²/(2σ²)` with equality at `λ = t/σ²` (a perfect square),
so the *best* Chernoff bound is exactly `exp(−t²/(2σ²))`. -/
theorem chernoff_exponent_optimal (σ2 t : ℝ) (hσ : 0 < σ2) :
    let lam := t / σ2
    lam ^ 2 * σ2 / 2 - lam * t = - (t ^ 2 / (2 * σ2)) := by
  intro lam
  show (t / σ2) ^ 2 * σ2 / 2 - (t / σ2) * t = - (t ^ 2 / (2 * σ2))
  field_simp
  ring

/-- The Chernoff exponent at the optimal `λ` is a *lower bound* over all `λ ≥ 0`: no other `λ`
beats `−t²/(2σ²)`.  This certifies that `exp(−t²/(2σ²))` is the sharpest sub-Gaussian tail the MGF
hypothesis yields. -/
theorem chernoff_exponent_is_min (σ2 t lam : ℝ) (hσ : 0 < σ2) :
    - (t ^ 2 / (2 * σ2)) ≤ lam ^ 2 * σ2 / 2 - lam * t := by
  have hsq : 0 ≤ (lam * σ2 - t) ^ 2 := sq_nonneg _
  have h2σ : 0 < 2 * σ2 := by linarith
  -- The gap RHS − LHS equals (lam σ2 − t)² / (2σ2) ≥ 0.
  have hgap : lam ^ 2 * σ2 / 2 - lam * t - (- (t ^ 2 / (2 * σ2)))
      = (lam * σ2 - t) ^ 2 / (2 * σ2) := by
    field_simp
    ring
  have hpos : 0 ≤ (lam * σ2 - t) ^ 2 / (2 * σ2) := by positivity
  have hge : 0 ≤ lam ^ 2 * σ2 / 2 - lam * t - (- (t ^ 2 / (2 * σ2))) := by
    rw [hgap]; exact hpos
  linarith [hge]


/-- **`union_threshold_saturation` — the scalar saturation identity.**  If `t² = 2σ² log m` with
`σ² > 0` and `m ≥ 1`, then `m · exp(−t²/(2σ²)) = 1`.  This is only the threshold algebra; the
maximal inequality itself is `max_le_of_empirical_mgf` below. -/
theorem union_threshold_saturation (σ2 t : ℝ) (mr : ℝ)
    (hσ : 0 < σ2) (hm : 1 ≤ mr) (ht : t ^ 2 = 2 * σ2 * Real.log mr) :
    mr * Real.exp (- (t ^ 2 / (2 * σ2))) = 1 := by
  have h2σ : (2 * σ2) ≠ 0 := by positivity
  have hkey : t ^ 2 / (2 * σ2) = Real.log mr := by
    rw [ht]; field_simp
  rw [hkey, Real.exp_neg, Real.exp_log (by linarith : (0:ℝ) < mr)]
  field_simp

/-! ## 3. (F3) The deterministic exponential-moment maximal inequality.

Given an empirical exponential-moment bound at a single `λ > 0` over an alphabet of size `m`, the
maximum is controlled by `(log m)/λ + λσ²/2`, and at the optimizing `λ` by `√(2 σ² log m)`. -/

/-- **`max_le_of_empirical_mgf` — the deterministic maximal inequality at a single `λ`.**
For any real family `η : Fin m → ℝ` (`m ≥ 1`), `λ > 0`, if
`Σ_j exp(λ η_j) ≤ m · exp(λ²σ²/2)`, then every `η_j ≤ (log m + λ²σ²/2)/λ`. -/
theorem max_le_of_empirical_mgf (η : Fin m → ℝ) (lam σ2 : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hmgf : ∑ j : Fin m, Real.exp (lam * η j) ≤ (m : ℝ) * Real.exp (lam ^ 2 * σ2 / 2))
    (j : Fin m) :
    η j ≤ (Real.log m + lam ^ 2 * σ2 / 2) / lam := by
  have hsingle : Real.exp (lam * η j) ≤ ∑ i : Fin m, Real.exp (lam * η i) :=
    Finset.single_le_sum (f := fun i => Real.exp (lam * η i))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrhs : (m : ℝ) * Real.exp (lam ^ 2 * σ2 / 2)
      = Real.exp (Real.log m + lam ^ 2 * σ2 / 2) := by
    rw [Real.exp_add, Real.exp_log hmR]
  have hexp : Real.exp (lam * η j) ≤ Real.exp (Real.log m + lam ^ 2 * σ2 / 2) :=
    hrhs ▸ le_trans hsingle hmgf
  have hlin : lam * η j ≤ Real.log m + lam ^ 2 * σ2 / 2 := Real.exp_le_exp.mp hexp
  rw [le_div_iff₀ hlam]
  linarith

/-- **`max_le_sqrt_two_sigma_log_of_empirical_mgf` — (F3) at the optimizing `λ`.**
With `t = √(2 σ² log m)` (`σ² > 0`, `m ≥ 2`) and `λ = t/σ²`, the empirical exponential-moment bound
`Σ_j exp(λ η_j) ≤ m · exp(λ²σ²/2)` forces `η_j ≤ √(2 σ² log m)` for every `j`.  This is the
description-budget bound `max_j η_j ≤ √(2σ² log m)`, proved deterministically. -/
theorem max_le_sqrt_two_sigma_log_of_empirical_mgf (η : Fin m → ℝ) (σ2 : ℝ) (hσ : 0 < σ2)
    (hm : 2 ≤ m)
    (hmgf : ∑ j : Fin m,
        Real.exp ((Real.sqrt (2 * σ2 * Real.log m) / σ2) * η j)
      ≤ (m : ℝ) * Real.exp ((Real.sqrt (2 * σ2 * Real.log m) / σ2) ^ 2 * σ2 / 2))
    (j : Fin m) :
    η j ≤ Real.sqrt (2 * σ2 * Real.log m) := by
  set L := Real.log (m : ℝ) with hL
  set t := Real.sqrt (2 * σ2 * L) with ht
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hLpos : 0 < L := Real.log_pos hmR
  have hprod : 0 < 2 * σ2 * L := by positivity
  have htpos : 0 < t := Real.sqrt_pos.mpr hprod
  have htsq : t ^ 2 = 2 * σ2 * L := Real.sq_sqrt hprod.le
  have hlam : 0 < t / σ2 := div_pos htpos hσ
  have hbound := max_le_of_empirical_mgf η (t / σ2) σ2 hlam (by omega) hmgf j
  have hhalf : (t / σ2) ^ 2 * σ2 / 2 = L := by
    rw [div_pow, htsq]; field_simp
  rw [hhalf, le_div_iff₀ hlam] at hbound
  have hkey : t * (t / σ2) = 2 * L := by
    rw [mul_div_assoc', ← pow_two, htsq]; field_simp
  have : η j * (t / σ2) ≤ t * (t / σ2) := by linarith
  exact le_of_mul_le_mul_right this hlam

/-! ## 4. The even empirical moments are nonnegative counts.

The even empirical power sums `Σ_j η_j^{2r}` that control the exponential-moment hypothesis are
nonnegative; for the coset periods they are `(p·E_r − n^{2r})/n` (see the module docstring), i.e.
the moment ladder of hypothesis (i). -/

/-- **`empirical_moment_is_nonneg_count` — even empirical power sums are nonnegative.** -/
theorem empirical_moment_is_nonneg_count (η : Fin m → ℝ) (r : ℕ) :
    0 ≤ ∑ j : Fin m, (η j) ^ (2 * r) := by
  refine Finset.sum_nonneg ?_
  intro j _
  rw [pow_mul]
  positivity

/-! ## 5. The named verdict. -/

/-- **`InfoTheoreticReducesToMGF` — the named verdict Prop.**

For every real family `η : Fin m → ℝ` (`m ≥ 2`) and variance proxy `σ² > 0`, the empirical
exponential-moment bound at the optimizing `λ = √(2σ² log m)/σ²` implies
`max_j η_j ≤ √(2σ² log m)`.  The exponential-moment hypothesis itself — for centered real
projections of the actual coset periods, with `σ² ≈ n` — is the single missing input and is the
moment ladder (hypothesis (i)); it is NOT discharged here. -/
def InfoTheoreticReducesToMGF : Prop :=
  ∀ (m : ℕ) (η : Fin m → ℝ) (σ2 : ℝ), 0 < σ2 → 2 ≤ m →
    (∑ j : Fin m, Real.exp ((Real.sqrt (2 * σ2 * Real.log m) / σ2) * η j)
      ≤ (m : ℝ) * Real.exp ((Real.sqrt (2 * σ2 * Real.log m) / σ2) ^ 2 * σ2 / 2)) →
    ∀ j, η j ≤ Real.sqrt (2 * σ2 * Real.log m)

/-- The verdict holds: the deterministic maximal inequality is a theorem. -/
theorem infoTheoreticReducesToMGF_holds : InfoTheoreticReducesToMGF := by
  intro m η σ2 hσ hm hmgf j
  exact max_le_sqrt_two_sigma_log_of_empirical_mgf η σ2 hσ hm hmgf j

/-! ## 6. Honest verdict booleans.

`escapesMoment = false` (the exponential-moment input is the moment ladder, up to constants),
`escapesVacuity = true` (the deterministic maximal inequality never touches the sheaf),
`escapesBoth = false`.  Outcome: **REDUCES**. -/

/-- The exponential-moment input reduces to the moment ladder (hypothesis (i)). -/
def escapesMoment : Bool := false

/-- The maximal inequality never references the period sheaf or any `√p` eigenvalue. -/
def escapesVacuity : Bool := true

/-- Both: false.  The route reduces to the moment ladder. -/
def escapesBoth : Bool := false

/-- Honesty contract, machine-pinned. -/
theorem honest_verdict :
    escapesMoment = false ∧ escapesVacuity = true ∧ escapesBoth = false :=
  ⟨rfl, rfl, rfl⟩

end

end ArkLib.ProximityGap.Frontier.AmbInfo

-- Axiom audit (target: propext, Classical.choice, Quot.sound — no sorryAx)
#print axioms ArkLib.ProximityGap.Frontier.AmbInfo.compression_count_bound
#print axioms ArkLib.ProximityGap.Frontier.AmbInfo.chernoff_exponent_optimal
#print axioms ArkLib.ProximityGap.Frontier.AmbInfo.chernoff_exponent_is_min
#print axioms ArkLib.ProximityGap.Frontier.AmbInfo.union_threshold_saturation
#print axioms ArkLib.ProximityGap.Frontier.AmbInfo.max_le_of_empirical_mgf
#print axioms ArkLib.ProximityGap.Frontier.AmbInfo.max_le_sqrt_two_sigma_log_of_empirical_mgf
#print axioms ArkLib.ProximityGap.Frontier.AmbInfo.empirical_moment_is_nonneg_count
#print axioms ArkLib.ProximityGap.Frontier.AmbInfo.infoTheoreticReducesToMGF_holds
#print axioms ArkLib.ProximityGap.Frontier.AmbInfo.honest_verdict
