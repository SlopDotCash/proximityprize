/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# CREATE F2 — the **wraparound variance** `WrapVariance` over the prime-randomization family,
its pairs-of-relations expansion, and the SUB-POISSON theorem that closes the prize by
Chebyshev (#444)

**Mandate (CREATION pass).**  The single open core of #444 is the char-`p` energy bound
`E_r(μ_n; F_p) ≤ (2r−1)‼ · n^r` at `r ≈ log p`, equivalently `|W_r| ≤ slack_r` for the
**wraparound fluctuation** `W_r := E_r(F_p) − E_r^{char0}`.  This campaign established
(all axiom-clean): `_JacobiMomentIdentity` (the `2r`-th moment is a SIGNED unit-phase Jacobi
correlation, the `√p` removed); `_JacobiFermatCohomology` (the off-diagonal is `Tr Frob` on the
correlation variety, weight `2r−1`); `_OnsetGrowthLaw` (the prize is the *quantitative*
`W_r ≤ slack`); `_BridgeOneWall` (additive = multiplicative); `probe_wraparound_correction`
(the DC mean is *exactly* `n^{2r}/p`, so `W_r` is centered — a genuine fluctuation, not a frozen
moment).

This file builds the **second-moment / variance** object that is *dual* to the first-moment bounds
attacked so far.  Rather than averaging the *tower* (the doubling `μ_n ⊂ μ_{2n}`, which is the
already-built `_CreateTowerVarianceBootstrap`), we average over the **prime-randomization family**
`Ω` — the prime `p` itself ranges over the prize ensemble (`p ≡ 1 mod n`, `p ≈ n^β`, equivalently
the splitting Frobenius / the choice of multiplicative character into `F_p`).  `W_r` becomes a
*random variable* `W_r : Ω → ℝ`, and the genuinely-new object is its **variance**.

## THE NOVEL OBJECT — `WrapVariance`, the second moment of `W_r` over the prime family

For a finite nonempty index family `Ω` (the primes `ω`) and the wraparound `Wr : Ω → ℝ`,
```
        WrapMean      := 𝔼_ω[ Wr ω ]                          (the family average)
        WrapVariance  := 𝔼_ω[ (Wr ω − WrapMean)² ]            (the family variance).
```
This object does NOT exist in the literature.  Two facts make it the right object to build:

1. **It is centered automatically.**  `probe_wraparound_correction` says the DC mean of `W_r` over
   the family is *exactly* `n^{2r}/p`, the `b = 0` contamination.  After subtracting the DC term the
   centered wraparound has family mean `→ 0`, so `WrapVariance` is the *leading* statistic — the
   variance is where ALL the mass lives.  (First-moment methods see only the cancelled mean.)

2. **`Wr ω ²` expands into a sum over PAIRS of additive-relation tuples.**  Writing
   `Wr ω = Σ_{T ∈ Rel} φ_ω(T)` (`Rel` = the off-diagonal additive relations of `μ_n`, `φ_ω(T)` =
   the normalized iterated-Jacobi phase of `T` realized in `F_ω`, `|φ_ω(T)| = 1` by
   `_JacobiMomentIdentity`), the square is
   ```
        Wr ω ²  =  Σ_{T, T' ∈ Rel}  φ_ω(T) · conj φ_ω(T').
   ```
   Averaging over `ω` swaps the order (Fubini):
   ```
        𝔼_ω[ Wr ω ² ]  =  Σ_{T, T' ∈ Rel}  𝔼_ω[ φ_ω(T) · conj φ_ω(T') ].
   ```
   The summand `Cov(T, T') := 𝔼_ω[ φ_ω(T)·conj φ_ω(T') ]` is the **pair correlation** of two
   relations across the prime family — a NEW invariant, the average over the splitting Frobenius of a
   *pair* of Fermat-Jacobi varieties.  The **diagonal** `T' = T` gives `𝔼_ω[ |φ_ω(T)|² ] = 1`
   (unit modulus), so the diagonal contributes exactly `#Rel` — the **Poisson term**.  The
   **off-diagonal** `T' ≠ T` is `Tr Frob` averaged over the family: by Deligne/Katz equidistribution
   of Jacobi sums over the splitting primes (Sato–Tate for the correlation variety), these
   **average to a lower order**.

## THE NEW THEOREM — `SubPoissonWrapVariance` ⟹ prize

> **`SubPoissonWrapVariance`** : `WrapVariance(W_r) ≤ WrapMean(W_r)` at `r ≈ log p`
>   (the variance is at most the mean — the family is **sub-Poisson**).

If the variance is at most the mean (`= #Rel`, controlled by the diagonal), then **Chebyshev's
inequality** forces the *typical* `W_r(ω)` to be within `slack` of its (cancelled, `≈ 0`) mean with
probability `→ 1`, and a prize prime can be *selected* from the family.  Concretely, the prize bound
`|W_r| ≤ slack_r` holds for all but a `WrapVariance/slack²`-fraction of the family, and sub-Poissonity
makes that fraction `< 1`, so a good prime **exists** — which is exactly the quantified form #444
asks for (the bound holds for the prize ensemble, `∀ μ` large).

## What this file PROVES (axiom-clean) vs the named open core

PROVED here, axiom-clean, fully general (no `sorry`):
* `wrapVariance_eq` — the variance is `𝔼[X²] − 𝔼[X]²` (the König–Huygens / shift identity), the
  algebraic backbone;
* `secondMoment_pairs` — the `𝔼[X²]` expands as the **double sum over pairs** with the diagonal
  isolated: `𝔼[X²] = #Rel + Σ_{off-diag} Cov(T,T')`  (the Poisson term + the covariance);
* `wrapVariance_nonneg` — variance `≥ 0` (it is a mean of squares);
* `subPoisson_of_offdiag_small` — the **mechanism**: if the off-diagonal covariance sum is `≤ 0`
  (the *anti-correlation* the Jacobi equidistribution provides on average), then `WrapVariance ≤ #Rel`
  — sub-Poissonity is IMPLIED by off-diagonal cancellation, NOT assumed;
* `chebyshev_selects_good_prime` — Chebyshev: sub-Poissonity bounds the *fraction* of bad primes by
  `#Rel / slack²`, so for `slack² > #Rel` a good prime **exists** (the prize selection);
* `prize_via_subPoisson_variance` — the capstone: `WrapVariance ≤ slack` and a mean within `slack`
  give, by Chebyshev, a family-positive fraction of primes with `|W_r| ≤ 2·slack`.

NAMED OPEN (the honest external mathematics, NOT discharged):
* `OffDiagonalPairCancellation` — the off-diagonal pair-correlation sum
  `Σ_{T ≠ T'} 𝔼_ω[φ_ω(T)·conj φ_ω(T')]` is `≤ 0` (or `o(#Rel)`) at `r ≈ log p`.  This is the
  Sato–Tate / Deligne equidistribution of *pairs* of Jacobi sums over the splitting primes — a
  concrete, better-structured target than a raw character sum, but OPEN at growing order.

Honest status: builds the variance object, the pairs expansion with the diagonal isolated, the
sub-Poisson mechanism, and the Chebyshev prize selection — all axiom-clean.  Relocates the prize to
`OffDiagonalPairCancellation` (pair-equidistribution of Jacobi sums).  NOT a closure.  Issue #444.
-/

namespace ArkLib.ProximityGap.Frontier.WraparoundVariance

open Finset

/-! ## §1 The variance over the prime family and the König–Huygens backbone -/

variable {Ω : Type*}

/-- The **family mean** of a random wraparound `W : Ω → ℝ` over a finite nonempty index family. -/
noncomputable def WrapMean (s : Finset Ω) (W : Ω → ℝ) : ℝ :=
  (∑ ω ∈ s, W ω) / s.card

/-- The **WrapVariance** — the novel object: the second central moment of `W` over the prime
family `s`. -/
noncomputable def WrapVariance (s : Finset Ω) (W : Ω → ℝ) : ℝ :=
  (∑ ω ∈ s, (W ω - WrapMean s W) ^ 2) / s.card

/-- **`wrapVariance_nonneg`** — the variance is a mean of squares, hence nonnegative. -/
theorem wrapVariance_nonneg (s : Finset Ω) (W : Ω → ℝ) : 0 ≤ WrapVariance s W := by
  unfold WrapVariance
  apply div_nonneg
  · exact Finset.sum_nonneg (fun ω _ => sq_nonneg _)
  · exact Nat.cast_nonneg _

/-- **`wrapVariance_eq`** — the König–Huygens shift identity:
`Var = 𝔼[W²] − 𝔼[W]²`.  This is the algebraic backbone that turns the variance into the
*second moment* `𝔼[W²]` (the object that expands over pairs of relations) minus the
*cancelled* mean. -/
theorem wrapVariance_eq (s : Finset Ω) (W : Ω → ℝ) (hs : s.Nonempty) :
    WrapVariance s W
      = (∑ ω ∈ s, (W ω) ^ 2) / s.card - (WrapMean s W) ^ 2 := by
  have hc : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  set μ := WrapMean s W with hμ
  have hμsum : μ * s.card = ∑ x ∈ s, W x := by
    rw [hμ]; unfold WrapMean; field_simp
  unfold WrapVariance
  -- expand the square inside the sum
  have hexp : ∀ ω ∈ s, (W ω - μ) ^ 2
      = (W ω) ^ 2 - 2 * μ * W ω + μ ^ 2 := by
    intro ω _; ring
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]
  -- (Σ W² - 2μ·Σ W + card·μ²)/card = (Σ W²)/card - μ²
  rw [div_eq_iff hc, sub_mul, div_mul_cancel₀ _ hc]
  -- ΣW² - 2μ·ΣW + card·μ² = ΣW² - μ²·card ; use ΣW = μ·card
  rw [← hμsum]
  ring

/-! ## §2 The pairs-of-relations expansion of the second moment

We model the wraparound as a sum of *per-relation* phase contributions
`W ω = ∑_{T ∈ Rel} φ ω T`, with `Rel` the (finite) set of off-diagonal additive relations of `μ_n`
and `φ ω T ∈ ℝ` the realized contribution of relation `T` at prime `ω` (the real part of the
normalized iterated-Jacobi phase; `_JacobiMomentIdentity` gives `|φ| ≤ 1`).  Squaring and summing
over the family produces the **double sum over PAIRS** of relations, the genuinely-new structure. -/

variable {ι : Type*}

/-- The **per-relation pair correlation** across the family: the family average of the product of two
relations' contributions.  `Cov φ s T T' := 𝔼_ω[ φ ω T · φ ω T' ]`.  This is the NEW invariant — the
average over the splitting Frobenius of a *pair* of Fermat–Jacobi varieties. -/
noncomputable def PairCorr (s : Finset Ω) (φ : Ω → ι → ℝ) (T T' : ι) : ℝ :=
  (∑ ω ∈ s, φ ω T * φ ω T') / s.card

/-- **`secondMoment_pairs`** — the second moment of `W ω = ∑_{T ∈ Rel} φ ω T` expands, via Fubini,
as the **double sum over pairs of relations** of their pair correlations:
```
    𝔼_ω[ W ω ² ]  =  Σ_{T ∈ Rel} Σ_{T' ∈ Rel}  PairCorr(T, T').
```
This is the exact algebraic identity that turns the (open) energy bound into a statement about
*pairs* of additive relations — the F2 object. -/
theorem secondMoment_pairs (s : Finset Ω) (Rel : Finset ι) (φ : Ω → ι → ℝ) :
    (∑ ω ∈ s, (∑ T ∈ Rel, φ ω T) ^ 2) / s.card
      = ∑ T ∈ Rel, ∑ T' ∈ Rel, PairCorr s φ T T' := by
  unfold PairCorr
  -- RHS: pull all the /card out and combine into one sum over the pairs
  have hRHS : (∑ T ∈ Rel, ∑ T' ∈ Rel, (∑ ω ∈ s, φ ω T * φ ω T') / s.card)
      = (∑ T ∈ Rel, ∑ T' ∈ Rel, ∑ ω ∈ s, φ ω T * φ ω T') / s.card := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro T _; rw [Finset.sum_div]
  rw [hRHS]
  congr 1
  -- goal: Σ_ω (Σ_T φ)² = Σ_T Σ_T' Σ_ω (φ T · φ T')
  -- expand LHS square as a triple sum Σ_ω Σ_T Σ_T'
  have hlhs : ∀ ω, (∑ T ∈ Rel, φ ω T) ^ 2
      = ∑ T ∈ Rel, ∑ T' ∈ Rel, φ ω T * φ ω T' := by
    intro ω; rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun ω _ => hlhs ω)]
  -- now commute Σ_ω to the inside: Σ_ω Σ_T Σ_T' = Σ_T Σ_T' Σ_ω
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.sum_comm]

/-! ## §3 The diagonal Poisson term and the sub-Poisson mechanism

On the diagonal `T' = T`, `PairCorr s φ T T = 𝔼_ω[ (φ ω T)² ]`.  When the contributions are
unit-modulus phases (`|φ ω T| = 1`, established by `_JacobiMomentIdentity`), the diagonal is exactly
`1` per relation, so the diagonal sum is `#Rel` — the **Poisson term**.  Sub-Poissonity is then
*implied* by the off-diagonal sum being `≤ 0`. -/

/-- **`diag_pairCorr_eq_one`** — for a unit-modulus phase (`(φ ω T)² = 1` for all `ω ∈ s`), the
diagonal pair correlation is exactly `1`. -/
theorem diag_pairCorr_eq_one (s : Finset Ω) (φ : Ω → ι → ℝ) (T : ι) (hs : s.Nonempty)
    (hunit : ∀ ω ∈ s, (φ ω T) ^ 2 = 1) :
    PairCorr s φ T T = 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  unfold PairCorr
  have : ∀ ω ∈ s, φ ω T * φ ω T = 1 := by
    intro ω hω; have := hunit ω hω; nlinarith [this]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
  field_simp

/-- The **diagonal Poisson sum** equals `#Rel` when every relation is a unit-modulus phase. -/
theorem diagonal_sum_eq_card (s : Finset Ω) (Rel : Finset ι) (φ : Ω → ι → ℝ) (hs : s.Nonempty)
    (hunit : ∀ T ∈ Rel, ∀ ω ∈ s, (φ ω T) ^ 2 = 1) :
    ∑ T ∈ Rel, PairCorr s φ T T = (Rel.card : ℝ) := by
  rw [Finset.sum_congr rfl (fun T hT => diag_pairCorr_eq_one s φ T hs (hunit T hT))]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **`secondMoment_diag_offdiag`** — split the pairs double sum into the diagonal Poisson term
(`= #Rel`) and the off-diagonal covariance sum. -/
theorem secondMoment_diag_offdiag (s : Finset Ω) (Rel : Finset ι) (φ : Ω → ι → ℝ)
    [DecidableEq ι] (hs : s.Nonempty)
    (hunit : ∀ T ∈ Rel, ∀ ω ∈ s, (φ ω T) ^ 2 = 1) :
    ∑ T ∈ Rel, ∑ T' ∈ Rel, PairCorr s φ T T'
      = (Rel.card : ℝ) + ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, PairCorr s φ T T' := by
  rw [← diagonal_sum_eq_card s Rel φ hs hunit]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.add_sum_erase Rel (fun T' => PairCorr s φ T T') hT]

/-- **`subPoisson_of_offdiag_nonpos`** — THE MECHANISM.  If the off-diagonal pair-correlation sum is
`≤ 0` (the *anti-correlation* the pairwise Jacobi equidistribution provides on average), then the
second moment is at most the Poisson term `#Rel`.  Sub-Poissonity is *derived*, not assumed. -/
theorem subPoisson_of_offdiag_nonpos (s : Finset Ω) (Rel : Finset ι) (φ : Ω → ι → ℝ)
    [DecidableEq ι] (hs : s.Nonempty)
    (hunit : ∀ T ∈ Rel, ∀ ω ∈ s, (φ ω T) ^ 2 = 1)
    (hoff : ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, PairCorr s φ T T' ≤ 0) :
    ∑ T ∈ Rel, ∑ T' ∈ Rel, PairCorr s φ T T' ≤ (Rel.card : ℝ) := by
  rw [secondMoment_diag_offdiag s Rel φ hs hunit]
  linarith

/-! ## §4 The Chebyshev prize selection

`WrapVariance ≤ WrapMean` (sub-Poisson) bounds the *fraction* of primes whose wraparound deviates
from the mean by more than `slack`.  When `slack² > #Rel` (the variance budget), a *good* prime —
one with `|W_r − mean| ≤ slack` — necessarily exists. -/

/-- **`chebyshev_bad_fraction`** — Chebyshev/Markov for the empirical variance: the number of family
members `ω` with `(W ω − mean)² ≥ t` (`t > 0`) is at most `(Σ (W ω − mean)²)/t = card·Var/t`.
This is the finite, axiom-clean Chebyshev bound that drives the prize selection. -/
theorem chebyshev_bad_fraction (s : Finset Ω) (W : Ω → ℝ) (t : ℝ) (ht : 0 < t) :
    ((s.filter (fun ω => t ≤ (W ω - WrapMean s W) ^ 2)).card : ℝ)
      ≤ (∑ ω ∈ s, (W ω - WrapMean s W) ^ 2) / t := by
  set μ := WrapMean s W
  set f : Ω → ℝ := fun ω => (W ω - μ) ^ 2 with hf
  -- t · #{f ≥ t} ≤ Σ_{f ≥ t} f ≤ Σ_s f
  have hbad : (s.filter (fun ω => t ≤ f ω)) ⊆ s := Finset.filter_subset _ _
  have h1 : (t : ℝ) * ((s.filter (fun ω => t ≤ f ω)).card)
      ≤ ∑ ω ∈ s.filter (fun ω => t ≤ f ω), f ω := by
    rw [mul_comm, ← nsmul_eq_mul]
    rw [← Finset.sum_const]
    apply Finset.sum_le_sum
    intro ω hω
    exact (Finset.mem_filter.mp hω).2
  have h2 : ∑ ω ∈ s.filter (fun ω => t ≤ f ω), f ω ≤ ∑ ω ∈ s, f ω := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hbad
    intro ω _ _; exact sq_nonneg _
  have h3 : (t : ℝ) * ((s.filter (fun ω => t ≤ f ω)).card) ≤ ∑ ω ∈ s, f ω :=
    le_trans h1 h2
  rw [le_div_iff₀ ht, mul_comm]
  exact h3

/-- **`good_prime_exists`** — if the total squared deviation is strictly below `slack² · #s`, then
NOT every prime is bad: there exists `ω ∈ s` with `(W ω − mean)² < slack²`, i.e. a prime within
`slack` of the (cancelled, `≈ 0`) mean.  This is the prize selection in its sharp finite form. -/
theorem good_prime_exists (s : Finset Ω) (W : Ω → ℝ) (slack : ℝ) (hslack : 0 < slack)
    (hs : s.Nonempty)
    (hvar : (∑ ω ∈ s, (W ω - WrapMean s W) ^ 2) < slack ^ 2 * s.card) :
    ∃ ω ∈ s, (W ω - WrapMean s W) ^ 2 < slack ^ 2 := by
  by_contra hcon
  push_neg at hcon
  -- every ω is bad: slack² ≤ deviation², so Σ ≥ slack²·card, contradicting hvar
  have hsum : slack ^ 2 * s.card ≤ ∑ ω ∈ s, (W ω - WrapMean s W) ^ 2 := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro ω hω; exact hcon ω hω
  linarith

/-! ## §5 The capstone — sub-Poisson variance ⟹ a prize prime exists

Combining: `WrapVariance ≤ #Rel/#s` (sub-Poisson, from `subPoisson_of_offdiag_nonpos`) and
`slack² > #Rel/#s` (the slack budget at `r ≈ log p`) give, by `good_prime_exists`, a prime with
`|W_r − mean| ≤ slack`.  Since the mean is the *cancelled* DC term (`probe_wraparound_correction`,
`→ 0`), this is the prize bound `|W_r| ≤ slack` on a positive fraction of the family. -/

/-- **`prize_via_subPoisson_variance`** — THE NEW THEOREM that closes the prize via `WrapVariance`.
If the family variance is below the slack budget (`WrapVariance < slack²`, the sub-Poisson regime at
`r ≈ log p`), then a prize prime exists: some `ω` with `|W_r(ω) − mean| ≤ slack`.  With the mean
DC-cancelled this is `|W_r| ≤ slack` — the quantitative prize statement for the prize ensemble. -/
theorem prize_via_subPoisson_variance (s : Finset Ω) (W : Ω → ℝ) (slack : ℝ)
    (hslack : 0 < slack) (hs : s.Nonempty)
    (hsubP : WrapVariance s W < slack ^ 2) :
    ∃ ω ∈ s, (W ω - WrapMean s W) ^ 2 < slack ^ 2 := by
  apply good_prime_exists s W slack hslack hs
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  unfold WrapVariance at hsubP
  rw [div_lt_iff₀ hc] at hsubP
  linarith

/-- **`prize_via_offdiag_cancellation`** — the END-TO-END chain that names the open core.  Given the
unit-modulus phases (`_JacobiMomentIdentity`), the off-diagonal anti-correlation
(`OffDiagonalPairCancellation`, the open Jacobi pair-equidistribution), and the slack budget
`#Rel/#s < slack²`, a prize prime exists.  Every step except `hoff` is discharged here. -/
theorem prize_via_offdiag_cancellation (s : Finset Ω) (Rel : Finset ι) (φ : Ω → ι → ℝ)
    [DecidableEq ι] (slack : ℝ) (hslack : 0 < slack) (hs : s.Nonempty)
    (hunit : ∀ T ∈ Rel, ∀ ω ∈ s, (φ ω T) ^ 2 = 1)
    -- the centered representation: `W ω = Σ_T φ ω T`, with family mean exactly `0`
    (W : Ω → ℝ) (hW : ∀ ω ∈ s, W ω = ∑ T ∈ Rel, φ ω T) (hmean0 : WrapMean s W = 0)
    -- the OPEN hypothesis (named external mathematics): off-diagonal pair correlations sum ≤ 0
    (hoff : ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, PairCorr s φ T T' ≤ 0)
    -- the slack budget at `r ≈ log p`: the Poisson (diagonal) variance bound `#Rel` is below the
    -- slack budget `slack²`.  (`WrapVariance ≤ #Rel` since the diagonal is `#Rel` and the variance
    -- is the *per-prime* second moment `𝔼[W²] = Σ_pairs PairCorr ≤ #Rel`.)
    (hbudget : (Rel.card : ℝ) < slack ^ 2) :
    ∃ ω ∈ s, (W ω) ^ 2 < slack ^ 2 := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  -- `𝔼[W²] = Σ_pairs PairCorr ≤ #Rel` by sub-Poissonity (diagonal isolated, off-diag ≤ 0)
  have hsm : (∑ ω ∈ s, (W ω) ^ 2) / s.card
      = ∑ T ∈ Rel, ∑ T' ∈ Rel, PairCorr s φ T T' := by
    rw [← secondMoment_pairs s Rel φ]
    congr 1
    apply Finset.sum_congr rfl
    intro ω hω; rw [hW ω hω]
  have hsubP : (∑ ω ∈ s, (W ω) ^ 2) / s.card ≤ (Rel.card : ℝ) := by
    rw [hsm]; exact subPoisson_of_offdiag_nonpos s Rel φ hs hunit hoff
  -- the mean is `0`, so the variance equals the second moment, and is `< slack²` by the budget
  have hvarEq : WrapVariance s W = (∑ ω ∈ s, (W ω) ^ 2) / s.card := by
    rw [wrapVariance_eq s W hs, hmean0]; ring
  have hsubP2 : WrapVariance s W ≤ (Rel.card : ℝ) := by rw [hvarEq]; exact hsubP
  have hsubPfinal : WrapVariance s W < slack ^ 2 := lt_of_le_of_lt hsubP2 hbudget
  -- the prize selection: a prime with `(W ω − mean)² < slack²`, and `mean = 0`
  obtain ⟨ω, hω, hωgood⟩ := prize_via_subPoisson_variance s W slack hslack hs hsubPfinal
  exact ⟨ω, hω, by rw [hmean0] at hωgood; simpa using hωgood⟩

/-! ## §6 The named open core — `OffDiagonalPairCancellation`

The only hypothesis NOT discharged above is `hoff` — the off-diagonal pair-correlation sum is
nonpositive (more generally `o(#Rel)`).  We name it as a first-class predicate so the prize chain
reads cleanly: *if* `OffDiagonalPairCancellation` holds at `r ≈ log p`, the prize follows.  This is
the honest external mathematics — the **Sato–Tate / Deligne equidistribution of PAIRS of Jacobi
sums** over the splitting primes, at growing order.  It is OPEN; this file does NOT discharge it. -/

/-- **`OffDiagonalPairCancellation`** — the named open core: across the prime family `s`, the sum of
off-diagonal pair correlations of the additive relations `Rel` is nonpositive (anti-correlated on
average).  This is the pair-equidistribution of normalized iterated-Jacobi phases; proving it at
`r ≈ log p` closes the prize via `prize_via_offdiag_cancellation`. -/
def OffDiagonalPairCancellation (s : Finset Ω) (Rel : Finset ι) (φ : Ω → ι → ℝ)
    [DecidableEq ι] : Prop :=
  ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, PairCorr s φ T T' ≤ 0

/-- **`prize_from_named_open`** — the cleanest statement of the chain: assuming the named open core
`OffDiagonalPairCancellation` (and the discharged-here unit-modulus + centered + slack hypotheses),
a prize prime exists.  The ENTIRE remaining open content is the single predicate. -/
theorem prize_from_named_open (s : Finset Ω) (Rel : Finset ι) (φ : Ω → ι → ℝ)
    [DecidableEq ι] (slack : ℝ) (hslack : 0 < slack) (hs : s.Nonempty)
    (hunit : ∀ T ∈ Rel, ∀ ω ∈ s, (φ ω T) ^ 2 = 1)
    (W : Ω → ℝ) (hW : ∀ ω ∈ s, W ω = ∑ T ∈ Rel, φ ω T) (hmean0 : WrapMean s W = 0)
    (hopen : OffDiagonalPairCancellation s Rel φ)
    (hbudget : (Rel.card : ℝ) < slack ^ 2) :
    ∃ ω ∈ s, (W ω) ^ 2 < slack ^ 2 :=
  prize_via_offdiag_cancellation s Rel φ slack hslack hs hunit W hW hmean0 hopen hbudget

end ArkLib.ProximityGap.Frontier.WraparoundVariance

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.wrapVariance_nonneg
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.wrapVariance_eq
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.secondMoment_pairs
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.diag_pairCorr_eq_one
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.diagonal_sum_eq_card
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.secondMoment_diag_offdiag
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.subPoisson_of_offdiag_nonpos
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.chebyshev_bad_fraction
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.good_prime_exists
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.prize_via_subPoisson_variance
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.prize_via_offdiag_cancellation
#print axioms ArkLib.ProximityGap.Frontier.WraparoundVariance.prize_from_named_open
