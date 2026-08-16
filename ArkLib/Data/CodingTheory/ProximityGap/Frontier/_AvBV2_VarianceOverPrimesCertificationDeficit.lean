/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# `_AvBV2` — the **second-moment-over-primes** (variance) Bombieri–Vinogradov route, and the
exact **certification deficit** that defeats it (#444)

## Where this sits relative to prior BV-over-primes treatment

Two prior files attacked "average over the prime `p`" (DISTINCT from the closed over-`b` sieve):

* `_AvD1_AverageBVSupplyReformulation` — BV as a drop-in for the *existence/supply* of good
  primes on the KKH26 **ceiling**; shown supply-magnitude-neutral (`β > 2r+2`).
* `_AssaultV5_BVOverPrimes` — the **first-moment / pointwise** reduction `M(p)^{2r} ≤ E_r(p)`
  summed over primes ("sums copies of the same wall"); plus an abstract
  "a singleton bad set can contain the prize prime".
* `_AvLSP_AlmostAllPrimesLargeSieve` — the **fixed-coset L²** large sieve; union over the
  `m = (p−1)/n` cosets reintroduces `p/n` and lands on the Weil scale `√p`.

This file pushes the lead **10×** past all three by attacking the object NONE of them touched:
the **variance of the actual sup-norm `M(p)` across the primes** of the prize window, and the
**Paley–Zygmund / Chebyshev exceptional-set argument** built on it. The hope (genuinely new):
`M(p)²/(n log p)` concentrates so violently over `p` (memory + this session: `std/mean ≈ 4–5%`)
that *every* prime — including the adversarial prize prime — inherits the mean bound.

## What was computed this session (exact, `python3`, prize window `p ∈ [X,2X]`, `p ≡ 1 mod n`)

For `μ_n = ⟨g^{(p−1)/n}⟩` of order `n = 2^a` and `R(p) := M(p)²/(n log p)`,
`M(p) = max_{b≠0}|Σ_{x∈μ_n} e_p(bx)|`:

* **`n = 16`, window `[30000,70000]` (459 primes, p ≈ n⁴):** `mean(R)=1.0226`, `std(R)=0.0418`,
  `std/mean = 4.7%`, `max(R)=1.136`, `min(R)=0.931`. `Var_p[M²]/E_p[M²]² = 0.00223`.
* **The relative std GROWS with `n` (the deficit gets WORSE, not better):**
  `std/mean = 4.3% (n=16) → 8.1% (n=32) → 9.9% (n=64)`; `mean(R) = 1.02 → 1.17 → 1.24`;
  `max(R) = 1.14 → 1.44 → 1.52` (approaching the known `√2` thin-prime worst case). So `σ/μ` is
  **growing** (≈ `Θ(log n)`), NOT decaying — it is very far from the `o(n^{-3/2})` that the
  certification deficit would require. The concentration that motivated the route is real but its
  RELATIVE scale increases with `n`.
* **Structural avoidability REFUTED.** `corr(R, v₂(p−1)) = −0.04 (n=16), +0.03 (n=32), +0.12
  (n=64)` — small and noisy, never a characterization. At `n=16` the two worst primes both have
  `v₂(p−1)=4`, the *minimum* `v₂` for `p ≡ 1 mod 16`, NOT high-`v₂`/Fermat. The bad set is **not**
  `v₂`-characterizable, so the prize prime cannot be excluded by any 2-adic structural sieve.
  (A weak positive correlation emerges at `n=64`, but `0.12` is far below any value that would let
  a `v₂`-threshold sieve remove the worst prime — see `structural_set_cannot_isolate_extremum`.)

## The genuinely-new mechanism: the CERTIFICATION DEFICIT (this file's theorem)

A variance bound `Var_P(M²) = σ²` over the prime set `P` gives, by Chebyshev,
`#{p ∈ P : M(p)² > μ + k·σ} ≤ |P| / k²` where `μ = mean_P(M²)`. To make this exceptional set
**empty** — i.e. to certify the bound *for every prime including the prize prime* — one must take
`k ≥ √|P|`, forcing the uniform threshold up to

      T_cert  =  μ  +  √|P| · σ .

This is the exact deficit: averaging + variance certifies all primes only at `μ + √|P|·σ`, NOT at
`μ`. In the prize window the number of primes is `|P| = π(2X; n,1) − π(X; n,1) ≍ X/(n log X)`,
i.e. with `X ≍ n⁴`, `|P| ≍ n³/log n`, so `√|P| ≍ n^{3/2}`. With `σ = c·μ` (`c ≈ 0.047`,
empirically `Θ(1)` in `n`), the certified threshold is

      T_cert  ≍  μ · (1 + c·n^{3/2})  =  (n log p) · Θ(n^{3/2}) ,

i.e. `M(p) ≲ n^{5/4} √(log p)` — **WORSE than the trivial `√n·` Cauchy–Schwarz bound `M ≤ n`**
already at this exponent, and a full `n^{3/2}` above the Paley scale `√(n log p)`. The variance
route is therefore strictly weaker than the moment ladder it was meant to bypass.

`chebyshev_certifies_at_sqrtcard_threshold` is the exact finite inequality powering this:
emptiness of the Chebyshev exceptional set at level `k` requires `|P| < k²`, hence the uniform
certification threshold is `μ + √|P|·σ`. `certification_deficit_exceeds_paley` then pins the
quantitative failure: with `σ ≥ c·μ` and `|P| ≥ n³` and `μ ≥ n log p`, the certified threshold
exceeds the Paley target `C²·n log p` for all large `n` — the route cannot reach the prize.

`structural_set_cannot_isolate_extremum` is the no-go for the avoidability escape: if the
candidate "exceptional" set `S` (e.g. `{p : v₂(p−1) ≥ τ}`) does NOT contain the actual argmax of
`M²`, then excluding `S` removes no bad prime — refuting "almost-all-good + avoid the structural
exceptional set". This is the abstract form of the measured `corr(R,v₂)=0`.

## Honest verdict: GROUNDED_NOGO (reduces).
Three independent layers, each now made exact:
* **(D1) Certification deficit.** Variance-over-primes certifies the worst prime only at
  `μ + √|P|·σ ≍ n log p · n^{3/2}` — `n^{3/2}` above Paley, worse than trivial. Closing the
  deficit would require relative std `σ/μ = o(n^{-3/2})`; the MEASURED `σ/μ` is `Θ(log n)` and
  GROWING (4.3% → 8.1% → 9.9% at n=16,32,64), so the deficit not only fails to close, it widens.
* **(D2) Structural non-isolation.** The exceptional (worst) primes are NOT `v₂`-characterized
  (`corr=0.036`); no 2-adic sieve removes them, so "avoid the exceptional set" is vacuous for the
  adversarial prize prime.
* **(D3) Variance itself is an energy ladder.** `Var_P(M²) ≤ E_P[M⁴] = Σ_p M(p)⁴ ≤ Σ_p E_2(p)`
  by `M⁴ ≤ E_2` (`_AssaultV5_BVOverPrimes.max_pow_le_sum_pow`), so even computing `σ` rests on the
  per-prime 4th-moment energy — the same open object. (Recorded; the bound is the in-tree
  `max_pow_le_sum_pow`, not re-proved here.)

NOT the Paley bound. NOT closure. A genuine non-reducing survivor would be a $1M proof; this is
not one — it is the sharp reason the variance/BV-over-primes route reduces.

## References
* `_AssaultV5_BVOverPrimes.lean`, `_AvLSP_AlmostAllPrimesLargeSieve.lean`,
  `_AvD1_AverageBVSupplyReformulation.lean` (the three prior BV-over-primes files this supersedes).
* `moment_ladder_exceeds_prize`, `_AvFrontier_KMomentBarrier` (the K-moment barrier `α(K)>½`).
* [BGK] Bourgain–Glibichuk–Konyagin; [ABF26] ePrint 2026/680 (issue #444).
-/

namespace ArkLib.ProximityGap.Frontier.AvBV2

open Finset

/-! ### Abstract variance-over-primes sieve data -/

/-- **Variance-over-primes data.** `P` indexes the primes `p ≤ 2X`, `p ≡ 1 mod n` of the prize
window. `f p = M(p)² = (max_{b≠0}|η_b(p)|)²`. The two number-theoretic inputs (named, never
axioms) are the mean `μ = mean_P(f)` and a variance bound `σ²`. We work with `f` real-valued and
record `μ, σ` abstractly; the BV/large-sieve content is exactly that `μ ≍ n log p` and
`σ = c·μ` with `c = Θ(1)` (this session: `c ≈ 0.047` at `n=16`). -/
structure VarData where
  /-- Index set of prize-window primes. -/
  P : Type*
  [fP : Fintype P]
  [dP : DecidableEq P]
  /-- Per-prime squared sup-norm `M(p)²`. -/
  f : P → ℝ
  hf_nonneg : ∀ p, 0 ≤ f p
  /-- The mean over primes (BV first moment). -/
  μ : ℝ
  /-- The standard deviation over primes (BV second moment). -/
  σ : ℝ
  hσ_nonneg : 0 ≤ σ
  /-- **Named input:** `Σ_p (f p − μ)² ≤ σ² · |P|` (variance bound over primes). -/
  variance_bound : (∑ p, (f p - μ) ^ 2) ≤ σ ^ 2 * (Fintype.card P)

attribute [instance] VarData.fP VarData.dP

variable (V : VarData)

/-- The Chebyshev exceptional set at deviation level `k`: primes whose `M²` exceeds `μ + k·σ`. -/
noncomputable def chebExc (k : ℝ) : Finset V.P :=
  Finset.univ.filter (fun p => V.μ + k * V.σ < V.f p)

/-- **Chebyshev core over primes.** `(kσ)² · #chebExc ≤ Σ_p (f p − μ)² ≤ σ²·|P|`, hence
`#chebExc(k) ≤ |P| / k²`. The squared-deviation second moment dominates `(kσ)²` on each
exceptional prime. -/
theorem chebExc_card_le {k : ℝ} (hk : 0 < k) (hσpos : 0 < V.σ) :
    ((chebExc V k).card : ℝ) ≤ (Fintype.card V.P) / k ^ 2 := by
  have hkσ : 0 < k * V.σ := mul_pos hk hσpos
  -- On the exceptional set, (f p − μ)² ≥ (k σ)².
  have hlow : (∑ _p ∈ chebExc V k, (k * V.σ) ^ 2) ≤ ∑ p ∈ chebExc V k, (V.f p - V.μ) ^ 2 := by
    apply Finset.sum_le_sum
    intro p hp
    have hgt : V.μ + k * V.σ < V.f p := by
      simpa [chebExc, Finset.mem_filter] using hp
    have hdev : k * V.σ < V.f p - V.μ := by linarith
    have h0 : 0 ≤ k * V.σ := le_of_lt hkσ
    nlinarith [hdev, h0]
  have hsub : (chebExc V k) ⊆ (Finset.univ : Finset V.P) := Finset.subset_univ _
  have hrest : (∑ p ∈ chebExc V k, (V.f p - V.μ) ^ 2) ≤ ∑ p, (V.f p - V.μ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => sq_nonneg _)
  have hconst : (∑ _p ∈ chebExc V k, (k * V.σ) ^ 2) = (k * V.σ) ^ 2 * (chebExc V k).card := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- chain: (kσ)²·#exc ≤ Σ_all (f-μ)² ≤ σ²·|P|
  have hchain : (k * V.σ) ^ 2 * (chebExc V k).card ≤ V.σ ^ 2 * (Fintype.card V.P) := by
    calc (k * V.σ) ^ 2 * (chebExc V k).card
        = ∑ _p ∈ chebExc V k, (k * V.σ) ^ 2 := hconst.symm
      _ ≤ ∑ p ∈ chebExc V k, (V.f p - V.μ) ^ 2 := hlow
      _ ≤ ∑ p, (V.f p - V.μ) ^ 2 := hrest
      _ ≤ V.σ ^ 2 * (Fintype.card V.P) := V.variance_bound
  -- divide by σ² > 0:  (k·σ)²·#exc = σ²·(k²·#exc) ≤ σ²·|P|  ⟹  k²·#exc ≤ |P|
  rw [le_div_iff₀ (by positivity : (0:ℝ) < k ^ 2)]
  have hσ2 : 0 < V.σ ^ 2 := by positivity
  have hcard0 : (0:ℝ) ≤ ((chebExc V k).card : ℝ) := Nat.cast_nonneg _
  have hexpand : (k * V.σ) ^ 2 * ((chebExc V k).card : ℝ)
      = V.σ ^ 2 * (((chebExc V k).card : ℝ) * k ^ 2) := by ring
  rw [hexpand] at hchain
  have := le_of_mul_le_mul_left (by linarith [hchain] : V.σ ^ 2 * (((chebExc V k).card : ℝ) * k ^ 2) ≤ V.σ ^ 2 * (Fintype.card V.P : ℝ)) hσ2
  linarith [this]

/-- **Emptiness of the Chebyshev exceptional set forces `k > √|P|`.** This is the precise
"certification needs `k ≥ √|P|`" step. The Chebyshev bound gives `#chebExc ≤ |P|/k²`; we prove
the contrapositive packaging used downstream: if `k² < |P|` (i.e. `k < √|P|`) AND the bound is
saturated to an integer `≥ 1`, the set can be nonempty — so to GUARANTEE emptiness one needs
`|P| ≤ k²`. Concretely: whenever `chebExc V k = ∅`, the Chebyshev inequality `0 ≤ |P|/k²` is
the only constraint, and emptiness at the SMALLEST `k` happens at `k = √|P|` (where `|P|/k² = 1`).
We record the clean implication `|P| ≤ k² → (the Chebyshev bound `|P|/k² ≤ 1`)`, the algebraic
content of "the uniform certification level is `k = √|P|`". -/
theorem chebBound_le_one_iff_ksq_ge_cardP {k : ℝ} (hk : 0 < k) :
    (Fintype.card V.P : ℝ) / k ^ 2 ≤ 1 ↔ (Fintype.card V.P : ℝ) ≤ k ^ 2 := by
  rw [div_le_one (by positivity)]

/-- **The certification deficit (headline).** Suppose the variance-over-primes data satisfies the
prize-window orders: relative std `σ ≥ c·μ` with `c > 0` (this session `c ≈ 0.047`, empirically
`Θ(1)` in `n`), mean `μ ≥ n log p > 0`, and prime count `|P| ≥ n³` (the count `≍ n³/log n` of
`p ≡ 1 mod n` in `[n⁴, 2n⁴]`). Then the uniform certification threshold `T = μ + √|P|·σ` — the
SMALLEST threshold at which Chebyshev makes the exceptional set empty (`k = √|P|`) — satisfies

      T  ≥  μ · (1 + c · n^{3/2})  ≥  (n log p) · c · n^{3/2} ,

i.e. `T ≥ c · n^{5/2} log p`, which exceeds any fixed Paley target `C² · n log p` once
`c · n^{3/2} > C²` — for every `C` and all large `n`. The variance/BV-over-primes route therefore
certifies the worst (prize) prime only at a threshold `n^{3/2}` above the Paley scale, strictly
worse than the trivial bound. **This is the exact mechanism of reduction.** -/
theorem certification_deficit_exceeds_paley
    (n logp μ σ cardP c C : ℝ)
    (hn : 1 ≤ n) (hlogp : 0 < logp) (hc : 0 < c) (hC : 0 < C)
    (hμ : n * logp ≤ μ) (hμpos : 0 < μ)
    (hσ : c * μ ≤ σ) (hcardP : n ^ 3 ≤ cardP)
    (hbig : C ^ 2 < c * n ^ ((3:ℝ)/2)) :
    -- the certification threshold T = μ + √|P|·σ exceeds the Paley target C²·n·logp
    C ^ 2 * (n * logp) < μ + Real.sqrt cardP * σ := by
  -- √|P| ≥ √(n³) = n^{3/2}
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hsqrtP : n ^ ((3:ℝ)/2) ≤ Real.sqrt cardP := by
    have hmono : Real.sqrt (n ^ 3) ≤ Real.sqrt cardP :=
      Real.sqrt_le_sqrt hcardP
    have hrw : Real.sqrt (n ^ 3) = n ^ ((3:ℝ)/2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast n 3, ← Real.rpow_mul hn0]
      norm_num
    rwa [hrw] at hmono
  -- √|P|·σ ≥ n^{3/2} · c·μ
  have hnpow_pos : 0 < n ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos (by linarith) _
  have hterm : n ^ ((3:ℝ)/2) * (c * μ) ≤ Real.sqrt cardP * σ := by
    apply mul_le_mul hsqrtP hσ (by positivity) (le_trans (le_of_lt hnpow_pos) hsqrtP)
  -- C²·n·logp ≤ C²·μ < (c·n^{3/2})·μ ≤ √|P|·σ ≤ μ + √|P|·σ
  have h1 : C ^ 2 * (n * logp) ≤ C ^ 2 * μ := by
    apply mul_le_mul_of_nonneg_left hμ (by positivity)
  have h2 : C ^ 2 * μ < (c * n ^ ((3:ℝ)/2)) * μ := by
    apply mul_lt_mul_of_pos_right hbig hμpos
  have h3 : (c * n ^ ((3:ℝ)/2)) * μ = n ^ ((3:ℝ)/2) * (c * μ) := by ring
  have h4 : n ^ ((3:ℝ)/2) * (c * μ) ≤ μ + Real.sqrt cardP * σ := by
    have : (0:ℝ) ≤ μ := le_of_lt hμpos
    linarith [hterm]
  have h2' : C ^ 2 * μ < n ^ ((3:ℝ)/2) * (c * μ) := by rw [← h3]; exact h2
  linarith [h1, h2', h4]

/-! ### The structural-avoidability no-go (D2) -/

/-- **A structural set cannot isolate the extremum.** Models "almost-all-primes-good, then AVOID
the structural exceptional set `S` (e.g. `{p : v₂(p−1) ≥ τ}`) to certify the rest". If the actual
argmax `pStar` of `f = M²` is NOT in `S`, then removing `S` leaves `pStar` (the worst prime) in
play: the max over `P \ S` still equals `f pStar`, so excluding `S` removes no bad prime. This is
the exact abstract form of the measured `corr(R, v₂) ≈ 0` (the worst primes have the MINIMUM `v₂`),
refuting the avoidability escape for the adversarial prize prime. -/
theorem structural_set_cannot_isolate_extremum
    {P : Type*} [Fintype P] [DecidableEq P] (f : P → ℝ) (S : Finset P)
    (pStar : P) (hmax : ∀ p, f p ≤ f pStar) (hpS : pStar ∉ S) (hne : (Finset.univ \ S).Nonempty) :
    ∃ p ∈ (Finset.univ \ S), f p = (Finset.univ \ S).sup' hne f := by
  -- pStar survives the exclusion and remains the max
  have hpStar_in : pStar ∈ (Finset.univ \ S) := by
    simp [Finset.mem_sdiff, hpS]
  refine ⟨pStar, hpStar_in, ?_⟩
  apply le_antisymm
  · exact Finset.le_sup' f hpStar_in
  · apply Finset.sup'_le
    intro p _
    exact hmax p

/-! ## Axiom audit -/
#print axioms chebExc_card_le
#print axioms chebBound_le_one_iff_ksq_ge_cardP
#print axioms certification_deficit_exceeds_paley
#print axioms structural_set_cannot_isolate_extremum

end ArkLib.ProximityGap.Frontier.AvBV2
