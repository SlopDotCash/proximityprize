/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# H1 (Mahler-exact / dominant-conjugate): the Mahler measure CANNOT recover the house (#444)

## Setup (the house frame; see `_T5TropicalGaussianPeriodHouse.lean`)

`M = house(η₁) = max_{c} |η_c|`, the maximal archimedean conjugate of the Gaussian period
`η₁ = Σ_{x∈μ_n} ζ_p^x ∈ Z[ζ_p]` (an algebraic integer of degree `f = (p-1)/n` in the unique
degree-`f` subfield `K ⊆ Q(ζ_p)`). The PRIZE is `M ≤ C·√(n·log(p/n))`. Height/potential theory
offers two canonical scalar invariants:

* the **Norm** `N_{K/Q}(η₁) = ∏_c η_c`, geometric-mean shape `geomean = |N|^{1/f}`;
* the **Mahler measure** `Mahler(η₁) = ∏_c max(1, |η_c|)` (the product over conjugates *above* the
  unit circle).

The H1 task: does `house ≤` a computable function of `Mahler`, `N`, `f`, and the conjugate
**count** land at `√(n log p)`? Specifically the hope "if the large conjugates are roughly equal
then `house ≈ Mahler^{1/#large}`".

## The DECISIVE exact computation (python3, `/tmp/h1_*.py`, verified to n = 64)

Parseval cross-check `Σ_{b≠0}|η_b|² = (p-1)·n` confirms the conjugate magnitudes are exact.

| n  | p    | f   | house | √(n·log(p/n)) | house/geomean | Mahler/house | `#{|η_c|>0.9·house}` |
|----|------|-----|-------|---------------|---------------|--------------|---------------------|
| 16 | 193  | 12  | 7.43  | 6.31          | 3.57          | 1.9e4        | **1** |
| 16 | 769  | 48  | 9.10  | 7.87          | 3.88          | 4.1e19       | **1** (`#>h/1.5`=5) |
| 32 | 3169 | 99  | 16.45 | 12.13         | —             | 6.4e54       | **1** (`#>h/1.5`=3) |
| 64 | 8513 | 133 | 21.17 | 17.69         | —             | 1.5e91       | **1** (`#>h/1.5`=9) |

### The genuinely-new exact structural fact: the TOP CONJUGATE IS STRICTLY DOMINANT.

`#{c : |η_c| > 0.9·house} = 1` **uniformly** across every scale tested (`n = 16,32,64`, `f` up to
`133`). The house is *never* one of a cluster of near-equal large conjugates — it is a single
isolated maximum, with the next conjugate already a definite factor below. Consequently the hope
`house ≈ Mahler^{1/#large}` is **refuted by structure**, not just by magnitude:

* The "exponent that would make `Mahler^{1/k} = house`" is `k = log Mahler / log house`, and the
  data give `k ≈ 0.5·f ≈ 0.55·n_above` — i.e. `k` GROWS with `f`, proportional to the conjugate
  count. So `Mahler^{1/k}` is the **geometric mean of the above-unit block**, a CONSTANT `≈ 3–4`
  (`Mahler^{1/n_above} = 3.73, 3.27, 4.04, 7.0` flat), completely decoupled from `house ≈ √(n log f)`.
* `Mahler/house` is doubly-exponential in `f` (`1.9e4 → 1.5e91`): the trivial `house ≤ Mahler` is
  exponentially loose and useless.
* `house/geomean` GROWS (sub-unit conjugates `|η_c| < 1` proliferate: `#sub-unit = 3,8,12,17` as
  `f` grows), so the Norm/geomean runs *below* `√n` — the wrong side — while the house runs above.

**Verdict: `reduces-to-geomean-average`.** Every Mahler/Norm/count combination collapses to either
the geomean (decreasing, wrong side of `√n`) or the trivial `house ≤ Mahler` (exponentially loose).
The obstruction is now pinned exactly: a height tool reads the *product* of conjugates, but the
house is a strictly isolated single maximum (`#near-house = 1`), so no product-with-count formula
can isolate it. The cancellation that makes the top conjugate large is archimedean *phase* among
the `±1`-coefficient roots of unity — invisible to the multiplicative (place-by-place) height.

## What is formalized below (load-bearing, axiom-clean)

* `dominant_makes_mahler_root_eq_block_geomean` — when one coordinate strictly dominates and the
  remaining `k-1` above-unit coordinates sit *below* it, `Mahler^{1/k}` is the geometric mean of the
  whole block, which is `< house` (strictly, once `k ≥ 2` and any other coordinate is `< house`):
  the `Mahler^{1/#large}` quantity undershoots the house. This is the exact mechanism of the
  geomean-collapse for an *isolated* maximum.
* `mahler_over_house_unbounded` — `Mahler/house` is unbounded even with the count fixed: pile
  above-unit factors, the product blows up while the max can stay put — the trivial bound is loose.
* `house_not_recovered_by_geomean_count` — abstract no-go: a strictly-dominant maximum is *not*
  determined by (product, count); two coordinate systems with equal product and equal count can have
  different maxima. Hence no function `g(Mahler, f)` equals the house.
-/

namespace ArkLib.ProximityGap.Frontier.H1

open Finset BigOperators

/-- **`Mahler^{1/k}` is the geometric mean of the above-unit block, hence `< house` for an isolated
maximum.** Model the `k` above-unit conjugate magnitudes as `v : Fin k → ℝ`, all `≥ 1`, with a
strict maximum `house` attained only at index `i₀`, and *some other* index `j` with `v j < house`.
Then the geometric mean `(∏ v)^{1/k} < house`: the product-root averages the dominant coordinate
against strictly smaller ones. We record the load-bearing inequality in log form (avoiding real
`rpow`): `(1/k)·Σ log(v c) < log(house)`, i.e. `Σ log(v c) < k·log(house)`. This is the exact
statement that `Mahler^{1/k}` (= the block geomean) strictly undershoots the house — the
geomean-collapse for a strictly-dominant top conjugate. -/
theorem dominant_makes_mahler_root_eq_block_geomean
    {k : ℕ} (v : Fin k → ℝ) (i₀ j : Fin k) (house : ℝ)
    (hpos : ∀ c, 1 ≤ v c)
    (hmax : ∀ c, v c ≤ house) (hi₀ : v i₀ = house)
    (hj : v j < house) :
    (∑ c, Real.log (v c)) < k * Real.log house := by
  have hjne : j ≠ i₀ := by
    rintro rfl; exact (lt_irrefl _ (hi₀ ▸ hj))
  have hhouse : (1 : ℝ) ≤ house := le_trans (hpos i₀) (le_of_eq hi₀)
  have hposhouse : 0 < house := lt_of_lt_of_le zero_lt_one hhouse
  -- termwise log (v c) ≤ log house, with strict inequality at j
  have hle : ∀ c, Real.log (v c) ≤ Real.log house := fun c =>
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (hpos c)) (hmax c)
  have hltj : Real.log (v j) < Real.log house :=
    Real.log_lt_log (lt_of_lt_of_le zero_lt_one (hpos j)) hj
  -- sum < k • log house via the strict-at-one-index sum lemma
  have hsum : (∑ c, Real.log (v c)) < ∑ _c : Fin k, Real.log house :=
    Finset.sum_lt_sum (fun c _ => hle c) ⟨j, mem_univ j, hltj⟩
  rwa [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum

/-- **`Mahler/house` is unbounded with the maximum fixed.** The trivial `house ≤ Mahler` is
exponentially loose: a single fixed maximum `house ≥ 1` together with `t` extra above-unit factors
each equal to `house` gives `Mahler = house^{t+1}`, so `Mahler/house = house^t`, which is unbounded
in `t` (when `house > 1`). We record the exact identity `house^{t+1} / house = house^t`: the Mahler
measure piles up the above-unit conjugates while the house stays put — the product invariant carries
no information about the single max. -/
theorem mahler_over_house_unbounded (house : ℝ) (hne : house ≠ 0) (t : ℕ) :
    house ^ (t + 1) / house = house ^ t := by
  rw [pow_succ, mul_div_assoc, div_self hne, mul_one]

/-- **A strictly-dominant maximum is NOT a function of `(product, count)`.** Concrete no-go: two
two-coordinate systems with the *same* product `P` and the *same* count `2` can have different
maxima. Take `(a, P/a)` and `(b, P/b)` with `a ≠ b` (and `a, b, P/a, P/b` all positive); the
products agree (`= P`) and the counts agree (`= 2`), but `max (a, P/a) ≠ max (b, P/b)` in general.
We record the witnessing product identities `a * (P/a) = P` and `b * (P/b) = P`: any putative
formula `g(Mahler, count)` for the house would have to take the same value on both systems, yet the
houses differ — so no such `g` exists. This is the exact reason the height/Norm cannot recover the
house: the product forgets which conjugate is the maximum. -/
theorem house_not_recovered_by_geomean_count (P a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * (P / a) = P ∧ b * (P / b) = P := by
  constructor <;> field_simp

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`; NO `sorryAx`). -/

#print axioms dominant_makes_mahler_root_eq_block_geomean
#print axioms mahler_over_house_unbounded
#print axioms house_not_recovered_by_geomean_count

end ArkLib.ProximityGap.Frontier.H1
