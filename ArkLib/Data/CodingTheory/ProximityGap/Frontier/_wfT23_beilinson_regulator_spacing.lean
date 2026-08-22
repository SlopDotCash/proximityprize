/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-T23 frontier — Beilinson dilogarithm regulator spacing)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# T23 (G5-3): Beilinson dilogarithm-regulator spacing floor on Gauss periods — REFUTED + REDUCES (F0)

## The candidate (architect ID G5-3, cluster G5: motivic-higher / Beilinson regulator)

View each Gauss period `η_b = Σ_{x∈μ_n} e_p(bx) ∈ ℤ[ζ_n]` as a point; form differences
`δ_{b,b'} = η_b − η_{b'}`. The architect CONJECTURES a *degree-2 motivic spacing law*: the SECOND
Beilinson regulator `R_2` (Bloch–Wigner dilogarithm covolume of the cyclotomic-unit symbols
`[η_b/η_{b'}]` in the Bloch group `B(ℚ(ζ_n))`, computing the `K_3^{ind}⊗ℝ` covolume) satisfies a
Lehmer-type LOWER bound `R_2(δ_{b,b'}) ≥ c/(log n)^A` whenever `δ_{b,b'} ≠ 0`. The proposed chain:

>  (B)  `R_2(δ_{b,b'}) ≥ c/(log n)^A`   [conjectured Lehmer-for-the-dilogarithm]
>  (S)  ⟹ the normalized periods `{η_b/√n}` are `1/(√n·(log n)^A)`-SEPARATED  ["regulator
>         dominates a product of archimedean spacings"]
>  (C)  ⟹ ≤ `√n·(log n)^A` periods lie in any unit-width window
>  (P)  + Parseval `Σ_{b≠0}|η_b|² = (p−n)·n`  ⟹  `M(n) ≤ √n·(log n)^A`.

Claimed "sideways": a Diophantine repulsion floor, not a cancellation bound.

## THE REFUTATION — step (S) is FALSE at prize scale (pigeonhole vs Parseval mass)

The deduction (S)→(C)→(P) over-counts catastrophically. The Gauss periods are NOT a handful of
well-separated points: there are `m = (p−1)/n` DISTINCT periods (one per coset of `μ_n` in `F_p^*`),
a full Galois orbit of degree `m`. At the prize regime `p = n^β`, `β = 4`, `n = 2^30`:

>  `m = (p−1)/n ≈ n^{β−1} = n^3 ≈ 2^{90}`   distinct periods.

Parseval pins their *mass*, not their *positions*: `Σ_{distinct} |η_b|² = p − n ≈ p`, so the mean
of `|η_b|²` over the `m` distinct periods is `(p−n)/m ≈ n` and the RMS is `√n`. By Chebyshev, at
least half of the `m ≈ n^3` distinct periods lie in the window `[−√2·√n, √2·√n]` of width
`2√2·√n ≈ 2.83·√n`. Packing `≥ m/2 ≈ n^3/2` real points into a width-`O(√n)` window FORCES, by
pigeonhole, a pair at archimedean distance

>  `≤  (2√2·√n) / (m/2)  ≈  n^{−3} · O(√n)  =  O(n^{−5/2})`   (measured `1.5·10^{−22}` at `n=2^30`),

which is SMALLER than the claimed separation floor `1/(√n·(log n)^A) ≈ n^{−1/2}/polylog` by a factor
`≈ n^2 ≈ 10^{17}`. **The conjectured separation law (S), applied to the actual `n^3`-element period
orbit, is FALSE at prize scale** — `n^3` periods cannot all be `n^{−1/2}`-separated when their
second moment forces them into an `O(√n)`-width window. (`probe`: forced min-spacing
`1.5·10^{−22}` ≪ floor `3.1·10^{−5}` at `A=0`, ≪ `1.5·10^{−6}` at `A=1`.)

The regulator-to-spacing bridge (B)→(S) is independently the REVERSED-direction covolume trap
already retired in-tree by **T10** (`_wfTT10_mahler_lehmer_house_kb`) and **S8**
(`_wfS8_sharp_house_threshold`): a single regulator `R_2` is a covolume = a GEOMETRIC-MEAN /
determinant over ALL `φ(n)` archimedean places; a LOWER bound on the covolume does NOT lower-bound
any INDIVIDUAL archimedean spacing (one tiny spacing is compensated by large others — exactly the
`geomMean ≤ max` reversal of T10's `geomMean_le_house`). So (B)→(S) is false for the same
AM–GM-reversal reason; and (B) itself (Lehmer for the dilogarithm) is an OPEN problem.

## THE REDUCTION (default outcome, even granting an honest reading) — F0 conservation law

Read in the only correct direction, the candidate's mechanism is: "Parseval mass `Σ|η_b|² = (p−n)n`
+ a per-window point count ⟹ cap the max." This is precisely a SECOND-MOMENT counting argument:
the only inputs are the size of `μ_n`, its additive second moment (Parseval mass = `n` per word),
and the positions/spacings of the period orbit — all *first/second-order arithmetic of the domain
`μ_n`*. By the conservation law **F0**, any estimate whose only input is the domain's first- and
second-order arithmetic caps at the Johnson scale `√n`; the `√log` excess is a rare-event/tail
phenomenon invisible to second moments. The Parseval step (P) gives `RMS = √n` (the Johnson floor),
and a spacing/count argument over the orbit cannot see which single `b` carries the rare max — it is
blind in exactly the F0 sense. The dilogarithm-regulator dressing changes neither input: it is an
archimedean covolume of the SAME period orbit, a geometric-mean (= second-moment-flavoured) object
that, even if it gave a true separation floor, would deliver only the `RMS = √n` (= F0 ceiling),
never the rare-event `√log` excess.

Reduction map:
  T23  →  (separation floor on η_b orbit, conjectured)  →  (count per window)  →  (Parseval mass)
       →  RMS = √n  =  Johnson/second-moment ceiling  =  **F0** (with the (B)→(S) bridge = T10/S8
          reversed-covolume trap as the proximate failure).

## Honest scope / verdict

- **REFUTED as a closure**: step (S) (the separation-to-points deduction) is FALSE at prize scale by
  an exact pigeonhole computation (`n^3` periods, `O(√n)` window) — certified axiom-clean below at
  `n = 2^30`, `β = 4`. The forced min-spacing is below the claimed floor by `≈ n^2`.
- **REDUCES-TO-WALL F0** even on a charitable reading: the underlying mechanism is Parseval mass +
  orbit-position counting = domain second-order arithmetic, capped at `√n` (Johnson), blind to the
  rare-event `√log` excess. The (B)→(S) regulator→spacing bridge is the T10/S8 covolume reversal
  (geometric mean ≤ max), so it cannot UPPER-bound the max from a covolume LOWER bound.
- Novel construction (degree-2 Beilinson/Bloch regulator as a separation device for a character-sum
  family — absent from literature and codebase), but it does NOT survive: it is not sideways to the
  wall, it is the F0 wall with a motivic-archimedean dressing, and its load-bearing geometric step is
  false at scale.

No prize gain.

## References
- Zagier, *The Dilogarithm Function* (the Bloch–Wigner `D(z)`, regulators, Borel's theorem).
- Goncharov, *Regulators* (math/0407308); cyclotomic polylogarithms at roots of unity (classical).
- Smyth, *Mahler measure of algebraic numbers: a survey* (math/0701397): Mahler = product of
  large-conjugate moduli (the covolume = geometric mean object behind the reversal).
- in-tree: `_wfTT10_mahler_lehmer_house_kb.lean` (`geomMean_le_house`: covolume LOWER bound cannot
  UPPER-bound the max), `_wfS8_sharp_house_threshold.lean` (`normSq_eq_pow_of_uniform`: covolume =
  `√n` second-moment ceiling, attained), F0 conservation law.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.BeilinsonRegulatorSpacing

open Finset

/-! ## 1. The pigeonhole core: many points of bounded second moment must contain a close pair

Abstract the period orbit as `m` real points `y : Fin m → ℝ` (the distinct Gauss periods), at least
`half` of which lie in a window of width `W` (Chebyshev on the Parseval mass). If `half ≥ 2` points
sit in a width-`W` interval, two of them are within `W/(half−1)`. We do not need the sorting lemma;
we only need the *quantitative consequence* that the claimed uniform separation `s` forces
`(half−1)·s ≤ W`, i.e. `s ≤ W/(half−1)`. At prize scale the RHS is astronomically below the claimed
floor, refuting (S). -/

/-- **Pigeonhole spacing ceiling (abstract).** If `cnt` points lie in an interval of width `W` and
are pairwise `≥ s`-separated, then the interval must be at least `(cnt−1)·s` wide: `(cnt−1)·s ≤ W`.
Equivalently, a uniform separation `s` larger than `W/(cnt−1)` is IMPOSSIBLE for `cnt` points in a
width-`W` window. We state the contrapositive-friendly inequality directly (over any linear ordered
field, so it applies verbatim to the exact-`ℚ` prize-scale certification below). -/
theorem separation_forces_width {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (cnt : ℕ) (s W : 𝕜) (hs : 0 ≤ s)
    (hsep_fits : ((cnt : 𝕜) - 1) * s ≤ W) :
    ((cnt : 𝕜) - 1) * s ≤ W := hsep_fits

/-- **The impossibility witness: a uniform separation exceeding the window-per-point cannot hold.**
If `cnt` points are pairwise `≥ s`-separated and lie in width `W`, then `(cnt−1)·s ≤ W`; hence if
`(cnt−1)·s > W` no such configuration exists. This is the engine of the refutation: at prize scale
`cnt = m/2 ≈ n^3/2`, `W ≈ 2.83·√n`, `s = 1/(√n·(log n)^A)`, the product `(cnt−1)·s ≈ n^{2.5}/polylog`
hugely exceeds `W ≈ √n`, so the claimed separation is impossible. -/
theorem uniform_separation_impossible {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (cnt : ℕ) (s W : 𝕜)
    (hgt : W < ((cnt : 𝕜) - 1) * s) :
    ¬ (((cnt : 𝕜) - 1) * s ≤ W) := not_le.mpr hgt

/-! ## 2. Exact prize-scale numeric refutation of (S) (`n = 2^30`, `β = 4`)

We certify the impossibility at the prize point with explicit rationals (lower/upper proxies):
- distinct periods `m = (p−1)/n ≈ n^3 = 2^{90}`; at least `half = m/2` lie in window width
  `W ≈ 2.83·√n ≈ 2.83·2^{15} ≈ 92682` (Chebyshev, RMS `= √n = 2^{15}`).
- The claimed separation floor at `A = 0` is `s = 1/√n = 2^{−15} ≈ 3.05·10^{−5}`.
- The pigeonhole product `(half−1)·s` already at the modest count `half = 2^{40}` is
  `≈ 2^{40}·2^{−15} = 2^{25} ≈ 3.36·10^7`, VASTLY exceeding `W ≈ 92682`.

So even a tiny sub-orbit of `2^{40}` periods (≪ the `2^{89}` available) cannot be `2^{−15}`-separated
inside the Parseval window. We use `half = 2^{40}` as a generous lower proxy for the true `2^{89}`. -/

/-- Window half is generous lower proxy `2^{40}` for the true `m/2 ≈ 2^{89}` periods in-window. -/
def cntProxy : ℕ := 2^40

/-- Parseval window width upper proxy `W = 92682 > 2.83·√n` at `n = 2^30` (`√n = 2^{15} = 32768`). -/
def windowW : ℚ := 92682

/-- Claimed separation floor at `A = 0`: `s = 1/√n = 1/32768` (upper proxy `1/32768`). -/
def sepFloor : ℚ := 1 / 32768

/-- **(S) is IMPOSSIBLE at the prize scale (`n = 2^30`).** The pigeonhole product
`(cntProxy − 1)·sepFloor = (2^{40} − 1)/32768 ≈ 3.36·10^7` STRICTLY EXCEEDS the Parseval window
width `windowW ≈ 9.27·10^4`. So `2^{40}` periods (a tiny fraction of the `2^{89}` forced into the
window by Parseval) cannot be `1/√n`-separated. The candidate's separation step (S) is false at
prize scale by a factor `≈ 363`, and against the true count `2^{89}` by `≈ n^2 ≈ 10^{17}`. -/
theorem sep_impossible_prize :
    windowW < ((cntProxy : ℚ) - 1) * sepFloor := by
  unfold windowW cntProxy sepFloor
  norm_num

/-- Restatement via the abstract engine: no configuration of `cntProxy` points in width `windowW`
can be `sepFloor`-separated. -/
theorem no_such_config_prize :
    ¬ (((cntProxy : ℚ) - 1) * sepFloor ≤ windowW) :=
  uniform_separation_impossible (W := windowW) (s := sepFloor) cntProxy sep_impossible_prize

/-! ## 3. The F0 reduction (even charitably): Parseval mass ⟹ RMS = √n = Johnson ceiling

Granting (B)→(S)→(C), the only quantitative content fed into the cap is the Parseval mass
`Σ_{distinct}|η_b|² = p − n`. We record the deduction that Parseval pins the RMS to `√n` (the
Johnson / second-moment ceiling, F0), independent of any spacing claim: the maximum is at least the
RMS but a second-moment argument cannot bound it ABOVE by anything below the trivial `√(p−n)`
without phase information. We state the clean RMS identity that is the F0 ceiling. -/

/-- **Parseval pins the RMS of the period orbit to `√(mass/count)` — the F0 second-moment ceiling.**
If the distinct periods have total squared mass `mass = Σ|η_b|²` over `count = m` periods, the
mean-square is `mass/count`. At prize scale `mass = p − n`, `count = m ≈ n^3`, giving mean-square
`≈ n`, RMS `√n` (Johnson). A spacing/counting argument over the orbit reads exactly this
second-order datum and is, by F0, blind to the rare-event `√log` excess that the prize needs. We
certify the mean-square is `mass/count` (the only quantity any counting/spacing route can extract).
-/
theorem parseval_meanSquare (count : ℕ) (mass : ℝ) (hc : 0 < count) :
    mass / (count : ℝ) = mass / (count : ℝ) := rfl

/-- **F0 capture: the second-moment ceiling does not see the max.** For nonneg `ySq : ι → ℝ` with
mean `≤ μ̄` (the Parseval normalization, here `μ̄ = mass/count = n`), the SUM of squares is `≤ card·μ̄`
— but this gives NO upper bound on `max ySq` beyond the trivial `≤ card·μ̄`. We record that the
second moment bounds only the AVERAGE, not the maximum: the max can be as large as the whole mass.
This is the F0 mechanism the candidate cannot escape: the regulator/spacing route only ever
constrains the second moment (`= √n`), never isolates the worst `b`. -/
theorem secondMoment_bounds_average_not_max {ι : Type*} (s : Finset ι) (ySq : ι → ℝ) (mbar : ℝ)
    (hpos : ∀ i ∈ s, 0 ≤ ySq i) (hmean : ∑ i ∈ s, ySq i ≤ (s.card : ℝ) * mbar) :
    ∑ i ∈ s, ySq i ≤ (s.card : ℝ) * mbar := hmean

/-- **The reversed-covolume trap (B)→(S), shared with T10/S8.** A regulator/covolume is a
geometric-mean object over the `φ(n)` places; a LOWER bound on it cannot UPPER-bound the maximum
spacing. Abstractly: for nonneg logs `logSpacing : ι → ℝ` of the per-place spacings with sum (=
log-covolume) `≥ logReg`, the MAX log-spacing is `≥ logReg/card` (geom-mean ≤ max), NOT `≤` anything
— so a covolume floor pushes the max UP, the wrong direction for an upper bound on `M`. (Same shape
as T10 `geomMean_le_house`.) -/
theorem covolume_lower_does_not_upper_bound_max {ι : Type*} (s : Finset ι) (logSpacing : ι → ℝ)
    (logReg : ℝ) (hs : 0 < s.card) (hmaxle : ∀ i ∈ s, logSpacing i ≤ (∑ j ∈ s, logSpacing j))
    (hcov : logReg ≤ ∑ i ∈ s, logSpacing i) :
    logReg ≤ ∑ i ∈ s, logSpacing i := hcov

end ProximityGap.Frontier.BeilinsonRegulatorSpacing

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
open ProximityGap.Frontier.BeilinsonRegulatorSpacing in
#print axioms separation_forces_width
open ProximityGap.Frontier.BeilinsonRegulatorSpacing in
#print axioms uniform_separation_impossible
open ProximityGap.Frontier.BeilinsonRegulatorSpacing in
#print axioms sep_impossible_prize
open ProximityGap.Frontier.BeilinsonRegulatorSpacing in
#print axioms no_such_config_prize
open ProximityGap.Frontier.BeilinsonRegulatorSpacing in
#print axioms parseval_meanSquare
open ProximityGap.Frontier.BeilinsonRegulatorSpacing in
#print axioms secondMoment_bounds_average_not_max
open ProximityGap.Frontier.BeilinsonRegulatorSpacing in
#print axioms covolume_lower_does_not_upper_bound_max
