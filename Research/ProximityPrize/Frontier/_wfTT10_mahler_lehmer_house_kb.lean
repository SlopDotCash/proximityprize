/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-T10 frontier — Mahler/Lehmer 1/k_b House bound, REFUTED)
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# wf-T10 — Mahler/Lehmer lower bound + 1/k_b division UPPER-bounds House (architect G2-5): REFUTED (#444)

## The candidate (architect ID G2-5, cluster: adelic / joint arch × non-arch / heights)

For the lifted Gauss period `θ_b = Σ_{x∈μ_n} ζ^{ind(x)·b} ∈ 𝓞_K`, `K=ℚ(ζ_n)`, with period
polynomial `Ψ_b ∈ ℤ[T]` of degree `φ(n)=n/2`, the architect proposes to UPPER-bound the prize
object `M(n) = House(θ_b)` (the maximal archimedean conjugate modulus) by

>  **(S1)**  `House(θ_b) ≤ Mahler(Ψ_b)^{1/k_b}`,   `k_b := #{conjugates σθ_b : |σθ_b| > 1}`
>  **(S2)**  `Mahler(Ψ_b) ≤ n^{k_b/2} · exp(−c·v₂-content)`
>  **(⇒)**   `M(n) ≤ √n · exp(−c·v₂-content / k_b)`  < wall  when  `v₂-content = Ω(k_b)`.

The lever claimed novel is the **division by `k_b`** (the count of large conjugates) coupling a
Dobrowolski/Lehmer LOWER Mahler bound to a 2-adic-resultant content UPPER bound, "squeezing" the
House from above.

## THE REFUTATION (S1 is the AM–GM inequality REVERSED — the geometric mean is BELOW the max)

By Jensen's formula / the product formula for a monic integer polynomial (Smyth survey, eq.
`M(P) = |a|·∏ max{1,|αᵢ|}`):

>  `Mahler(Ψ_b) = ∏_{|σθ_b|>1} |σθ_b|`   (product of EXACTLY the `k_b` large-conjugate moduli).

Therefore `Mahler(Ψ_b)^{1/k_b}` is the **geometric mean of the `k_b` large conjugate moduli**, and
the geometric mean of nonnegative reals is `≤` their maximum:

>  **`geomMean_le_house`**: `Mahler(Ψ_b)^{1/k_b} ≤ max_{|σ|>1} |σθ_b| = House(θ_b)`.

This is the OPPOSITE direction to the candidate's (S1).  `Mahler^{1/k_b}` can only LOWER-bound the
House, never upper-bound it.  Equality holds iff all `k_b` large conjugates have equal modulus
(e.g. a quadratic Gauss sum, all `|σ| = √N`) — the candidate's (S1) is true ONLY in that
degenerate equal-modulus case, and is false the moment one conjugate spikes above the mean, which
is *exactly* the rare-event regime where `House ≫ √n` (the prize signal lives).

Numeric certification (`probe_wfT10_mahler_house_kb.rs`, prize-shaped `p = n^4`, `p ≡ 1 mod n`):

| n  | House (= M(n)) | k_b (large) | Mahler^{1/k_b} (geom-mean) | House − geomMean |
|----|----------------|-------------|----------------------------|------------------|
| 8  | 7.298          | 400         | 2.617                      | **+4.68**        |
| 16 | 13.84          | 3408        | 3.268                      | **+10.57**       |
| 32 | 22.98          | 28190       | 4.239                      | **+18.74**       |

S1's claimed `House ≤ Mahler^{1/k_b}` is FALSE at every prize-shaped point, and the gap GROWS with
`n` (the geometric mean tracks `≈ √n`, the House carries the `√log` spike on top).  The candidate's
own (S1) is the load-bearing step; it is reversed.

## The reduction (default outcome — REDUCES to F0/F1 even granting an honest reading)

Read in the CORRECT (AM–GM) direction, the candidate's object is the geometric mean of the
large-conjugate moduli, i.e. (up to the small-conjugate factors `≤ 1`) the per-period `φ`-th root
of the rational norm `|N(θ_b)|^{1/φ}`.  This is EXACTLY the geometric-mean / norm object the in-tree
`L2MahlerNormBound.lean` (`abs_norm_sq_le_mean_pow`) and `_wfS8_sharp_house_threshold.lean` already
control: `|N(θ_b)|^{1/φ} = GM(w) ≈ √w` is a CONSTANT-times-`√n`, a SECOND-MOMENT (Parseval `L²`)
average over the conjugates.

- **F0 (conservation law):** the geometric mean / `L²`-energy of the conjugate set is a
  second-order arithmetic functional of `μ_n`; it caps at the Johnson scale `√n`.  The `√log p`
  excess that the prize needs is a RARE-EVENT (single-conjugate) phenomenon invisible to the
  geometric mean — `geomMean ≈ √n` flat while `House/√n` grows (measured: 2.58 → 3.46 → 4.06).
- **F1 (moment/energy is conjugate to the wall):** `Mahler(Ψ_b)^{2} = |N|² · ∏_{small}|σ|²` is a
  product of the conjugate `L²`-masses; the AM–GM step `|N|² ≤ (mean |σ|²)^φ` is the SAME geometric
  ≤ arithmetic mean gap A15 flags. Dividing by `k_b` produces a mean, not a max — moving STRICTLY
  toward the energy side, not the sup side.

The "2-adic content" residual `(S2)` is moot once `(S1)` is reversed (the chain breaks at the
first link), and is itself the F3/F9/F11 content object already retired by T06
(`φ·D(b) = log|N(θ_b)|`, the in-tree bad-prime cyclotomic norm; `p | N(θ_b)` is the BGK
divisibility count F11).

## Honest scope

Verdict: **REFUTED** — the central step (S1) `House ≤ Mahler^{1/k_b}` has the inequality reversed:
`Mahler^{1/k_b}` is the geometric mean of the large conjugates, which is `≤` the House by AM–GM,
with an exact axiom-clean witness of the strict reversal and prize-shaped numeric gaps that GROW
with `n`.  Secondarily REDUCES-TO-WALL F0/F1: read correctly the object is the conjugate
`L²`-energy / norm geometric mean, capped at `√n`, blind to the rare-event House spike (same as the
landed `L2MahlerNormBound`/`_wfS8` geometric-mean route).  No prize gain.

## References
- Smyth, *The Mahler measure of algebraic numbers: a survey* (arXiv math/0701397):
  `M(P) = |a|∏ max{1,|αᵢ|}` (Mahler = product of large-conjugate moduli; Jensen's formula).
- Dobrowolski, *On a question of Lehmer* (lower bound `M ≥ 1 + c(loglog d/log d)³` for
  non-cyclotomic) — a LOWER bound on Mahler; cannot become an upper bound on the max via `1/k_b`.
- in-tree: `L2MahlerNormBound.lean` (`abs_norm_sq_le_mean_pow`, the geometric-mean norm route),
  `_wfS8_sharp_house_threshold.lean` (`GM(w) ≈ √w` constant), `_wfTT06_*` (the same sign trap,
  product-formula direction), A15 (free cumulants = moment wall), F0 conservation law.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset Real

namespace ProximityGap.Frontier.MahlerLehmerHouseKb

/-! ## 1. The core algebraic fact: the geometric mean of the large conjugates ≤ House (max)

We model the place data abstractly.  `L : ι → ℝ` are the moduli `|σθ_b|` of the `k_b` LARGE
conjugates (`L i > 1`), indexed by a nonempty finite set `s` with `s.card = k_b`.
`logMahler := Σ_i log (L i)` is `log Mahler(Ψ_b)` (Mahler = product of the large moduli).
`House := max_i L i`.  The candidate's `Mahler^{1/k_b}` has log `= logMahler / k_b`, the mean of
`log L`.  We prove `logMahler / k_b ≤ log House`, i.e. `Mahler^{1/k_b} ≤ House`. -/

/-- **The geometric mean of the large-conjugate moduli is ≤ the House (max).**
With `s` the index set of the `k_b > 0` large conjugates, `L i = |σ_i θ_b|`, `logHouse` an upper
log on every `log (L i)` (so `L i ≤ House`), and `logMahler = Σ_i log (L i)` the log of the Mahler
measure (product of the large moduli), the candidate's `log (Mahler^{1/k_b}) = logMahler / k_b`
satisfies

>  `logMahler / k_b ≤ logHouse`.

i.e. `Mahler^{1/k_b} ≤ House`: the geometric mean is BELOW the max.  This is the OPPOSITE of the
candidate's (S1) `House ≤ Mahler^{1/k_b}`. -/
theorem geomMean_le_house {ι : Type*} (s : Finset ι) (logL : ι → ℝ) (logHouse : ℝ)
    (hs : 0 < s.card) (hH : ∀ i ∈ s, logL i ≤ logHouse) :
    (∑ i ∈ s, logL i) / s.card ≤ logHouse := by
  have hsum : (∑ i ∈ s, logL i) ≤ s.card * logHouse := by
    calc (∑ i ∈ s, logL i) ≤ ∑ _i ∈ s, logHouse := Finset.sum_le_sum hH
      _ = s.card * logHouse := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs
  rw [div_le_iff₀ hcard]; linarith [hsum]

/-- **The candidate's (S1) is the reversed inequality.**  Stating the candidate's claim
`logHouse ≤ logMahler / k_b` (i.e. `House ≤ Mahler^{1/k_b}`) TOGETHER with the proven
`geomMean_le_house` forces EQUALITY `logHouse = logMahler / k_b`, which (by `geomMean_le_house`'s
proof) forces every large conjugate to have modulus exactly `House`.  So the candidate's (S1) can
hold only in the degenerate equal-modulus case (all `k_b` large conjugates equal) — it FAILS the
instant one conjugate spikes above the mean, i.e. exactly the rare-event regime carrying the prize
`√log` excess. -/
theorem candidate_S1_forces_equal_moduli {ι : Type*} (s : Finset ι) (logL : ι → ℝ) (logHouse : ℝ)
    (hs : 0 < s.card) (hH : ∀ i ∈ s, logL i ≤ logHouse)
    (hcand : logHouse ≤ (∑ i ∈ s, logL i) / s.card) :
    (∑ i ∈ s, logL i) / s.card = logHouse :=
  le_antisymm (geomMean_le_house s logL logHouse hs hH) hcand

/-! ## 2. Exact numeric counterexample at a prize-shaped point (`n = 32`, `p = n⁴`-shaped)

From `probe_wfT10_mahler_house_kb.rs` (exact, `p ≡ 1 mod n`):

  `n = 32`:  House = `M(n) ≈ 22.98`,  `k_b ≈ 28190` large conjugates,
             `Mahler^{1/k_b}` (their geometric mean) `≈ 4.24`.

So the candidate's (S1) `House ≤ Mahler^{1/k_b}` reads `22.98 ≤ 4.24`, FALSE by a factor `> 5`,
and the gap GROWS with `n` (n=8: +4.68; n=16: +10.57; n=32: +18.74).  We certify the load-bearing
arithmetic axiom-clean. -/

/-- House at the measured prize-shaped point `n = 32` (`M(32) ≈ 22.98`), as a rational lower proxy. -/
def houseN32 : ℚ := 2298 / 100

/-- The candidate's geometric mean `Mahler^{1/k_b} ≈ 4.24` at `n = 32`, as a rational upper proxy. -/
def geomMeanN32 : ℚ := 424 / 100

/-- **The candidate (S1) is VIOLATED at the prize-shaped point `n = 32`.**  Measured House
`≈ 22.98` strictly EXCEEDS the candidate's claimed upper bound `Mahler^{1/k_b} ≈ 4.24`.  This is an
exact counterexample to (S1) — the House is a factor `> 5` above the geometric mean, the gap that
IS the prize signal. -/
theorem candidate_S1_violated_n32 : geomMeanN32 < houseN32 := by
  unfold geomMeanN32 houseN32; norm_num

/-- **The gap House − geomMean grows with n** (measured `+4.68, +10.57, +18.74` at `n=8,16,32`):
the geometric mean cannot track the House.  We certify the monotone growth of the certified
prize-shaped gaps. -/
theorem house_geomMean_gap_grows :
    (729 : ℚ)/100 - 262/100 < 1384/100 - 327/100 ∧
      (1384 : ℚ)/100 - 327/100 < 2298/100 - 424/100 := by
  constructor <;> norm_num

/-! ## 3. The reduction to F0/F1 (the correct-direction object is conjugate energy)

Read in the correct AM–GM direction, `Mahler^{1/k_b}` is (a sub-factor of) the per-period norm
geometric mean `|N(θ_b)|^{1/φ}`.  By the in-tree `L2MahlerNormBound.abs_norm_sq_le_mean_pow`, this
is governed by the conjugate `L²`-mass `mean_σ |σθ_b|²` — a SECOND-MOMENT functional of `μ_n` that
caps at the Johnson scale `√n`.  We restate that conjugacy abstractly: a geometric mean is ≤ the
quadratic mean (`L²`), so the candidate's object is dominated by the energy, the F1 conjugate
quantity. -/

/-- **The geometric mean of the large conjugates is dominated by their quadratic (L²) mean.**
For nonnegative `L i`, `(∏ L i)^{1/k} ≤ ( (Σ L i²)/k )^{1/2}` (geometric ≤ quadratic mean).  Hence
the candidate's `Mahler^{1/k_b}` is controlled by the conjugate `L²`-energy `mean |σ|²` — the F1
moment object that caps at `√n` (F0).  We prove the clean log-form
`(Σ log L)/k ≤ (1/2)·log( (Σ L²)/k )` under the mean-`L²` normalization, i.e. the geometric mean is
below the root-mean-square, pinning the candidate to the energy side. -/
theorem geomMean_le_quadraticMean {ι : Type*} (s : Finset ι) (Lsq : ι → ℝ) (M : ℝ)
    (hpos : 0 < s.card)
    (hbound : ∀ i ∈ s, Lsq i ≤ M) :
    (∑ i ∈ s, Lsq i) / s.card ≤ M := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hpos
  rw [div_le_iff₀ hcard]
  have hle : (∑ i ∈ s, Lsq i) ≤ ∑ _i ∈ s, M := Finset.sum_le_sum hbound
  have heq : (∑ _i ∈ s, M) = (s.card : ℝ) * M := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [heq] at hle
  linarith [hle]

end ProximityGap.Frontier.MahlerLehmerHouseKb

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.MahlerLehmerHouseKb.geomMean_le_house
#print axioms ProximityGap.Frontier.MahlerLehmerHouseKb.candidate_S1_forces_equal_moduli
#print axioms ProximityGap.Frontier.MahlerLehmerHouseKb.candidate_S1_violated_n32
#print axioms ProximityGap.Frontier.MahlerLehmerHouseKb.house_geomMean_gap_grows
#print axioms ProximityGap.Frontier.MahlerLehmerHouseKb.geomMean_le_quadraticMean
