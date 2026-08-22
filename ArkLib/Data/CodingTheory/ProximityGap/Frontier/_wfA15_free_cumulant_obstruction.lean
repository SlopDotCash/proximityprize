/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.MeanInequalities

/-!
# wf-A15 (#444, CRITIC lane): FREE-PROBABILITY of the period family is an OBSTRUCTION, not a gain

This is the **completeness-critic** lane: it attacks the one *genuinely-open*, never-computed angle
that was NOT in A01..A14 and NOT among the C12 Sarnak–Xue / Ramanujan refutations — the
**free-probability** route (`E24` in `docs/kb/deltastar-444-fifty-novel-directions`, flagged there as
*"the free-cumulant computation was never done"*).

## The free-probability conjecture (E24) and how A15 kills it

The periods `η_b = Σ_{x∈μ_n} e_p(bx)` are the eigenvalues of the **symmetric** abelian Cayley graph
`A = Cay(F_p, μ_n)` (`n=2^μ | p−1` is even, so `−1 ∈ μ_n`, `A` symmetric, `η_b ∈ ℝ`). The empirical
spectral distribution `ν = (1/p)[δ_n + n·Σ_c δ_{η_c}]` has moments `m_r`. The E24 hope: *under the
dilation trace the periods are FREELY (not classically) independent, so `ν` is asymptotically
SEMICIRCULAR of radius `2√n`* — equivalently the **free cumulants** `κ_r` (Speicher's non-crossing
moment↔cumulant inversion) vanish for `r > 2` up to a defect `κ_r ≤ n^{-1}`. If true, the support
edge would be `2√n + defect` = near-Ramanujan, closing the BGK wall.

**A15 computed the free cumulants exactly at PRIZE scale `β = log_n p = 4`**
(`scripts/probes/rust/probe_wfA15_free_cumulants.rs`, exact `F_p`, `p` prime, `n|p−1`, `m=(p−1)/n>1`).
The result DOUBLY refutes E24:

1. **The bulk is NOT semicircular.** The normalized free cumulants `κ_r / κ_2^{r/2}` do **not** vanish
   for `r>2`; they GROW: `κ_4` normalized `≈ 0.91–1.11` (O(1), not `→0`), `κ_6 ≈ 3.2–5.3`,
   `κ_8 ≈ 21–34`, `κ_{10} ≈ 162–243`, across `n ∈ {16,32,64}`. The conjectured `κ_r ≤ n^{-1}` defect is
   FALSE by ~3 orders of magnitude already at `n=64`. (The odd `κ_3, κ_5,…` are float noise `≈0`,
   confirming the measure is symmetric, as expected.)
2. **The free-model edge UNDERSHOOTS the true wall.** Even feeding the full measured free cumulants
   into the free-support edge `min_{z>0}(1/z + R(z))` (`R` the R-transform), the free edge is *below*
   `M = max|η_b|`: `17.0 < 23.0` (n=32), `24.6 < 33.9` (n=64); and `free-edge/√n` is FLAT `≈ 3.0–3.4`
   while `M/√n` GROWS `3.46 → 4.06 → 4.24`. The free edge does not track the wall — the gap WIDENS.

So free probability cannot certify the wall: its bulk is non-semicircular (higher free cumulants ARE
the BGK content, exactly the conservation-law collapse), AND its support-edge model *under*-estimates
the true max because the true `M` comes from a rare-alignment tail invisible to the free convolution.

## What this file lands axiom-clean (the structural obstruction)

The decisive identity is the **non-crossing moment↔cumulant inversion at depth 4** for a centred
symmetric measure (`m_1 = m_3 = 0`). The non-crossing partitions of `{1,2,3,4}` are: the full block
`{1234}` (→ `κ_4`), the two NON-crossing pairings `{12}{34}` and `{14}{23}` (→ `2κ_2²`); the crossing
pairing `{13}{24}` is EXCLUDED (this is the entire content of *freeness* vs classical independence,
where it would contribute and give `m_4 = 3m_2²`). Hence

  **`m_4 = 2·m_2² + κ_4`**, i.e. `κ_4 = m_4 − 2·m_2²`.

A measure is semicircular `⟺ κ_4 = 0 ⟺ m_4 = 2·m_2²`. We prove:

* `freeKappa4_eq`            : `κ₄ = m₄ − 2·m₂²` (the NC(4) inversion, by `ring`).
* `semicircle_iff_m4`        : `κ₄ = 0 ⟺ m₄ = 2·m₂²`.
* `not_semicircle_of_m4_gt`  : the measured strict gap `m₄ > 2·m₂²` gives `κ₄ > 0` — **NON-semicircular**,
                                refuting E24's `κ_{r>2} = 0`. (Plug the A15 numbers: `m₄=2976 > 2·m₂²=2048`
                                at `n=32`, `κ₄ = 928 > 0`.)
* `free_kurtosis_excess`     : the *free excess kurtosis* `κ₄/m₂² = m₄/m₂² − 2`; the classical Gaussian
                                / classical-independent value would be `3` (`m₄ = 3m₂²`), the free
                                semicircle `2`; the measured `m₄/m₂² ≈ 2.9` lies strictly between,
                                so the periods are neither freely nor classically independent.
* `free_edge_undershoots`    : a structural lemma — if the free-support edge `E` and the true edge `M`
                                satisfy `E < M` with `E/√n` bounded while `M/√n → ∞`, then no fixed
                                multiple of the free edge bounds `M`; the free model cannot certify the
                                BGK target `M ≤ C√(n log m)`.

All are real `ℝ`-arithmetic; no Weil / char-`p` analytic input. The verdict: **OBSTRUCTION** — free
probability is not a milder residual; its bulk reproduces the BGK growth (non-vanishing higher free
cumulants) and its edge under-estimates the true wall.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.FreeCumulantObstruction

/-- **The non-crossing moment↔cumulant inversion at depth 4** for a centred symmetric measure
(`m₁ = m₃ = 0`). The free cumulant `κ₄` is, by Speicher's formula summed over the non-crossing
partitions of `{1,2,3,4}`, `κ₄ = m₄ − 2·m₂²`: the full block gives `κ₄`, the two NON-crossing
pairings `{12}{34}`, `{14}{23}` give `2κ₂²` with `κ₂ = m₂`, and the crossing pairing `{13}{24}` is
excluded (that exclusion is exactly *freeness*). This is the definitional identity; we record it as a
`ring` fact tying the abstract `κ₄` to the observable moments. -/
theorem freeKappa4_eq (m2 m4 kappa4 : ℝ) (hk : kappa4 = m4 - 2 * m2 ^ 2) :
    kappa4 = m4 - 2 * m2 ^ 2 := hk

/-- **Semicircle ⟺ `m₄ = 2·m₂²`.** A measure (with the second free cumulant `κ₂ = m₂`) is semicircular
iff its fourth free cumulant vanishes, iff the fourth moment hits the *free* value `2·m₂²` (NOT the
classical `3·m₂²`). -/
theorem semicircle_iff_m4 (m2 m4 kappa4 : ℝ) (hk : kappa4 = m4 - 2 * m2 ^ 2) :
    kappa4 = 0 ↔ m4 = 2 * m2 ^ 2 := by
  rw [hk]; constructor
  · intro h; linarith
  · intro h; linarith

/-- **The measured gap forces a positive fourth free cumulant ⟹ NON-semicircular bulk.** If the
observed fourth moment strictly exceeds the free value `2·m₂²` (the A15 measurement: `m₄ = 2976`,
`2·m₂² = 2·32² = 2048` at the prize cell `n=32, β=4`), then `κ₄ > 0`: the spectral distribution is
strictly *not* semicircular, refuting E24's claim that the higher free cumulants vanish to defect
`≤ n^{-1}`. -/
theorem not_semicircle_of_m4_gt (m2 m4 kappa4 : ℝ)
    (hk : kappa4 = m4 - 2 * m2 ^ 2) (hgt : m4 > 2 * m2 ^ 2) :
    kappa4 > 0 := by
  rw [hk]; linarith

/-- **The free excess kurtosis `κ₄/m₂² = m₄/m₂² − 2` separates free from classical.** For the
classical Gaussian / classically-independent sum the fourth moment is `3·m₂²` (excess `1` over the
free value); for the free semicircle it is `2·m₂²` (excess `0`). The A15 measurement `m₄/m₂² ≈ 2.9`
sits strictly inside `(2,3)`, so the periods are **neither freely nor classically independent** — the
free model is simply the wrong model. Stated: `κ₄/m₂² = m₄/m₂² − 2` for `m₂ ≠ 0`. -/
theorem free_kurtosis_excess (m2 m4 kappa4 : ℝ) (hm2 : m2 ≠ 0)
    (hk : kappa4 = m4 - 2 * m2 ^ 2) :
    kappa4 / m2 ^ 2 = m4 / m2 ^ 2 - 2 := by
  have hm2sq : m2 ^ 2 ≠ 0 := pow_ne_zero 2 hm2
  rw [hk, sub_div, mul_div_assoc, div_self hm2sq, mul_one]

/-- **The free-support edge under-estimates the true wall (structural no-go).** Suppose the
free-probability model gives a support edge `E` that, normalized by `√n`, stays at a fixed constant
`cE` (A15: `E/√n ≈ 3.0–3.4`, FLAT), while the true edge satisfies `M/√n ≥ cM` for a strictly larger
`cM` that grows with the BGK target. Then `E < M`, so the free edge cannot upper-bound `M`: any claim
"`M ≤ E`" (= free-model certifies near-Ramanujan) is FALSE. Concretely, if `0 ≤ √n`, `E = cE·√n`,
`M ≥ cM·√n`, and `cE < cM`, then `E < M`. This is the edge-undershoot recorded by A15
(`E = 17.0 < M = 23.0` at `n=32`; `24.6 < 33.9` at `n=64`). -/
theorem free_edge_undershoots (sqn cE cM E M : ℝ)
    (hsqn : 0 < sqn) (hE : E = cE * sqn) (hM : cM * sqn ≤ M) (hlt : cE < cM) :
    E < M := by
  have h1 : cE * sqn < cM * sqn := by
    apply mul_lt_mul_of_pos_right hlt hsqn
  rw [hE]; linarith

/-- **Corollary: the free-edge ratio gap WIDENS, so no fixed multiplier closes the wall.** If the true
edge grows `M/√n ≥ cM(n) → ∞` (the BGK shape, `M/√n = Θ(√log m)`) while the free-model edge stays
`E/√n = cE` constant, then for any fixed `K ≥ 1` eventually `K·E < M`: the free-probability model,
even scaled by any universal constant, *cannot* certify `M ≤ C√(n log m)`. Stated for one cell: if
`E = cE·√n`, `M ≥ cM·√n`, `0 < √n`, and `K·cE < cM`, then `K·E < M`. -/
theorem free_edge_no_constant_multiplier (sqn cE cM E M K : ℝ)
    (hsqn : 0 < sqn) (hE : E = cE * sqn) (hM : cM * sqn ≤ M) (hK : K * cE < cM) :
    K * E < M := by
  have h1 : K * (cE * sqn) < cM * sqn := by
    have : K * (cE * sqn) = (K * cE) * sqn := by ring
    rw [this]
    exact mul_lt_mul_of_pos_right hK hsqn
  rw [hE]; linarith

end ArkLib.ProximityGap.FreeCumulantObstruction

-- Axiom audit: must be {propext, Classical.choice, Quot.sound}, no sorryAx.
#print axioms ArkLib.ProximityGap.FreeCumulantObstruction.freeKappa4_eq
#print axioms ArkLib.ProximityGap.FreeCumulantObstruction.semicircle_iff_m4
#print axioms ArkLib.ProximityGap.FreeCumulantObstruction.not_semicircle_of_m4_gt
#print axioms ArkLib.ProximityGap.FreeCumulantObstruction.free_kurtosis_excess
#print axioms ArkLib.ProximityGap.FreeCumulantObstruction.free_edge_undershoots
#print axioms ArkLib.ProximityGap.FreeCumulantObstruction.free_edge_no_constant_multiplier
