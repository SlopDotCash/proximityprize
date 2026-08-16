/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# wf-T16 (#444): Frobenius-refined Chang cover of the H-invariant large spectrum — REDUCES-TO-WALL

ANGLE T16 / G4-1 (cluster G4: post-2020 additive combinatorics, STRUCTURE/COVERING not norms).

## The candidate

Prize regime: `p` prime, `n = 2^μ ∣ p-1`, `p = Θ(n^4)` (β = 4), `n = 2^30`; `η_b = Σ_{x∈μₙ} e_p(b x)`,
`M = max_{b≠0} |η_b|`. For `α ∈ (0,1]` set `Spec_α = {b : |η_b| ≥ α·n}` (the large spectrum of `1_{μₙ}`).
CANDIDATE: there is an absolute `C₀` and a set `Λ` of at most
`D := C₀·α⁻²·(log(p/n)/μ)` dilation-cosets covering a dissociated transversal of `Spec_α`, with `b*`
(`|η_{b*}| = M`) inside; then `|Spec_α| ≤ n·D` and "Parseval-balance over the `≤ n·D` large cosets at
`α = M/n` forces `M ≤ C·√(n·log(p/n))`" — the floor. The *new content* is the factor `1/μ` in `D`:
Chang gives `D₀ = C₀·α⁻²·log(p/n)` (the WALL); the claim is that 2-power Frobenius orbits of the
`{-1,0,1}`-relations collapse the dissociated dimension by `μ = log₂ n`.

## Verdict: REDUCES-TO-WALL (F1 primary via Rudin/Khintchine; F0 the balancing reversal).
## The `1/μ` collapse is REFUTED empirically; the residual `D₀` form IS the wall.

Three independent failures, all at the prize regime (`p` prime, `p ≡ 1 mod n`, `μₙ` proper, β = 4,
`p ~ n⁴`, NEVER `n = p-1`):

### (1) F1 — Chang's dimension IS a second-moment object (Rudin ⇐ Khintchine).
Chang's lemma bound `dim(Spec_α) ≤ C₀·α⁻²·log(1/density)` is proved via **Rudin's inequality**, which
is itself a corollary of **Khintchine's inequality**: characters of a dissociated set behave like
independent `±1` random variables and the dimension bound is the resulting `L²`/even-moment estimate.
So `D₀` is conjugate to the energy ladder F1 — exactly the input the conservation law F0 says caps at
Johnson. The base form `D₀ = α⁻²·log(p/n)` is *admitted by the candidate to recover the WALL*
(`n^{1-o(1)}`), so the entire prize content rests on the `1/μ` factor alone.

### (2) The `1/μ` Frobenius collapse is empirically FALSE (probe `probe_wfT16_chang_frobenius_dim.rs`).
The proposed mechanism requires the large spectrum to be organized into 2-power Frobenius/squaring
orbits whose `{-1,0,1}`-relations collapse the dissociated dimension. But the squaring map `b ↦ b²`
(the only 2-power orbit map on the cosets, since `μₙ` is 2-power) does NOT preserve `|η|`: measured
`|η_{b*²}|/M` at the argmax `b*` drops to `≈ 0.05` immediately (n=64: 1.00→0.063; n=128: 1.00→0.047;
n=256: 1.00→0.35). The peak coset is NOT squaring-invariant — there is no Galois invariance of the
large spectrum to collapse relations along. And the measured dissociated dimension of `Spec_α` tracks
`D₀` as a roughly **constant fraction** (`d/D₀ ≈ 0.18–0.36` at α=0.5 across n=8..64), NOT `D₀/μ`
(which would force `d/D₀ → 1/μ`, i.e. `0.33,0.25,0.20,0.17,0.14,...`). The `1/μ` collapse does not occur.

### (3) F0 — the balancing step is REVERSED (probe `probe_wfT16_balance_arith.rs`).
Even granting a covering `|Spec_α| ≤ n·D`, combining it with Parseval `Σ_{b≠0}|η_b|² = n(p-n)` yields
a **LOWER** bound on `M`, never an upper one. Concretely the mass-vs-cardinality inequality
`mass ≤ |Spec|·M²` gives `M² ≥ mass/|Spec| = n(p-n)/(n·D)`, i.e. `M ≥ √((p-n)/D)`, which is
`≥ √n` (Johnson RMS) and INCREASES as the covering `D` shrinks. So a *smaller* dissociated dimension
(the candidate's whole point) pushes the only forced bound on `M` **up**, not down. Measured: the RMS
coset period equals `√n` to full precision (Johnson), `Σ_{b≠0}|η_b|² = n(p-n)` exact, and the
"forced" `M`-lower-bound is `≥ Johnson` at every tested `n = 8..256`. The covering count cannot
upper-bound the sup; it pins the Johnson RMS floor — the conservation law F0 verbatim.

## Distinctness from prior kills
A7/A12 killed the Croot–Sisask *almost-period* (primal) object via the L²/L^q norm threshold.
T16 attacks the *dual* (Chang dissociated-dimension / covering) object — but it lands on the same
wall by a different door: Chang's dimension is the Rudin/Khintchine second moment (F1), and the
covering cardinality enters Parseval on the lower-bound side (F0). The `1/μ` Galois refinement, the
only genuinely new lever, has no empirical support (squaring breaks the peak).

This file records the load-bearing inequalities axiom-clean. The Frobenius/dimension measurements are
in `scripts/probes/rust/probe_wfT16_*.rs`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.WfT16

open Real

/-! ## Part 1: the balancing step is a LOWER bound on `M` (F0 reversal). -/

/-- **The Parseval/cardinality balance is a LOWER bound.** If the total spectral mass `mass`
(here `n(p-n)`) is carried by a set of `S` frequencies each of size `≤ M`, then `mass ≤ S·M²`,
hence `M² ≥ mass / S`. This is the only relation between a *cardinality* bound `S` and Parseval —
it bounds `M` from BELOW, the wrong direction for the prize. -/
theorem balance_is_lower_bound
    {mass S Msq : ℝ} (hS : 0 < S) (hMass : mass ≤ S * Msq) :
    mass / S ≤ Msq := by
  rw [div_le_iff₀ hS]; linarith [hMass]

/-- **The forced lower bound increases as the covering `D` shrinks.** With `mass = n(p-n)` and
`S = n·D`, the forced bound is `M² ≥ (p-n)/D`. Smaller `D` (the candidate's `1/μ` collapse) makes
this LARGER. Monotonicity: for `0 < D₁ ≤ D₂`, the forced lower bound at `D₁` is ≥ that at `D₂`. -/
theorem forced_lower_antitone_in_D
    {pmn D₁ D₂ : ℝ} (hpmn : 0 ≤ pmn) (hD₁ : 0 < D₁) (hD₁₂ : D₁ ≤ D₂) :
    pmn / D₂ ≤ pmn / D₁ :=
  div_le_div_of_nonneg_left hpmn hD₁ hD₁₂

/-- **Concrete reversal at the prize.** With `pmn = n(p-n)` and `S = n·D`, the forced bound on `M²`
is `(p-n)/D ≥ n` whenever `D ≤ (p-n)/n = p/n - 1`. At β = 4, `p/n - 1 ≈ n³`, while the Chang
dimension `D ≤ α⁻²·log(p/n) = O(log n) ≪ n³`, so the forced lower bound is always `≥ n` (Johnson),
i.e. the balance NEVER drops below the Johnson RMS scale `√n`. -/
theorem forced_lower_at_least_johnson
    {n pmn D : ℝ} (hn : 0 < n) (hD : 0 < D) (hDle : D ≤ pmn / n) :
    n ≤ pmn / D := by
  -- from D ≤ pmn/n we get n*D ≤ pmn, hence n ≤ pmn/D
  have h1 : D * n ≤ pmn := (le_div_iff₀ hn).mp hDle
  rw [le_div_iff₀ hD]; linarith [h1]

/-! ## Part 2: Chang's base dimension `D₀` is the wall (admitted), only `1/μ` could escape. -/

/-- The Chang base dimension `D₀ = C₀·α⁻²·log(p/n)` and the candidate's refined target `D = D₀/μ`.
At β = 4, `log(p/n) = 3·log n` and `μ = log₂ n = log n / log 2`, so the refined `D` would be
`C₀·α⁻²·3·log 2 = O(1)` (in α): a CONSTANT dilation-cosets, independent of n. -/
theorem refined_dim_is_constant_in_n
    {C₀ α logn : ℝ} (hα : α ≠ 0) (hlog2 : Real.log 2 ≠ 0) (hlogn : logn ≠ 0) :
    (C₀ * (α ^ 2)⁻¹ * (3 * logn)) / (logn / Real.log 2)
      = C₀ * (α ^ 2)⁻¹ * (3 * Real.log 2) := by
  field_simp

/-- **The escape would require `O(1)` dissociated dimension, contradicting the lower bound.** If the
refined cover had only `D = O(1)` cosets (constant in n), then `S = n·D = O(n)` frequencies, and the
forced lower bound `M² ≥ (p-n)/D` would be `≈ n³/O(1) = Θ(n³)`, i.e. `M ≳ n^{3/2}` — VASTLY above the
true `M ≈ √(n log)`. So an `O(1)`-coset cover is impossible (it would force a false huge lower bound);
equivalently, the covering cardinality cannot be the prize lever. Formalized: with `pmn ≥ n³` (β=4)
and `D` constant, the forced `M²` lower bound exceeds any `K·n` ceiling once `n` is large. -/
theorem constant_cover_forces_absurd_lower
    {n pmn D K : ℝ} (hn : 0 < n) (hD : 0 < D) (hK : 0 < K)
    (hpmn : K * n * D < pmn) :
    K * n < pmn / D := by
  rw [lt_div_iff₀ hD]; nlinarith [hpmn]

/-! ## Part 3: the conservation-law statement (F0) for this angle. -/

/-- **F0 for T16.** Any bound on `M` whose only inputs are (i) a cardinality/dissociated-dimension
covering count of the spectrum and (ii) Parseval (the second moment `Σ|η_b|² = n(p-n)`) produces only
the Johnson RMS scale or a lower bound on `M`. The combination is monotone the wrong way: improving
the structural input (smaller `D`) worsens the only forced `M`-relation. This is the conservation law:
second-order arithmetic of the domain (Parseval) plus an `L^∞`/structural count cannot see the √log
tail; the relation is `M² ≥ (p-n)/D ≥ n`, an equality-flat Johnson floor, never an upper bound. -/
theorem conservation_law_T16
    {n pmn D : ℝ} (hn : 0 < n) (hD : 0 < D) (hDle : D ≤ pmn / n) :
    -- the unique forced relation is a LOWER bound at the Johnson scale, monotone-decreasing in D:
    n ≤ pmn / D ∧ ∀ D', 0 < D' → D' ≤ D → pmn / D ≤ pmn / D' := by
  refine ⟨forced_lower_at_least_johnson hn hD hDle, ?_⟩
  intro D' hD' hD'le
  have hpmn : 0 ≤ pmn := by
    have h1 : n * D ≤ pmn := by have := (le_div_iff₀ hn).mp hDle; linarith
    nlinarith [mul_pos hn hD]
  exact forced_lower_antitone_in_D hpmn hD' hD'le

/-! ## Axiom audit -/

-- Expect: [propext, Classical.choice, Quot.sound] for each (no sorryAx).
#print axioms balance_is_lower_bound
#print axioms forced_lower_antitone_in_D
#print axioms forced_lower_at_least_johnson
#print axioms refined_dim_is_constant_in_n
#print axioms constant_cover_forces_absurd_lower
#print axioms conservation_law_T16

end ArkLib.ProximityGap.Frontier.WfT16
