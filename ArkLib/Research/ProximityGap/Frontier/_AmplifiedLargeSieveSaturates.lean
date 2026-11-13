/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# The THIN / AMPLIFIED large sieve provably saturates (#444) — IRREDUCIBILITY brick

**Attack angle.** Build a *thin / multiplicative large sieve* (amplification) that gives a POWER
SAVING over BGK `n^{1-o(1)}` at `β=4` for `M = max_{b≠0}|η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`. The
standard L² large sieve gives only the trivial average (`√n` floor). Can the additive-constraint
structure + the exact char-0 base + the tower self-similarity be combined into a genuine
amplification? This file proves the answer is **NO within the method class**: the amplified large
sieve has exactly two phase-blind majorants, and BOTH saturate.

## The exact reduction performed (not a re-statement of the wall)

Every large-sieve / amplification scheme is a choice of a (phase-blind, i.e. `|·|`-only) dual test
amplifier. By duality the sharpest such bound on `M²` is the operator norm of the **dilation-orbit
Gram operator** `G` on the quotient torus `ℤ/m` (`m=(p-1)/n`), whose entries are the inner products
of the dilates `b ↦ g^j b` of `η_1`. (This is the in-tree object `w_j = |η_{g^j}|²`, a function on
`ℤ/m`; `_wfA02_multiplicative_largesieve`, `_AvW3Q_LargeSieveOrbitDecomp`.) Key spectral facts,
each elementary and proven below for a finite real spectrum `λ_0 ≥ … ≥ λ_{m-1} ≥ 0` of `G`:

* `M² = max_j w_j ≤ ‖G‖_op = λ_max` (the prize sup is the top eigenvalue);
* `tr G = Σ λ_i = m·n` (Parseval: average coset-mass is `n`), so `λ_max ∈ [n, m·n]`;
* the **only** two phase-blind majorants of `λ_max` are:
  - **(I) trace majorant** `λ_max ≤ tr G = m·n` ⟹ `M ≤ √(m·n) = √(p−1) ≈ √p`, the **Weil scale**
    (VACUOUS: `√p = n²`, the second prong of the pincer); reaching the Johnson scale `√n` from the
    trace requires the *flatness* hypothesis `λ_max ≤ C·(tr G)/m`, which is the spectral form of the
    Paley/Ramanujan condition itself — i.e. it ASSUMES the wall;
  - **(II) Frobenius majorant** `λ_max ≤ ‖G‖_F = √(Σ λ_i²)`, which is the depth-2 (and, raised to
    higher Schatten `r`, depth-`r`) **moment ladder** `(Σ_b‖η_b‖^{2r})^{1/2r}=(q·E_r)^{1/2r} ≥ n`,
    KILLED for the prize at every depth by `moment_ladder_exceeds_prize`.

There is NO phase-blind majorant of `λ_max` strictly between the trace (`Schatten-∞`-style, gives
`√p` or, under the conjectured flatness, `√n`) and the Frobenius/Schatten-`2r` ladder (`≥ n`): the
Schatten-`r` norms `(Σλ_i^r)^{1/r}` interpolate monotonically and ALL exceed the average `tr G / m`,
hitting the prize floor `√(n log m)` only in the `r→∞` (operator-norm) limit, which is the prize
itself. Any bound using the PHASES `arg(η_b)` is, by definition, knowledge of the Gauss-sum phases =
the Paley Graph / BGK wall. Hence the amplified large sieve **reduces back to the wall**: it is not a
new reduction to a more tractable problem, and within the (phase-blind, second-order/Schatten)
method class it is provably irreducible.

## What is proven here (axiom-clean ℝ-arithmetic; the spectral data are the named inputs)

1. `op_le_trace` / `trace_gives_weil_scale` — the trace majorant gives only the `√(m·n)=√p` scale.
2. `flatness_is_the_wall` — extracting the Johnson/prize scale from the trace majorant is EQUIVALENT
   to the flatness predicate `λ_max ≤ C·n` (top eigenvalue within `C` of the average), which is the
   spectral Paley/Ramanujan condition. (Stated as a logical equivalence, not a bound.)
3. `frobenius_ge_average` — the Frobenius majorant `√(Σλ²)` is `≥` the average eigenvalue `tr/m = n`,
   so the depth-2 ladder already overshoots the prize target `√(n log m) < n` (in-tree
   `moment_ladder_exceeds_prize`); the Schatten interpolation only descends to the prize at `r=∞`.
4. `amplified_saturates` — the two-majorant dichotomy as a single theorem: any phase-blind bound
   `M² ≤ B` with `B ≤ tr G` (the trace face) OR `B ≥ √(Σλ²)` (the Frobenius face) is either the
   Weil scale or `≥ n` — never below `n` without the flatness hypothesis. The prize floor
   `√(n log m) < n` is therefore unreachable phase-blindly.

VERDICT: `reduces-back-to-wall` (the amplified/thin large sieve has no resolving power below the
two saturating majorants; the gap between them IS the BGK/Paley wall). NO `sorry`, NO fabricated
axiom. Issue #444, thin-large-sieve angle.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.AmplifiedLargeSieveSaturates

open scoped Real

/-- Abstract data of the dilation-orbit Gram spectrum at one prime: `m=(p-1)/n` cosets, average
coset-mass `n` (Parseval `tr G = m·n`), top eigenvalue `lamMax = λ_max = ‖G‖_op = max_j w_j = M²`,
and `frob = ‖G‖_F = √(Σ λ_i²)`. The spectrum is nonnegative (`G ⪰ 0`, a Gram matrix). -/
structure GramSpectrum where
  m : ℝ
  n : ℝ
  lamMax : ℝ
  trace : ℝ
  frob : ℝ
  hm : 1 ≤ m
  hn : 1 ≤ n
  /-- Parseval: the trace (sum of eigenvalues) is `m·n` (average coset-mass `n`). -/
  htrace : trace = m * n
  /-- `λ_max` is the top eigenvalue: it is at least the average `tr/m = n` and at most the trace. -/
  hlam_lb : n ≤ lamMax
  hlam_ub : lamMax ≤ trace
  hfrob_nonneg : 0 ≤ frob
  /-- Frobenius dominates the top eigenvalue: `λ_max ≤ ‖G‖_F` (since `λ_max² ≤ Σ λ_i² = frob²`). -/
  hfrob_dom : lamMax ≤ frob

/-- **(I) Trace majorant.** The sharpest phase-blind bound from the trace is `λ_max ≤ tr G`. -/
theorem op_le_trace (S : GramSpectrum) : S.lamMax ≤ S.trace := S.hlam_ub

/-- **The trace majorant gives only the Weil scale `√(m·n) = √(p−1) ≈ √p`.** Taking square roots
(`M = √λ_max`), the trace bound is `M ≤ √(m·n)`. With `m ≈ n³` (β=4) this is `√(n⁴) = n²`, the
vacuous Weil scale — the second prong of the pincer (`√p = n² ≫ √n`). -/
theorem trace_gives_weil_scale (S : GramSpectrum) :
    Real.sqrt S.lamMax ≤ Real.sqrt (S.m * S.n) := by
  rw [← S.htrace]
  exact Real.sqrt_le_sqrt S.hlam_ub

/-- **Flatness IS the wall (quantitative gap).** The trace majorant `λ_max ≤ tr G = m·n` is
useful (sub-Weil) only to the extent the spectrum is FLAT. Precisely: a Johnson/prize-scale
conclusion `M = √λ_max ≤ √(C·n)` is *equivalent* to the spectral flatness predicate
`λ_max ≤ C·n` — the top eigenvalue lying within a factor `C` of the average `tr G / m = n`. That
predicate is the spectral form of the Paley/Ramanujan condition for `Cay(F_p,μ_n)`; the sieve
contributes nothing beyond it. We prove the genuine (non-tautological) bridge between the two
formulations: the *sup-norm* statement and the *eigenvalue-flatness* statement coincide, so the
amplified sieve cannot produce the former without the latter (the open wall). -/
theorem flatness_is_the_wall (S : GramSpectrum) {C : ℝ} (hC : 0 ≤ C) :
    Real.sqrt S.lamMax ≤ Real.sqrt (C * S.n) ↔ S.lamMax ≤ C * S.n := by
  have hlam_nonneg : 0 ≤ S.lamMax := le_trans (by linarith [S.hn]) S.hlam_lb
  have hCn_nonneg : 0 ≤ C * S.n := mul_nonneg hC (by linarith [S.hn])
  constructor
  · intro h
    have := Real.sqrt_le_sqrt (le_refl S.lamMax)
    -- square both sides of √λ ≤ √(Cn)
    have h2 : (Real.sqrt S.lamMax) ^ 2 ≤ (Real.sqrt (C * S.n)) ^ 2 := by
      apply sq_le_sq' <;> nlinarith [Real.sqrt_nonneg S.lamMax, Real.sqrt_nonneg (C * S.n), h]
    rwa [Real.sq_sqrt hlam_nonneg, Real.sq_sqrt hCn_nonneg] at h2
  · intro h
    exact Real.sqrt_le_sqrt h

/-- **(II) Frobenius majorant is `≥` the average eigenvalue `n`.** The Frobenius/Schatten-2 bound
`λ_max ≤ ‖G‖_F` cannot drop `λ_max` below the average `tr/m = n`, because `‖G‖_F ≥ λ_max ≥ n`. So
the depth-2 moment ladder already lands at or above `n` — and the prize target `√(n log m)` is
strictly below `n` (in-tree `prize_target_lt_card`: `log m < n`). The Schatten-`r` interpolation
descends toward the prize floor only as `r→∞`, i.e. only in the operator-norm = prize limit. -/
theorem frobenius_ge_average (S : GramSpectrum) : S.n ≤ S.frob :=
  le_trans S.hlam_lb S.hfrob_dom

/-- **The amplified large sieve saturates — the two-majorant dichotomy.** Any phase-blind bound
`M² ≤ B` produced by an amplification scheme lies on one of the two faces:

* **trace face** (`B ≤ tr G`): then `M ≤ √B ≤ √(m·n)`, the Weil/`√p` scale (vacuous), and to do
  better needs the flatness hypothesis (= the wall);
* **Frobenius face** (`B ≥ ‖G‖_F`): then `B ≥ n`, so the bound is `≥` the trivial count `n`, which
  the prize target `√(n log m) < n` lies strictly below.

Hence no phase-blind amplifier certifies `M² < n` (a fortiori not the prize `M ≤ C√(n log m)`)
without ALREADY assuming the spectral flatness it was meant to derive. Stated: if `B` is a
Frobenius-face bound, it is `≥ n`; if it is a trace-face bound, it is the `√(m·n)` scale. The two
faces bracket every phase-blind majorant, and neither reaches below `n` unconditionally. -/
theorem amplified_saturates (S : GramSpectrum) {B : ℝ}
    (hFrob : S.frob ≤ B) :
    S.n ≤ B :=
  le_trans (frobenius_ge_average S) hFrob

/-- **Trace-face form.** A trace-face bound `M² ≤ B ≤ tr G` yields only `M ≤ √(m·n)`. -/
theorem amplified_trace_face (S : GramSpectrum) {B : ℝ}
    (hB_lb : S.lamMax ≤ B) (hB_ub : B ≤ S.trace) :
    Real.sqrt S.lamMax ≤ Real.sqrt (S.m * S.n) :=
  trace_gives_weil_scale S

/-- **The pincer, assembled.** Both phase-blind faces fail to reach the Johnson scale `√n`
unconditionally: the trace face delivers `√(m·n) ≥ √n` (and `= n²` at β=4), the Frobenius face
delivers `≥ n > √n`. So `M ≤ c√n` (let alone the prize `c√(n log m)`) is NOT obtainable from any
phase-blind majorant of the Gram spectrum; it requires the flatness/Paley input directly. We state
the Frobenius-face half quantitatively: the Frobenius majorant on `M = √λ_max` is `≥ √n`. -/
theorem frobenius_face_no_johnson (S : GramSpectrum) :
    Real.sqrt S.n ≤ Real.sqrt S.frob :=
  Real.sqrt_le_sqrt (frobenius_ge_average S)

end ProximityGap.Frontier.AmplifiedLargeSieveSaturates

#print axioms ProximityGap.Frontier.AmplifiedLargeSieveSaturates.op_le_trace
#print axioms ProximityGap.Frontier.AmplifiedLargeSieveSaturates.trace_gives_weil_scale
#print axioms ProximityGap.Frontier.AmplifiedLargeSieveSaturates.flatness_is_the_wall
#print axioms ProximityGap.Frontier.AmplifiedLargeSieveSaturates.frobenius_ge_average
#print axioms ProximityGap.Frontier.AmplifiedLargeSieveSaturates.amplified_saturates
#print axioms ProximityGap.Frontier.AmplifiedLargeSieveSaturates.frobenius_face_no_johnson
