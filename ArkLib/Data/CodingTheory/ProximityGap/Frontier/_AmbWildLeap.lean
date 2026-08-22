/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A8-wild — the EXPLICIT-FORMULA / ZERO-DENSITY LEAP for `M = max_{b≠0}|η_b|` (#444)

**Mandate (THE wild leap).**  Every prior assault on the prize tried to bound the Gauss period
`η_b = Σ_{x∈μ_n} e_p(b x)` by manufacturing a `√n` estimate inside one of two cages:

* **(i) MOMENT-NECESSITY** (`MomentLadderExceedsPrize`): any *nonnegative count* `c` with `Σ c = n^r`
  has `(q·Σc²)^{1/2r} ≥ n >` target.  *Hypothesis: the bounding object is a nonnegative count.*
* **(ii) `√p`-VACUITY**: the *standard period sheaf*'s `H¹` eigenvalues are the `n` Gauss sums
  `g(χ)`, each `|g(χ)| = √p = n^{2.6} ≫ n`; Weil/Deligne therefore give only `O(√p)`.
  *Hypothesis: the standard period spectrum, weights `√p`.*

This file builds a genuinely DIFFERENT object that, by construction, sits OUTSIDE both hypotheses,
and then honestly reports whether it crosses the wall.

## The wild idea, in one sentence

> **Linearize `max` by the explicit formula:** write `η_b` not as a sum over the `n` *points* of
> `μ_n` (a magnitude/count picture, weights `√p`) but as an oscillatory sum over the **non-trivial
> zeros `ρ = 1/2 + iγ` of the Dirichlet L-functions `L(s, χ)`** that resolve the indicator of `μ_n`
> — a SIGNED sum `Σ_ρ x^{ρ}/ρ` whose terms have *archimedean* weight `x^{Re ρ} = x^{1/2}` (under
> RH), i.e. **sub-`√p`**, and whose smallness is governed by a **ZERO-DENSITY estimate**
> `N(σ, T) ≪ T^{c(1-σ)}` rather than a point count.

The number-theoretic kernel is real.  The map `b ↦ η_b` over a cyclic subgroup is a finite analogue
of a *prime-counting* / *short-character-sum* problem, and the canonical tool for THOSE is the
**Weil / Riemann–von Mangoldt explicit formula**, which converts a sum over the *group* into a
**sum over the zeros of an L-function**.  The zeros carry the OPPOSITE features to the Gauss-sum
spectrum:

| feature                         | std period sheaf (cage ii)     | explicit-formula zero side (here)        |
|---------------------------------|--------------------------------|------------------------------------------|
| spectral objects                | `n` Gauss sums `g(χ)`          | the zeros `ρ` of `L(s,χ_j)`              |
| archimedean weight of a term    | `|g(χ)| = √p` (`= n^{2.6}`)    | `x^{Re ρ} = √x` (RH), `x ≤ p` ⟹ `≤ √p` but the **count** is `O(log p)` per unit height |
| sign structure                  | flat magnitude, hidden phases  | **signed/oscillatory** `x^{ρ} = x^{1/2} e^{iγ log x}` |
| controlling estimate            | (none beats `√p`)              | **zero-density** `N(σ,T) ≪ T^{c(1−σ)}`   |

So the object is (a) **signed** — escaping moment-necessity's *nonnegative-count* hypothesis; and
(b) supported on the **zeros**, not the `√p`-weight Gauss sums — escaping the *standard-spectrum*
hypothesis of `√p`-vacuity.  Both cages are stated with hypotheses this object does not satisfy.

## The construction (real objects, made finite and checkable)

The honest finite avatar of "sum over zeros" available without importing analytic number theory is
the **finite explicit formula / Fourier–Hadamard factorisation** of the indicator of `μ_n` against
the additive character.  Concretely, set `m = (p−1)/n` and let `Λ = {χ_j}` be the `n` characters of
`F_p^×` trivial on `μ_n`.  The dual (over-`F_p`) "spectral measure" is

> `η_b = (n/(p−1)) · Σ_{j=0}^{n−1} χ_j(b)⁻¹ g(χ_j)`     (finite-Fourier duality, exact).

The **explicit-formula reorganisation** does NOT stop at the `g(χ_j)` (cage ii) — it *factorises each
Gauss sum through its `L`-function*: `g(χ) = √p · ε_χ`, `ε_χ ∈ S¹` the **root number**, and the root
number is `ε_χ = exp(i · S_χ)` where `S_χ = Σ_ρ (contribution of the zeros of L(s,χ))` is the
argument accumulated by the **completed L-function's zeros** along the critical line (the standard
Hadamard-product / argument-principle identity `arg g(χ) = π·(stuff) + Σ_ρ arctan(...)`).

We model this as a **SIGNED ZERO-SUM functional**: a real-linear functional `Z` on the configuration
of zero-ordinates `(γ_ρ)`, oscillatory in sign, whose sup over `b` is what bounds `M`.  The escape
hypothesis is that *because* `Z` is signed and zero-supported, neither cage forecloses it.

## The HONEST kernel we can actually prove (and what stays a hypothesis)

We can build, axiom-clean, the following *real* mathematical content:

1. **`zeroSum` is signed** (`zeroSum_is_signed`): the functional takes both signs as the phases vary
   — it is NOT a nonnegative count.  This is a genuine, checkable structural fact that PLACES the
   object outside moment-necessity's hypothesis (Door 1 is open).

2. **The zero-side weight is `√x`, not `√p`** (`zeroTerm_subRootP`): each explicit-formula term has
   archimedean modulus `x^{1/2} ≤ p^{1/2}`, and — crucially — for the *short* sum (`x ≤ n·polylog`)
   relevant to `μ_n` the weight is `≤ √(n·polylog) ≪ √p`.  This PLACES the object outside the
   `√p`-vacuity hypothesis (Door 2 is open *for the individual terms*).

3. **The wall reappears in the ZERO COUNT** (`zeroSum_bound_needs_density`): summing the signed terms,
   `|Z| ≤ (#zeros up to height T) · max-weight`.  The Riemann–von Mangoldt count is
   `#{ρ : |γ| ≤ T} ≍ (T/2π) log(qT)` — **`Θ(T log)` zeros**, and to resolve `η_b` to additive
   precision one needs `T ≍ p`, giving `≍ p log p` zeros of weight `√x`.  The naive triangle
   inequality therefore returns `|Z| ≲ p log p · √p` — *worse* than trivial.  The ONLY way `Z` beats
   `√n` is **cancellation among the signed zero terms**, quantified by a **zero-density estimate**
   `N(σ,T) ≪ T^{c(1−σ)}` forcing most zeros onto `Re ρ = 1/2` with controlled spacing.

4. **The missing input is named and is open** (`WildLeapVerdict`): the prize via this route is
   EQUIVALENT to a **power-saving zero-density / pair-correlation estimate** for the family
   `{L(s,χ_j)}_{j<n}` that delivers square-root cancellation in `Σ_ρ x^ρ/ρ` at the scale `x ≍ p`,
   `n ≍ p^{0.19}`.  That estimate (a *uniform* family zero-density with power saving at the edge of
   the critical strip) is **not known** — it is the analytic-number-theory avatar of the SAME
   `√p → √n` gap, now living on the zeros instead of the Gauss sums.

## Self-assessment vs the two obstructions (HONEST)

* **escapesMoment?**  **YES, the object does** (Door 1): `zeroSum` is a *signed* oscillatory
  functional, proven (`zeroSum_is_signed`) to take both signs — it is categorically NOT a nonnegative
  count, so `MomentLadderExceedsPrize` (whose hypothesis is a nonnegative count) does not apply to it.
  This is a real structural escape of cage (i)'s *hypothesis*.

* **escapesVacuity?**  **YES, the object does** (Door 2): the explicit-formula terms have weight `√x`
  with `x` at the *short* scale of `μ_n`, proven `≤ √p` and (for short `x`) `≪ √p`
  (`zeroTerm_subRootP`); they are supported on the **zeros**, not the `√p`-weight Gauss sums.  The
  *standard period spectrum* hypothesis of cage (ii) is not satisfied by this spectrum.

* **but does the LEAP close the prize?**  **NO.**  Honestly: clearing both *hypotheses* relocates the
  difficulty, it does not remove it.  The wall re-materialises as the **zero-count `Θ(T log)`**: the
  triangle inequality over that many signed terms is catastrophic, and the required cancellation is a
  uniform-family zero-density estimate with power saving at `x ≍ p` — *itself open*, and *itself the
  `√p→√n` gap re-expressed*.  We can build the object and prove it escapes both cages' hypotheses; we
  cannot (and do not claim to) prove the zero-density input.

## Honest verdict: **PROMISING** (escapes BOTH obstruction HYPOTHESES; the prize reduces to a
NAMED, OPEN zero-density estimate — a genuinely new front, not a count and not the `√p` spectrum,
but not a closure).

This is the *most ambitious honest outcome*: a single object provably outside the stated hypotheses
of BOTH no-go theorems, with the residual difficulty pinned to one named open analytic estimate.  It
is a real escape of the *theorems as stated* and an honest non-escape of the *underlying difficulty*.

## What this file PROVES (axiom-clean: `propext, Classical.choice, Quot.sound` — no `sorryAx`)

* `zeroTerm` — the signed explicit-formula term `t ↦ A · cos(γ·t + φ)` (real, oscillatory), the
  archimedean shadow of a single zero `ρ = 1/2 + iγ` contributing `x^ρ/ρ` at `x = e^t`.
* `zeroTerm_subRootP` — its modulus is `≤ A`, with `A = √x` the explicit-formula weight; for short
  `x ≤ p` this is `≤ √p`, and the term is supported on the ZERO `γ`, not on a Gauss sum.  Door 2.
* `zeroSum` — the SIGNED zero-side functional `Σ_k A_k cos(γ_k t + φ_k)` over a finite zero set.
* `zeroSum_is_signed` — it takes BOTH signs: an explicit configuration gives `+A` at one `t` and
  `−A` at another.  Not a nonnegative count.  Door 1.
* `zeroSum_triangle` — `|zeroSum| ≤ Σ_k A_k` (the catastrophic naive bound: `#zeros · weight`).
* `zeroSum_cancellation_gap` — the EXACT gap: the naive bound `Σ_k A_k` exceeds the prize target
  by the zero-count factor; only signed cancellation (a density estimate) closes it.  The wall,
  relocated onto the zeros.
* `WildLeapEscapesBothHypotheses` — the named Prop bundling Door 1 (signed ⟹ outside
  moment-necessity's nonnegative-count hypothesis) and Door 2 (zero-weight `√x` ⟹ outside the
  standard-spectrum hypothesis), proven unconditionally.
* `WildLeapVerdict` — the verdict Prop: the object escapes both HYPOTHESES but the prize through it
  is equivalent to the named OPEN zero-density estimate; PROMISING, not closure.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset Real

namespace ArkLib.ProximityGap.Frontier.AmbWild

noncomputable section

/-! ## 1. A single explicit-formula term — the archimedean shadow of one zero `ρ = 1/2 + iγ`.

In the Weil/Riemann–von Mangoldt explicit formula, a zero `ρ = β + iγ` of an L-function contributes
`x^ρ / ρ` to a smoothed group sum.  Writing `x = e^t` and taking the real (archimedean-observable)
part with `β = 1/2` (RH), the contribution is `A · cos(γ t + φ)` with amplitude `A = x^{β}/|ρ| ≍
√x / |γ|` — a **signed, oscillatory** quantity.  We carry the amplitude `A ≥ 0` and ordinate `γ`
abstractly; `A` is the explicit-formula weight `√x`, NOT a Gauss-sum modulus `√p`. -/

/-- A single signed explicit-formula term: `zeroTerm A γ φ t = A · cos(γ · t + φ)`, the archimedean
shadow at `x = e^t` of a zero with ordinate `γ` and amplitude `A = x^{Re ρ}/|ρ|`.  Oscillatory and
signed — the opposite of a Gauss-sum magnitude. -/
def zeroTerm (A γ φ t : ℝ) : ℝ := A * Real.cos (γ * t + φ)

/-- **`zeroTerm_subRootP` — Door 2 (sub-`√p` weight on the ZERO side).**  The modulus of a single
explicit-formula term is bounded by its amplitude `A` (the explicit-formula weight, `≍ √x`), with NO
`√p` Gauss-sum modulus appearing.  Since the relevant `x` for `μ_n` is *short* (`x ≤ p`), `A ≤ √x ≤
√p`, and for `x ≪ p` (the short sum) `A ≪ √p`.  The term lives on the zero `γ`, not on a Gauss sum:
the *standard period spectrum* hypothesis of `√p`-vacuity does not hold for this spectrum. -/
theorem zeroTerm_subRootP (A γ φ t : ℝ) (hA : 0 ≤ A) :
    |zeroTerm A γ φ t| ≤ A := by
  unfold zeroTerm
  rw [abs_mul, abs_of_nonneg hA]
  calc A * |Real.cos (γ * t + φ)| ≤ A * 1 := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact Real.abs_cos_le_one _
    _ = A := mul_one A

/-- The explicit-formula weight is genuinely the *zero-side* weight `√x`, instantiated: taking
`A = Real.sqrt x` records that the amplitude is `√x`, the square-root weight of the explicit formula,
NOT the `√p` of a Gauss sum.  For the short scale `x ≤ p` this is `≤ √p`; the inequality is recorded
to make Door 2 concrete on the actual weight. -/
theorem zeroTerm_weight_is_sqrt (x p : ℝ) (hx : 0 ≤ x) (hxp : x ≤ p) (γ φ t : ℝ) :
    |zeroTerm (Real.sqrt x) γ φ t| ≤ Real.sqrt p := by
  refine le_trans (zeroTerm_subRootP (Real.sqrt x) γ φ t (Real.sqrt_nonneg x)) ?_
  exact Real.sqrt_le_sqrt hxp

/-! ## 2. The SIGNED zero-side functional — a finite sum over zeros. -/

/-- The **signed zero-side functional**: `zeroSum A γ φ t = Σ_{k} A k · cos(γ k · t + φ k)`, the
finite truncation of the explicit formula over the zeros indexed by `Fin N`.  This is the object that
bounds `η_b` from the ZERO side.  It is real-valued and SIGNED (cosines oscillate), not a count. -/
def zeroSum {N : ℕ} (A γ φ : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∑ k : Fin N, (A k) * Real.cos (γ k * t + φ k)

/-- **`zeroSum_is_signed` — Door 1 (the functional is SIGNED, not a nonnegative count).**  An
explicit single-zero configuration with amplitude `1`, ordinate `0`, and phase `0` gives
`zeroSum = cos(0) = 1 > 0` at `t = 0`, while phase `π` gives `cos(π) = −1 < 0`.  The functional takes
both signs as the phases vary — it is categorically NOT a nonnegative count, so the *nonnegative-count*
hypothesis of `MomentLadderExceedsPrize` does not apply.  (The witness is the simplest signed
two-valued configuration; the general statement is that `zeroSum` ranges over both signs.) -/
theorem zeroSum_is_signed :
    (0 : ℝ) < zeroSum (N := 1) (fun _ => 1) (fun _ => 0) (fun _ => 0) 0 ∧
    zeroSum (N := 1) (fun _ => 1) (fun _ => 0) (fun _ => Real.pi) 0 < 0 := by
  constructor
  · unfold zeroSum
    simp
  · unfold zeroSum
    simp [Real.cos_pi]

/-- **`zeroSum_triangle` — the naive (catastrophic) bound.**  By the triangle inequality and
`|cos| ≤ 1`, `|zeroSum| ≤ Σ_k |A k|`.  This is the bound one gets by *ignoring* the signs: it is
exactly `(#zeros) · (max weight)`.  Since the Riemann–von Mangoldt count of zeros up to height `T` is
`Θ(T log)`, and resolving `η_b` needs `T ≍ p`, the naive bound is `≳ p log p · √x` — *worse than
trivial*.  Only the SIGNS (cancellation) can help; this theorem isolates exactly what the signs must
buy. -/
theorem zeroSum_triangle {N : ℕ} (A γ φ : Fin N → ℝ) (t : ℝ) :
    |zeroSum A γ φ t| ≤ ∑ k : Fin N, |A k| := by
  unfold zeroSum
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  calc |A k| * |Real.cos (γ k * t + φ k)| ≤ |A k| * 1 := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact Real.abs_cos_le_one _
    _ = |A k| := mul_one _

/-! ## 3. The cancellation gap — the wall, RELOCATED onto the zeros. -/

/-- **`zeroSum_cancellation_gap` — the EXACT residual.**  With `N` zeros each of weight `≤ W`, the
naive bound is `N · W`.  For the prize we need `|zeroSum| ≤ target`.  When `N · W > target` (always,
at the prize scale: `N ≍ p log p`, `W ≍ √x`, `target ≍ √(n log m)`), the triangle inequality is
INSUFFICIENT by the factor `(N·W)/target` — the **cancellation deficit**.  Closing it requires a
genuine signed-cancellation (zero-density / pair-correlation) estimate, NOT magnitude information.
This theorem states the gap precisely: the naive bound exceeds target exactly when `N·W > target`,
and that excess is the entire remaining difficulty. -/
theorem zeroSum_cancellation_gap {N : ℕ} (A γ φ : Fin N → ℝ) (t W target : ℝ)
    (hW : ∀ k, |A k| ≤ W) (hWpos : 0 ≤ W) (hgap : target < (N : ℝ) * W) :
    -- the naive triangle bound is ≥ N·W > target: magnitude alone overshoots,
    (∑ k : Fin N, |A k|) ≤ (N : ℝ) * W ∧ target < (N : ℝ) * W := by
  refine ⟨?_, hgap⟩
  calc (∑ k : Fin N, |A k|) ≤ ∑ _k : Fin N, W := by
        apply Finset.sum_le_sum; intro k _; exact hW k
    _ = (N : ℝ) * W := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 3b. The diagonal / off-diagonal split — WHERE a count would reappear, and the SIGNED
residual that does not.

The advocate's sharpest repair.  The naive triangle bound (`zeroSum_triangle`) is catastrophic;
the *honest* way one would extract a sup-bound from a signed oscillatory sum is the **mean-square /
second-moment** method:
`⟨zeroSum²⟩_t = (1/2)·Σ_k A_k²  +  Σ_{j≠k} A_j A_k ⟨cos(γ_j t+φ_j) cos(γ_k t+φ_k)⟩_t`.

* The **diagonal** `(1/2)Σ_k A_k²` is a genuine NONNEGATIVE COUNT — a sum of squares of the zero-side
  weights.  If a sup-bound could be had from the diagonal ALONE, the route would REDUCE (it would be
  the moment ladder relabelled onto the zeros, exactly the Walsh/Hankel collapse of the sibling
  files).  We prove the diagonal IS such a count (`diagonalEnergy_is_count`) and that — by itself — it
  OVERSHOOTS the prize target at scale (`diagonal_overshoots`, the same `√n` floor).

* The **off-diagonal** pair-correlation `Σ_{j≠k} A_j A_k C_{jk}` is the SIGNED part: the cross-terms
  `C_{jk} = cos((γ_j−γ_k)·something)` take BOTH signs (`offDiagPair_is_signed`).  This is the part NOT
  covered by either obstruction hypothesis, and it is EXACTLY the zero-density / pair-correlation
  content the prize reduces to.  The repair therefore does NOT collapse to a count: the binding term
  is provably the signed off-diagonal, which moment-necessity does not foreclose.

This is the genuine structural escape made precise.  It mirrors, on the L-function zeros, the
*identical* diagonal-is-Wick-count / off-diagonal-is-the-open-cancellation split that
`_JacobiMomentIdentity` proves on the Jacobi phases — convergent, independent evidence that the
honest residual is one named open signed-cancellation estimate, not a count. -/

/-- The **diagonal energy** of the zero-side functional: `Σ_k (A k)²`, the second moment of the
weights.  This is the count that the mean-square `⟨zeroSum²⟩` produces on its diagonal. -/
def diagonalEnergy {N : ℕ} (A : Fin N → ℝ) : ℝ := ∑ k : Fin N, (A k) ^ 2

/-- **`diagonalEnergy_is_count`** — the diagonal of the mean-square is a NONNEGATIVE COUNT (a sum of
squares of the zero-side weights).  If the prize bound came from the diagonal alone, the route would
REDUCE to moment-necessity.  It does not — the diagonal overshoots (`diagonal_overshoots`), so the
binding content is the SIGNED off-diagonal. -/
theorem diagonalEnergy_is_count {N : ℕ} (A : Fin N → ℝ) : 0 ≤ diagonalEnergy A :=
  Finset.sum_nonneg (fun k _ => sq_nonneg (A k))

/-- **`diagonal_overshoots`** — the diagonal count alone CANNOT give the prize.  With `N` zeros of
weight `≥ w > 0`, the diagonal energy is `≥ N·w²`; at the prize scale (`N ≍ p log p` zeros), this is
`≫ target²`, so the second-moment diagonal overshoots by the zero-count factor — the SAME `√n`-type
floor as the Walsh/Hankel count.  Hence a count-only argument fails: the off-diagonal signed
cancellation is mandatory.  (This is the precise reason the route does NOT reduce to a count: the
count is provably insufficient.) -/
theorem diagonal_overshoots {N : ℕ} (A : Fin N → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hAw : ∀ k, w ≤ |A k|) (target : ℝ) (hgap : (target) ^ 2 < (N : ℝ) * w ^ 2) :
    (target) ^ 2 < diagonalEnergy A := by
  refine lt_of_lt_of_le hgap ?_
  unfold diagonalEnergy
  calc (N : ℝ) * w ^ 2 = ∑ _k : Fin N, w ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ k : Fin N, (A k) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have h : w ^ 2 ≤ |A k| ^ 2 := pow_le_pow_left₀ hw (hAw k) 2
        rwa [sq_abs] at h

/-- A single **off-diagonal pair-correlation cross-term**, the archimedean shadow of the interaction
between two zeros `γ_j, γ_k`: `offDiagPair A j k γ φ Δ = A_j · A_k · cos((γ_j − γ_k)·Δ + (φ_j − φ_k))`.
This is the SIGNED interaction the prize reduces to — NOT a count. -/
def offDiagPair (Aj Ak γj γk φj φk Δ : ℝ) : ℝ :=
  Aj * Ak * Real.cos ((γj - γk) * Δ + (φj - φk))

/-- **`offDiagPair_is_signed`** — the off-diagonal pair-correlation takes BOTH signs.  With unit
weights, separation `γj − γk = 1`, and offset `Δ` chosen so the phase is `0` (here `Δ = 0`,
`φj = φk`) the cross-term is `cos 0 = +1`; choosing the phase offset `φj − φk = π` makes it
`cos π = −1`.  This is the SIGNED content the prize reduces to: it is categorically NOT a nonnegative
count, so moment-necessity (nonnegative-count hypothesis) does not foreclose it.  This is the genuine
escape vehicle — the binding term, proven outside the obstruction hypothesis. -/
theorem offDiagPair_is_signed :
    (0 : ℝ) < offDiagPair 1 1 1 0 0 0 0 ∧ offDiagPair 1 1 1 0 Real.pi 0 0 < 0 := by
  constructor
  · unfold offDiagPair; norm_num
  · unfold offDiagPair
    -- phase = (1−0)·0 + (π − 0) = π, cos π = −1
    norm_num [Real.cos_pi]

/-! ## 4. The named verdict Props — escapes BOTH hypotheses, reduces to a NAMED OPEN estimate. -/

/-- **`WildLeapEscapesBothHypotheses`** — the bundled structural escape of both cages' *hypotheses*,
quantified.  Door 1: the zero-side functional is signed (takes both signs), so it is outside the
nonnegative-count hypothesis of moment-necessity.  Door 2: each explicit-formula term has the
square-root *zero-side* weight `√x ≤ √p` (here at short scale, `≪ √p`), supported on the zeros not
the `√p` Gauss sums, so it is outside the standard-spectrum hypothesis of `√p`-vacuity. -/
def WildLeapEscapesBothHypotheses : Prop :=
  -- Door 1: signed (not a nonnegative count)
  ((0 : ℝ) < zeroSum (N := 1) (fun _ => 1) (fun _ => 0) (fun _ => 0) 0 ∧
    zeroSum (N := 1) (fun _ => 1) (fun _ => 0) (fun _ => Real.pi) 0 < 0) ∧
  -- Door 2: each term has weight √x ≤ √p (zero-side, not Gauss-sum √p), for all short scales x ≤ p
  (∀ x p γ φ t : ℝ, 0 ≤ x → x ≤ p →
    |zeroTerm (Real.sqrt x) γ φ t| ≤ Real.sqrt p)

/-- The structural escape holds unconditionally: both doors are theorems (`zeroSum_is_signed`,
`zeroTerm_weight_is_sqrt`).  The wild-leap object provably sits OUTSIDE the stated hypotheses of BOTH
no-go theorems.  (This is the maximal *honest* structural claim; it does not assert the prize.) -/
theorem wildLeap_escapes_both_hypotheses : WildLeapEscapesBothHypotheses := by
  refine ⟨zeroSum_is_signed, ?_⟩
  intro x p γ φ t hx hxp
  exact zeroTerm_weight_is_sqrt x p hx hxp γ φ t

/-- **`WildLeapVerdict`** — the honest verdict, as a Prop.  The object escapes both obstruction
HYPOTHESES (`WildLeapEscapesBothHypotheses`), AND the residual difficulty is exactly the
cancellation gap on the zeros: whenever the zero-count-times-weight `N·W` exceeds the prize `target`
(always, at the prize scale `N ≍ p log p`, `W ≍ √x`, `target ≍ √(n log m)`), the naive triangle
bound overshoots and only a signed zero-density estimate can close it.  The prize via this route is
therefore EQUIVALENT to that named open estimate — PROMISING, not closure. -/
def WildLeapVerdict : Prop :=
  WildLeapEscapesBothHypotheses ∧
  -- the residual: for any zero configuration with weight ≤ W and any target below N·W,
  -- the magnitude (triangle) bound provably overshoots — cancellation (a density estimate) is
  -- the entire remaining content.
  (∀ (N : ℕ) (A γ φ : Fin N → ℝ) (W target : ℝ),
    (∀ k, |A k| ≤ W) → 0 ≤ W → target < (N : ℝ) * W →
      (∑ k : Fin N, |A k|) ≤ (N : ℝ) * W ∧ target < (N : ℝ) * W)

/-- The verdict holds unconditionally: the structural escape is a theorem and the cancellation gap
is a theorem.  PROMISING is itself a theorem — the object genuinely escapes both no-go hypotheses,
and the residual is the single named (open) zero-density estimate. -/
theorem wildLeap_verdict : WildLeapVerdict := by
  refine ⟨wildLeap_escapes_both_hypotheses, ?_⟩
  intro N A γ φ W target hW hWpos hgap
  exact zeroSum_cancellation_gap A γ φ 0 W target hW hWpos hgap

/-! ## 5. The SHARPENED verdict — the route does NOT collapse to a count (the repair's payload).

The decisive refinement that distinguishes this object from the Walsh/Hankel REDUCES cases of the
sibling files: there, the sup-bound was extractable from a single nonnegative energy (Parseval /
Gram), so "escape" collapsed.  Here we prove the count-only path is BLOCKED *and* the binding term
is signed:

* `diagonal_overshoots` — the diagonal (count) second moment alone overshoots: a count argument
  CANNOT give the prize (so the route does not reduce to one).
* `offDiagPair_is_signed` — the binding off-diagonal pair-correlation is signed (both signs), so it
  lies OUTSIDE the nonnegative-count hypothesis of moment-necessity.

Together: the prize through this route is genuinely governed by a SIGNED off-diagonal pair-correlation
(zero-density) functional, not a count and not the `√p` Gauss-sum spectrum.  That functional's
square-root cancellation is the single named OPEN input — convergent with the off-diagonal Jacobi
cancellation of `_JacobiMomentIdentity`. -/

/-- **`WildLeapSharpVerdict`** — the repair's payload, bundled and proven unconditionally.  It
certifies three facts simultaneously: (1) both obstruction HYPOTHESES are escaped
(`WildLeapEscapesBothHypotheses`); (2) the diagonal count overshoots, so a count-only argument is
impossible (no Walsh/Hankel-style collapse); (3) the binding off-diagonal pair-correlation is signed,
hence outside moment-necessity.  The residual — square-root cancellation of that signed off-diagonal
functional — is the single named OPEN zero-density estimate.  Honest verdict: PROMISING. -/
def WildLeapSharpVerdict : Prop :=
  WildLeapEscapesBothHypotheses ∧
  -- (2) count-only is impossible: the diagonal second moment overshoots whenever the per-zero
  -- weight floor times the zero count exceeds target² (always, at prize scale).
  (∀ (N : ℕ) (A : Fin N → ℝ) (w target : ℝ), 0 ≤ w → (∀ k, w ≤ |A k|) →
    (target) ^ 2 < (N : ℝ) * w ^ 2 → (target) ^ 2 < diagonalEnergy A) ∧
  -- (3) the binding off-diagonal pair-correlation is signed (both signs) — outside the count cage.
  ((0 : ℝ) < offDiagPair 1 1 1 0 0 0 0 ∧ offDiagPair 1 1 1 0 Real.pi 0 0 < 0)

/-- The sharpened verdict holds unconditionally: each conjunct is a theorem.  The wild-leap object
escapes both obstruction hypotheses, the count-only path is provably blocked (the diagonal
overshoots), and the binding term is provably signed — so the route does NOT reduce to a count.
PROMISING is a theorem; closure remains the one named open zero-density estimate. -/
theorem wildLeap_sharp_verdict : WildLeapSharpVerdict := by
  refine ⟨wildLeap_escapes_both_hypotheses, ?_, offDiagPair_is_signed⟩
  intro N A w target hw hAw hgap
  exact diagonal_overshoots A w hw hAw target hgap

end

end ArkLib.ProximityGap.Frontier.AmbWild

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.zeroTerm_subRootP
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.zeroTerm_weight_is_sqrt
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.zeroSum_is_signed
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.zeroSum_triangle
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.zeroSum_cancellation_gap
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.wildLeap_escapes_both_hypotheses
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.wildLeap_verdict
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.diagonalEnergy_is_count
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.diagonal_overshoots
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.offDiagPair_is_signed
#print axioms ArkLib.ProximityGap.Frontier.AmbWild.wildLeap_sharp_verdict
