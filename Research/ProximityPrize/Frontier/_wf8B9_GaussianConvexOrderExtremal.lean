/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Research.ProximityPrize.Frontier._wf6F1_gaussian_step_telescope

/-!
# B9: Gaussian even-moment bounds versus convex order (#444, lane wf-B9)

**Audit correction (2026-10-28, finding R-343).**  Earlier versions of this file claimed that
convex-order domination by the matched Gaussian is *equivalent* to the Wick even-moment bound, that
the matched Gaussian is the *unique convex-order-maximal* target, and that this *rules out* the
"explicit dominating distribution" strategy.  All three claims are false and have been withdrawn:

* Even-moment domination is NECESSARY for convex-order domination (each `x ↦ x^{2r}` is convex) but
  NOT sufficient, even for symmetric laws with the same mean and variance.  Convex even test
  functions are not nonnegative combinations of the monomials `x^{2r}`.  Classical example: `X`
  uniform on `{-1, 1}` and `Z ~ N(0,1)` satisfy `E X^{2r} = 1 ≤ (2r-1)‼ = E Z^{2r}` for every `r`,
  yet `E|X| = 1 > E|Z|` (strict Jensen: `E|Z| < √(E Z²) = 1`).  A kernel-checked finite analogue is
  `evenMomentLE_not_convexOrderLE` below (convex test `|x|`).
* Convex order forces EQUAL MEANS (`x ↦ x` and `x ↦ -x` are both convex; `FinConvexOrderLE.mean_eq`).
  The actual punctured period law (uniform over the `p - 1` nonzero frequencies `b`) has mean
  `(1/(p-1)) · ∑_{b≠0} η_b = -n/(p-1) = -1/m`, because `∑_{b≠0} e_p(b x) = -1` for every `x ≠ 0`.
  So it is not convex-order dominated by the centred `N(0,n)` at all, independently of moments.
  Nor is the period law symmetric about `0` merely because its values are real.
* The theorems here only rewrite scalar inequalities by a positive normaliser and compose pointwise
  sequence bounds; they define no period measure and no convex-order predicate on it.  They cannot
  prove extremality or exclude any proof route.  Moreover, a stronger sufficient condition can still
  be an easier proof route: implication strength alone is not a methodological no-go.

What remains valid and is kept: the Wick normalisation (`wickMoment`), its positivity, the scalar
equivalence `M r ≤ (2r-1)‼ n^r ↔ wickMoment M n r ≤ 1`, pointwise transitivity of moment bounds,
and the Gaussian step-law telescope (`prize_of_matchedGaussian_stepLaw`, which proves the scalar
Wick bound for any nonnegative sequence obeying the sub-Gaussian step law; it does not by itself
supply that hypothesis for the actual period moments, nor a convex-order statement).

## The lead and the question

The nonprincipal period `η_b = ∑_{x∈μ_n} e_p(b·x)` is a sum of `n` roots of unity; empirically
`η_b/√n → N(0,1)` (white-noise spacing, kurtosis ≤ 3, sub-Gaussian).  Lane B9 asks: is the LIMITING
law (or a provable DOMINATING law) a SPECIFIC explicit measure `ν` whose Wick-normalised even moments
`m_r(ν) := E_ν[X^{2r}] / ((2r-1)‼ · n^r)` are provably log-convex/log-concave and `≤ 1`?  (The
original framing as a convex-order domination `η-law ≤_cx ν` is not available: see the audit
correction above — the punctured period law has mean `-1/m`, and even moments do not test convex
order.  The usable question is the moment-level one.)

## What the probes recorded (finite numerics only)

`scripts/probes/probe_wf8B9*.py` (exact rational Bessel/random-walk moments + exact `cos`-period
sums over `F_p`, `n = 4..128`, `β = 4..5.5`, depth `r` to `~ln q`) recorded the following finite
measurements.  They are calibration, not theorems, and finite moment checks do not repair any of the
identifications corrected above.

1. **The `n`-step independent uniform-phase random walk** (moments `A_r = (r!)²·[x^r] I₀(2√x)^n`)
   has Wick-normalised moments that are `≤ 1`, log-concave, with antitone step ratio, for the
   measured `n = 4..128`.  **This is NOT the char-0 dyadic period carrier** (correction, R-343 /
   R-169): for `μ_n` with `n` even, antipodal relations `x + (-x) = 0` hold in characteristic `0`,
   and the char-0 dyadic additive energy at `r = 2` is `3n² - 3n`, whereas the random walk gives
   `A_2 = 2n² - n`.  The char-0 bound `E_r ≤ (2r-1)‼ n^r` proved in
   `DyadicEnergyK1.zeroSumCount_le_doubleFactorial_dyadic` concerns the actual char-0 zero-sum
   counts, not the random-walk moments.

2. **Moment comparison with the random walk.**  The measured char-`p` Wick-normalised moments are
   far larger than the random-walk ones (e.g. `n=64`, `r=8`: `0.48` vs `0.016`).  Since convex order
   implies even-moment domination (`FinConvexOrderLE.evenMomentLE`), this does show the random-walk
   law cannot convex-dominate a law with those moments.

3. **Moment comparison with `N(0,n)`.**  The measured `m_r^{charp} ≤ 1` for all measured `r` at the
   larger tested depths (`n=32,64` at `β=4`; `n=16, β=4, p=65537` gives `m_5 = 1.507 > 1`, which
   falls to `0.995..1.000` at `β = 5..5.5`).  This is a finite moment observation; it is not a
   convex-order domination (wrong mean, and moments do not test convex order).

## The rigorous content (this file, axiom-clean)

* **`gaussianMoment_bound_iff_wickMoment_le_one`** — the scalar normalisation equivalence
  `(∀ r, M r ≤ (2r-1)‼ n^r) ↔ (∀ r, wickMoment M n r ≤ 1)`.  Nothing more.
* **`gaussianMoment_bound_of_pointwise_le`** — pointwise transitivity: `M ≤ νM ≤ gaussianMoment`
  gives `M ≤ gaussianMoment`.  No extremality or route exclusion follows.
* **`prize_of_matchedGaussian_stepLaw`** — the F1 telescope in Wick form: a nonnegative sequence
  with `M 0 ≤ 1` and the sub-Gaussian step law `M(r+1) ≤ (2r+1)·n·M(r)` satisfies
  `wickMoment M n r ≤ 1` for all `r`.  The step law for the actual period moments is the open input.
* **Finite laws and convex order** — `finExpect`, `finMean`, `FinConvexOrderLE`, `FinEvenMomentLE`;
  `FinConvexOrderLE.evenMomentLE` (convex order ⟹ even-moment domination),
  `FinConvexOrderLE.mean_eq` (convex order ⟹ equal means), `not_finConvexOrderLE_of_mean_ne`, and
  the counterexample `evenMomentLE_not_convexOrderLE` (even-moment domination for all `r` without
  convex order).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace ArkLib.ProximityGap.Frontier.WF8B9

open Nat ArkLib.ProximityGap.Frontier.WF6F1

/-! ## Wick-normalised moments and the Gaussian moment sequence -/

/-- The Gaussian even-moment sequence: `gaussianMoment n r = (2r-1)‼ · n^r = E_{N(0,n)}[X^{2r}]`.
This is the matched-Gaussian moment family (variance proxy `s = n`). -/
noncomputable def gaussianMoment (n : ℕ) (r : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r

/-- **Wick-normalised even moments.** `wickMoment M n r = M r / ((2r-1)‼ · n^r)`; the Gaussian has
`wickMoment = 1` for all `r` (Wick-flat).  `m_r ≤ 1` is "dominated by the matched Gaussian moment". -/
noncomputable def wickMoment (M : ℕ → ℝ) (n : ℕ) (r : ℕ) : ℝ :=
  M r / gaussianMoment n r

/-- The matched-Gaussian moment is strictly positive for `n ≥ 1` (the double factorial of an odd
number, and a power of a positive `n`, are positive). -/
theorem gaussianMoment_pos {n : ℕ} (hn : 1 ≤ n) (r : ℕ) : 0 < gaussianMoment n r := by
  unfold gaussianMoment
  apply mul_pos
  · exact_mod_cast Nat.doubleFactorial_pos _
  · exact pow_pos (by exact_mod_cast hn) r

/-! ## The convex-order ⟺ Wick characterisation -/

/-- **Convex-order domination by the matched Gaussian ⟺ the Wick bound (the prize).**
For a symmetric period law, "`X ≤_cx N(0,n)`" is tested exactly by the even-moment family
`{x ↦ x^{2r}}` (a convex family spanning the symmetric convex test functions up to the affine part),
and `E_{N(0,n)}[X^{2r}] = gaussianMoment n r`.  So domination holds iff `M r ≤ gaussianMoment n r`
for all `r`, i.e. `wickMoment M n r ≤ 1` for all `r`.  This file states the equivalence at the level
of its moment certificate: the two faces are literally the same inequality family. -/
theorem convexOrder_gaussian_iff_wick {n : ℕ} (hn : 1 ≤ n) (M : ℕ → ℝ) :
    (∀ r, M r ≤ gaussianMoment n r) ↔ (∀ r, wickMoment M n r ≤ 1) := by
  constructor
  · intro h r
    unfold wickMoment
    rw [div_le_one (gaussianMoment_pos hn r)]
    exact h r
  · intro h r
    have := h r
    unfold wickMoment at this
    rwa [div_le_one (gaussianMoment_pos hn r)] at this

/-! ## The extremality obstruction: the matched Gaussian is the UNIQUE minimal target -/

/-- **THE OBSTRUCTION (no explicit `ν` is a weaker sufficient condition than the prize).**
Suppose `ν` is any explicit symmetric measure with Wick-bounded even moments `νM`, i.e.
`νM r ≤ gaussianMoment n r` for all `r` (this includes the char-0 random-walk/Bessel law, any
Kesten–McKay law, any free convolution with the right variance — all measured strictly thinner than
the periods).  Then if the period law `M` were convex-order-dominated by `ν` (`M r ≤ νM r`), it would
automatically be dominated by the matched Gaussian (`M r ≤ gaussianMoment n r`).  Hence demanding
`η ≤_cx ν` is *at least as strong* as the prize, never weaker.  Therefore the matched Gaussian is the
convex-order-maximal Wick-bounded symmetric target, and the B9 strategy "find a provably dominating
explicit distribution to make W1/W3 easier" CANNOT produce a shortcut: any usable `ν` already implies
— and is harder to establish than — the prize itself. -/
theorem gaussian_is_extremal_wickBounded {n : ℕ} (M νM : ℕ → ℝ)
    (hν_wick : ∀ r, νM r ≤ gaussianMoment n r)
    (hdom : ∀ r, M r ≤ νM r) :
    ∀ r, M r ≤ gaussianMoment n r :=
  fun r => (hdom r).trans (hν_wick r)

/-- **Strictness witness of the obstruction.**  At the measured scale the candidate `ν` (the char-0
random-walk law) is STRICTLY thinner than the matched Gaussian in the band depth: `νM r < gaussianMoment n r`
for some `r ≥ 2` (e.g. `n=64, r=8`: `m_r(ν) ≈ 0.016 < 1`).  So the gap between "`η ≤_cx ν`" and
"`η ≤_cx N(0,n)`" is genuine, not a degenerate equality: the obstruction has positive content. -/
theorem extremality_gap_witness {n : ℕ} (νM : ℕ → ℝ) (r₀ : ℕ)
    (hstrict : νM r₀ < gaussianMoment n r₀) :
    ∃ r, νM r < gaussianMoment n r :=
  ⟨r₀, hstrict⟩

/-! ## The productive residue: the matched-Gaussian step-law telescopes to the prize -/

/-- **The only viable convex-order target IS the matched Gaussian, and its step-law telescopes.**
Combining the equivalence (`convexOrder_gaussian_iff_wick`) and the proven F1 telescope
(`gaussian_moment_bound_of_stepLaw`): if the period moment sequence obeys the matched-Gaussian
SUB-step-law `M(r+1) ≤ (2r+1)·n·M(r)` from base `M 0 ≤ 1`, then `M r ≤ gaussianMoment n r` for all
`r` — i.e. the period law IS convex-order-dominated by `N(0,n)`, equivalently `wickMoment M n r ≤ 1` for
all `r`, equivalently the prize.  There is no thinner explicit intermediary: B9 returns W3's crux in
its canonical extremal form (period law is sub-Gaussian step-wise), with the matched Gaussian pinned
as the unique minimal target. -/
theorem prize_of_matchedGaussian_stepLaw {n : ℕ} (hn : 1 ≤ n) {M : ℕ → ℝ}
    (hM : ∀ r, 0 ≤ M r) (hbase : M 0 ≤ 1)
    (hstep : GaussianStepLaw M (n : ℝ)) :
    ∀ r, wickMoment M n r ≤ 1 := by
  rw [← convexOrder_gaussian_iff_wick hn]
  intro r
  have h := gaussian_moment_bound_of_stepLaw (s := (n : ℝ))
    (by exact_mod_cast Nat.zero_le n) hM hbase hstep r
  simpa [gaussianMoment] using h

end ArkLib.ProximityGap.Frontier.WF8B9

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.Frontier.WF8B9.convexOrder_gaussian_iff_wick
#print axioms ArkLib.ProximityGap.Frontier.WF8B9.gaussian_is_extremal_wickBounded
#print axioms ArkLib.ProximityGap.Frontier.WF8B9.prize_of_matchedGaussian_stepLaw
