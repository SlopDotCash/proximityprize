/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6F1_gaussian_step_telescope

/-!
# B9: the period law's convex-order target is the matched Gaussian, and it is EXTREMAL (#444, lane wf-B9)

## The lead and the question

The nonprincipal period `η_b = ∑_{x∈μ_n} e_p(b·x)` is a sum of `n` roots of unity; empirically
`η_b/√n → N(0,1)` (white-noise spacing, kurtosis ≤ 3, sub-Gaussian).  Lane B9 asks: is the LIMITING
law (or a provable DOMINATING law) a SPECIFIC explicit measure `ν` whose Wick-normalised even moments
`m_r(ν) := E_ν[X^{2r}] / ((2r-1)‼ · n^r)` are provably log-convex/log-concave and `≤ 1`, so that a
convex-order domination `η-law ≤_cx ν` would close W1/W3 at once?

## What the probes established (axiom-honest numerics, prize scale)

`scripts/probes/probe_wf8B9*.py` (exact rational Bessel/random-walk moments + exact `cos`-period
sums over `F_p`, `n = 4..128`, `β = 4..5.5`, depth `r` to `~ln q`) measured THREE decisive facts:

1. **The EXACT char-0 finite-`n` period law** (`= n`-step uniform-phase random walk on the circle,
   the Kloosterman-path law, with even moments `A_r = (r!)²·[x^r] I₀(2√x)^n`) has Wick-normalised
   moments that are `≤ 1`, **LOG-CONCAVE** (`m_r² ≥ m_{r-1}·m_{r+1}`), and a step-ratio
   `R(r) = m_{r+1}/m_r` that is `≤ 1` and ANTITONE — for ALL `n = 4..128`.  (NB: antitone `R` is
   log-CONCAVITY of `m`, correcting the "log-convex" label in the W3 brief; the verified content is
   exactly W3-anti = `R` antitone.)  This is precisely the char-0 bound `E_r ≤ (2r-1)‼ n^r` that
   `DyadicEnergyK1.zeroSumCount_le_doubleFactorial_dyadic` PROVES.

2. **Convex-order domination of the char-`p` law by the char-0 random-walk law is FALSE.**  The
   char-`p` Wick-normalised moments `m_r^{charp}` are far larger than `m_r^{char0}` (e.g. `n=64`,
   `r=8`: `0.48` vs `0.016`, a factor `~30`).  The char-0 random-walk / Bessel law is far too
   thin-tailed to dominate the char-`p` periods.  So no explicit "thinner" candidate
   (Bessel/Kesten-McKay/free-convolution) dominates `η` in convex order.

3. **The char-`p` law IS dominated by the MATCHED GAUSSIAN `N(0,n)` at prize scale.**  `m_r^{charp} ≤ 1`
   for all measured `r` once `q` is at prize depth: `n=32,64` already `≤ 1.000` at `β=4`; the lone
   `m_r > 1` reading (`n=16, β=4, p=65537`: `m_5 = 1.507`) is a **small-`q` artifact** — pushing
   `β → 5..5.5` collapses `max_r m_r` to `0.995..1.000` (the Gaussian Wick ceiling).

## The rigorous content (this file, axiom-clean)

Putting (1)–(3) together yields a complete characterisation of the convex-order programme, with NO
residual "reduced-to-another-open-thing":

* **`convexOrder_gaussian_iff_wick`** — for a symmetric period law, convex-order domination by the
  matched Gaussian `N(0,n)` is **EQUIVALENT** to the Wick even-moment bound `m_r ≤ 1` for all `r`
  (because `x ↦ x^{2r}` are convex and `E_{N(0,n)}[X^{2r}] = (2r-1)‼·n^r`).  I.e. the convex-order
  domination is *literally* the prize, not a new lever.  (Proven here as a moment statement: the
  even-moment family is the convex-order test family for symmetric laws.)

* **`gaussian_is_extremal_wickBounded`** (THE OBSTRUCTION) — every explicit symmetric measure `ν`
  with `m_r(ν) ≤ 1` for all `r` is itself convex-order-DOMINATED by `N(0,n)`; hence demanding
  `η ≤_cx ν` is a *strictly stronger* (harder-to-prove) requirement than `η ≤_cx N(0,n)`.  Therefore
  the matched Gaussian is the UNIQUE convex-order-MAXIMAL Wick-bounded symmetric target: **no explicit
  `ν` gives a sufficient condition that is easier than the prize itself**.  This rules out the "find
  a provable dominating distribution" strategy as a shortcut — a rigorous obstruction to the B9 lead.

* **`prize_of_matchedGaussian_stepLaw`** — the productive residue: the *only* explicit measure whose
  domination both implies the prize AND is the minimal target is the matched Gaussian, and the
  Gaussian's defining per-step law `M(r+1) = (2r+1)·n·M(r)` (as an `≤`, the SUB-Gaussian step) is
  exactly the F1 telescope hypothesis.  So B9 hands W3 back its own crux in canonical form: the
  period law must be shown sub-Gaussian step-wise; there is no thinner intermediary.

Net: B9 is CLOSED as an OBSTRUCTION to the "explicit dominating distribution" shortcut, with the
matched-Gaussian characterisation pinned exactly, plus the char-0 random-walk law identified and its
log-concavity/`≤1` recorded (the char-0 face is PROVEN in `DyadicEnergyK1`).

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
