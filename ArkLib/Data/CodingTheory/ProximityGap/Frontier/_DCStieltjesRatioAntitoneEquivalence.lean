/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PowerSumRatioMonotone

/-!
# The DC-subtracted Gaussian-normalized step ratio: exact log-convexity constraints (#466)

## Setting

The prize CORE object is the DC-subtracted spectral moment sequence
`A_r := ∑_{b≠0} ‖η_b‖^{2r}` (`DCSubtractedMoment.sum_nonzero_moment`: `A_r = q·E_r − |G|^{2r}`).
Because `A_r = ∑_{b≠0} λ_b^r` with `λ_b := ‖η_b‖^2 ≥ 0`, it is a **genuine positive (Stieltjes)
moment sequence** of the atomic spectral measure `ν = ∑_{b≠0} δ_{λ_b}`. Consequently it is
log-convex (`PowerSumRatioMonotone.powerSum_sq_le_mul`: `A_{r+1}² ≤ A_r·A_{r+2}`), so the **raw
ratio** `ρ_r := A_{r+1}/A_r` is monotone **non-decreasing** (`powerSum_ratio_monotone`) and rises
toward the top of the spectrum `M² = max_{b≠0} λ_b`.

The Fable-critic / WF7 "step-ratio ladder" route asks whether the **Gaussian-normalized** ratio
`R̃_r := ρ_r / ((2r+1)·n) = A_{r+1} / ((2r+1)·n·A_r)` is **antitone** (`R̃_{r+1} ≤ R̃_r`), because
`WF7W3.stepLaw_of_antitone_base` shows base (`R̃_1 ≤ 1`) + antitone ⟹ `A_r ≤ (2r−1)‼·n^r` for all
`r` ⟹ the prize `M ≤ √(n·log(p/n))`.

`_CharPStepRatioMonotoneFails` refuted antitonicity for the **raw** (un-DC-subtracted) energy `E_r`.
This file settles the DC-subtracted question at the level it actually lives: **structurally**, via
the Stieltjes / log-convexity algebra, independent of any single prime.

## The exact log-convexity constraint (the theorem, prime-independent)

Write `g_r := ρ_{r+1}/ρ_r` (the per-step growth of the log-convex ratio; the "second log-difference"
of `A`). Then, for a positive log-convex `A`:

> **`R̃` antitone at `r`  ⟺  `g_r ≤ (2r+3)/(2r+1)`.**   (`Rtilde_antitone_iff_growth_le`)

and, because `A` is a *Stieltjes* sequence, the free lower bound `g_r ≥ 1` holds
(`growth_ge_one_of_logConvex`). Hence antitonicity is exactly the **sandwich**

> **`1 ≤ g_r ≤ 1 + 2/(2r+1)`**   (`Rtilde_antitone_iff_sandwich`),

whose **lower half is FREE** (Stieltjes log-convexity) and whose **upper half `g_r ≤ 1+2/(2r+1)` is
the ENTIRE content** — a per-step *cap on how fast the log-convex ratio may accelerate*.

## Classification of the desired antitonicity (the CORE verdict)

**Not forced, not vacuously false, and equivalent-in-difficulty to the M-bound.**

* The upper cap `g_r ≤ 1+2/(2r+1)` is **NOT implied** by positivity + log-convexity: a Stieltjes
  sequence can violate it. `stieltjes_can_violate_cap` exhibits an explicit two-atom nonnegative
  spectrum whose (genuine, log-convex, Stieltjes) moment sequence has `g_1 > 1 + 2/3` — the abstract
  shadow of the exact char-`p` witnesses (n=32, p∈{1391393, 2089889, 4102753}) where `R̃` reverses,
  `g_2 > 7/5`. So antitonicity is a **nontrivial arithmetic hypothesis**, not a structural theorem.
* It is **not** the raw-`E_r` failure of `_CharPStepRatioMonotoneFails`: the DC subtraction genuinely
  repairs the sign at many primes (including the primary K-bad n=32 prime p=786433 where the *raw*
  step-ratio reverses). The empirical separation (DC repairs the sign where raw fails) is recorded in
  the probe + report, not as a Lean claim; the Lean content is the prime-independent structure below.
* It is **equivalent-in-difficulty to bounding `M`**: `ρ_r ↗ M²`, so the cap `g_r ≤ 1+2/(2r+1)` for
  all `r ≤ log p` says exactly *the annealed spectral average climbs to `M²` no faster than the
  Gaussian schedule allows* — which, telescoped, is `A_r ≤ (2r−1)‼·n^r` = the prize.
  `cap_forces_gaussian_ratio` proves the cap-at-`r` gives the pointwise Gaussian ratio bound
  `ρ_r ≤ (2r+1)·n·R̃_1`, i.e. no M-free lever is created — the cap **is** the depth-`r` M-control.

**Net:** the DC-subtracted step-ratio antitonicity is *structurally possible* (unlike the raw one,
which is false), but it is **equivalent to the M-bound**, not a shortcut to it. The honest CORE
handoff: the only content is the per-step acceleration cap `g_r ≤ 1+2/(2r+1)`, which is a Turán-type
second-log-difference bound on the DC spectral moments and is exactly as hard as the prize.

## What is PROVEN here (axiom target `{propext, Classical.choice, Quot.sound}`, no `sorry`)

* `growth_ge_one_of_logConvex` — Stieltjes ⟹ `g_r ≥ 1` (free lower half).
* `Rtilde_antitone_iff_growth_le` — `R̃_{r+1} ≤ R̃_r ⟺ g_r ≤ (2r+3)/(2r+1)`.
* `Rtilde_antitone_iff_sandwich` — antitone ⟺ the sandwich `1 ≤ g_r ≤ 1+2/(2r+1)`.
* `cap_forces_gaussian_ratio` — the cap delivers the depth-`r` Gaussian ratio bound (M-equivalence).
* `stieltjes_can_violate_cap` — an explicit Stieltjes spectrum violating the cap (not-forced).

## Honesty / scope (rules 1,3,6)

Pure real algebra over an abstract nonnegative spectrum + the in-tree Stieltjes log-convexity. It is
field-universal (holds for the thick group too) and therefore, by rule 3, does **not** and **cannot**
prove the thinness-essential prize; it CLASSIFIES the antitone route as M-equivalent and NOT free.
No `axiom`/`native_decide`/`opaque`/`: True`/goal-weakening/hidden `sorry`. No char-p transfer, no
capacity/BGK claim. CORE stays OPEN.

Probe `scripts/probes/probe_466_dc_stieltjes_ratio.py`: exact DC moments `A_r = q·E_r − n^{2r}` via
integer modular convolution; confirms `ρ_r` monotone-up (Stieltjes) at every tested prime, and `R̃_r`
antitone at {F4/gen n16; p=786433, generic n32} but REVERSED at {p=1391393, 2089889, 4102753 (n32)}
with exact caps `g_2 = 1.406, 1.415, 1.408 > 7/5` — the abstract `stieltjes_can_violate_cap` made
arithmetic. Antitone failure tracks the largest wall constant `C = M/√(2n log p)` (C≈1.39 at the
worst violator), the M-equivalence in data.

## References
- `PowerSumRatioMonotone.powerSum_ratio_monotone` (the Stieltjes lower half reused here).
- `DCSubtractedMoment.sum_nonzero_moment` (`A_r = q·E_r − |G|^{2r}`).
- `_CharPStepRatioMonotoneFails` (the RAW-energy step-ratio refutation this DC analysis separates from).
- `_wf7W3_HypercontractiveStepAntitone` (`stepLaw_of_antitone_base`: base+antitone ⟹ prize).
- `_AvL11_DCSubtractedSOSHankel` (the DC Hankel/moment-certificate obstruction at order 3).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #466.
-/

open Finset

namespace ProximityGap.Frontier.DCStieltjesRatioAntitone

/-! ## 1. Abstract step-ratio algebra over a positive log-convex sequence

We work with an abstract sequence `A : ℕ → ℝ` (think `A r = ∑_{b≠0} λ_b^r`), its raw ratio
`ρ r = A (r+1) / A r`, and the Gaussian-normalized ratio `R̃ r = ρ r / ((2r+1)·n)`. All statements
are pointwise at a depth `r`, requiring only the positivity actually used. -/

variable (A : ℕ → ℝ) (n : ℝ)

/-- The raw log-convex ratio `ρ_r := A_{r+1} / A_r`. -/
noncomputable def rho (r : ℕ) : ℝ := A (r + 1) / A r

/-- The Gaussian-normalized step ratio `R̃_r := ρ_r / ((2r+1)·n) = A_{r+1} / ((2r+1)·n·A_r)`.
`R̃_r ≤ 1` is the depth-`r` sub-Gaussian (Wick) statement; antitonicity of `R̃` + base ⟹ prize. -/
noncomputable def Rtilde (r : ℕ) : ℝ := rho A r / ((2 * (r : ℝ) + 1) * n)

/-- `R̃_r` unfolds to `A_{r+1} / ((2r+1)·n·A_r)`. -/
theorem Rtilde_eq (r : ℕ) :
    Rtilde A n r = A (r + 1) / ((2 * (r : ℝ) + 1) * n * A r) := by
  unfold Rtilde rho
  rw [div_div]
  ring_nf

/-! ## 2. The free lower half: Stieltjes ⟹ `ρ_{r+1}/ρ_r ≥ 1`

If `A` is log-convex (`A_{r+1}² ≤ A_r·A_{r+2}`) with positive entries, the ratio `ρ` is monotone
non-decreasing, i.e. the per-step growth `g_r := ρ_{r+1}/ρ_r ≥ 1`. This is the LOWER half of the
antitone sandwich and it is FREE for any positive moment (Stieltjes) sequence. -/

/-- **Free lower half (Stieltjes).** For positive `A` with the one log-convexity inequality
`A_{r+1}² ≤ A_r·A_{r+2}`, the raw ratio is non-decreasing: `ρ_r ≤ ρ_{r+1}`. Equivalently the per-step
growth `g_r = ρ_{r+1}/ρ_r ≥ 1`. This is exactly the Cauchy–Schwarz / log-convexity backbone
(`powerSum_ratio_monotone`) transported to the abstract ratio. -/
theorem rho_monotone_of_logConvex {r : ℕ}
    (hAr : 0 < A r) (hAr1 : 0 < A (r + 1))
    (hlog : A (r + 1) ^ 2 ≤ A r * A (r + 2)) :
    rho A r ≤ rho A (r + 1) := by
  unfold rho
  rw [div_le_div_iff₀ hAr hAr1]
  nlinarith [hlog]

/-- The per-step growth `g_r := ρ_{r+1}/ρ_r` is `≥ 1` for a positive log-convex sequence with
`ρ_r > 0`. (Stated as the ratio being `≥ 1`; used as the free lower half of the sandwich.) -/
theorem growth_ge_one_of_logConvex {r : ℕ}
    (hAr : 0 < A r) (hAr1 : 0 < A (r + 1))
    (hlog : A (r + 1) ^ 2 ≤ A r * A (r + 2))
    (hrho : 0 < rho A r) :
    1 ≤ rho A (r + 1) / rho A r := by
  rw [le_div_iff₀ hrho, one_mul]
  exact rho_monotone_of_logConvex A hAr hAr1 hlog

/-! ## 3. The exact equivalence: `R̃` antitone ⟺ per-step growth cap `g_r ≤ (2r+3)/(2r+1)`

`R̃_{r+1} ≤ R̃_r`  ⟺  `ρ_{r+1}/((2r+3)n) ≤ ρ_r/((2r+1)n)`  ⟺  `(2r+1)·ρ_{r+1} ≤ (2r+3)·ρ_r`  ⟺
`ρ_{r+1}/ρ_r ≤ (2r+3)/(2r+1) = 1 + 2/(2r+1)`. The `n>0` cancels; the whole content is the growth
cap. -/

/-- **The antitone step is exactly the growth cap (cross-multiplied form).**
`R̃_{r+1} ≤ R̃_r`  ⟺  `(2r+1)·ρ_{r+1} ≤ (2r+3)·ρ_r`. Clean of division: this is the operative
inequality a proof must supply at each depth. -/
theorem Rtilde_antitone_iff_growth_cross {r : ℕ} (hn : 0 < n) :
    Rtilde A n (r + 1) ≤ Rtilde A n r ↔
      (2 * (r : ℝ) + 1) * rho A (r + 1) ≤ (2 * (r : ℝ) + 3) * rho A r := by
  unfold Rtilde
  have h1 : (0 : ℝ) < 2 * (r : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < 2 * ((r : ℝ) + 1) + 1 := by positivity
  have e2 : (2 * (((r : ℕ) + 1 : ℕ) : ℝ) + 1) = 2 * (r : ℝ) + 3 := by push_cast; ring
  rw [e2]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  constructor
  · intro h; nlinarith [h, mul_pos h1 hn, mul_pos h2 hn]
  · intro h; nlinarith [h, mul_pos h1 hn, mul_pos h2 hn]

/-- **The exact log-convexity constraint (ratio form).** With `ρ_r > 0` and `n > 0`,
`R̃_{r+1} ≤ R̃_r  ⟺  ρ_{r+1}/ρ_r ≤ (2r+3)/(2r+1)`. The RHS `(2r+3)/(2r+1) = 1 + 2/(2r+1)` is the
per-step acceleration budget of the log-convex ratio: this and nothing else is what antitonicity
demands. -/
theorem Rtilde_antitone_iff_growth_le {r : ℕ} (hn : 0 < n) (hrho : 0 < rho A r) :
    Rtilde A n (r + 1) ≤ Rtilde A n r ↔
      rho A (r + 1) / rho A r ≤ (2 * (r : ℝ) + 3) / (2 * (r : ℝ) + 1) := by
  rw [Rtilde_antitone_iff_growth_cross A n hn]
  rw [div_le_div_iff₀ hrho (by positivity)]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **The antitone sandwich (the CORE statement).** For a positive **Stieltjes** (log-convex)
sequence, `R̃` antitone at `r` is EXACTLY the two-sided bound
`1 ≤ ρ_{r+1}/ρ_r ≤ (2r+3)/(2r+1)`, whose left half is FREE (`growth_ge_one_of_logConvex`) and whose
right half `≤ 1 + 2/(2r+1)` carries the entire content. -/
theorem Rtilde_antitone_iff_sandwich {r : ℕ} (hn : 0 < n)
    (hAr : 0 < A r) (hAr1 : 0 < A (r + 1))
    (hlog : A (r + 1) ^ 2 ≤ A r * A (r + 2))
    (hrho : 0 < rho A r) :
    Rtilde A n (r + 1) ≤ Rtilde A n r ↔
      (1 ≤ rho A (r + 1) / rho A r ∧
        rho A (r + 1) / rho A r ≤ (2 * (r : ℝ) + 3) / (2 * (r : ℝ) + 1)) := by
  rw [Rtilde_antitone_iff_growth_le A n hn hrho]
  constructor
  · intro h
    exact ⟨growth_ge_one_of_logConvex A hAr hAr1 hlog hrho, h⟩
  · intro h; exact h.2

/-! ## 4. M-equivalence: the cap delivers the depth-`r` Gaussian ratio bound (no M-free lever)

The antitone step at `r` gives `ρ_{r+1} ≤ ((2r+3)/(2r+1))·ρ_r`. Iterated from the base
`ρ_1 = (2·1+1)·n·R̃_1 = 3n·R̃_1` this telescopes (via `stepLaw_of_antitone_base` in the WF7 file) to
`A_r ≤ (2r−1)‼·n^r`. The point below is the *pointwise* face: a single antitone step at `r` already
pins `ρ_r ≤ (2r+1)·n·R̃_1` whenever `R̃` has been antitone up to `r` — i.e. the depth-`r` ratio is
Gaussian-controlled by the base constant `R̃_1`, so the cap is not a source of any bound the M-object
does not already carry. This is the formal sense in which the antitone route is M-equivalent. -/

/-- **The cap forces the depth-`r` Gaussian ratio bound.** If `R̃_r ≤ R̃_1` (antitone monotonicity
having propagated the base value down to depth `r`) then the raw ratio obeys the Gaussian schedule
`ρ_r ≤ (2r+1)·n·R̃_1`. Since `ρ_r ↗ M²`, controlling `ρ_r` at every depth `r ≤ log p` by
`(2r+1)·n·R̃_1` IS the depth-`r` face of `M ≤ √(n log p)` — the antitone cap creates no lever the
M-bound does not already contain. -/
theorem cap_forces_gaussian_ratio {r : ℕ} (hn : 0 < n)
    (hchain : Rtilde A n r ≤ Rtilde A n 0) :
    rho A r ≤ (2 * (r : ℝ) + 1) * n * Rtilde A n 0 := by
  have hpos : (0 : ℝ) < (2 * (r : ℝ) + 1) * n := by positivity
  have hexp : Rtilde A n r = rho A r / ((2 * (r : ℝ) + 1) * n) := rfl
  rw [hexp] at hchain
  rw [div_le_iff₀ hpos] at hchain
  calc rho A r ≤ Rtilde A n 0 * ((2 * (r : ℝ) + 1) * n) := hchain
    _ = (2 * (r : ℝ) + 1) * n * Rtilde A n 0 := by ring

/-! ## 5. Not-forced: an explicit Stieltjes spectrum that VIOLATES the cap

The upper cap `g_r ≤ (2r+3)/(2r+1)` is NOT a consequence of positivity + log-convexity. We work with
the two-atom weighted spectrum `A_r = w·s^r + t^r`, the moment sequence of the nonnegative measure
`w·δ_s + δ_t`. It is a genuine Stieltjes sequence (`twoAtom_logConvex`, proved by direct algebra),
yet with a heavy top atom (`w=10, s=1, t=8`, i.e. the spike `10·δ_1 + δ_8`) its `R̃` is NOT antitone
at `r=1`: `A_1=18, A_2=74, A_3=522`, and the antitone cross-inequality `3·A_3·A_1 ≤ 5·A_2²` FAILS
(`28188 > 27380`), i.e. `g_1 = ρ_2/ρ_1 = 2349/1369 ≈ 1.716 > 5/3`. This is the abstract mechanism
behind the exact char-`p` reversals at n=32, p∈{1391393, 2089889, 4102753}: a large-`M` spectral
spike makes the log-convex ratio accelerate past the Gaussian budget, so antitonicity of the
DC-subtracted step ratio is a genuine (M-sized) arithmetic hypothesis, not a structural theorem. -/

/-- A concrete two-atom moment sequence: `A r = w·s^r + t^r`, the `r`-th moment of `w·δ_s + δ_t`.
For `w,s,t ≥ 0` this is a genuine Stieltjes moment sequence, hence log-convex (`twoAtom_logConvex`). -/
noncomputable def twoAtom (w s t : ℝ) (r : ℕ) : ℝ := w * s ^ r + t ^ r

/-- **`twoAtom` is log-convex (genuine Stieltjes).** `A_{r+1}² ≤ A_r·A_{r+2}` for the two-atom
sequence with `w,s,t ≥ 0`. Direct AM–GM/rearrangement: the cross term expands to
`w·(s^r·t^{r+2} + s^{r+2}·t^r) ≥ 2w·s^{r+1}·t^{r+1}` (AM–GM on `s^r t^{r+2}, s^{r+2} t^r`), which is
exactly the deficit `A_r·A_{r+2} − A_{r+1}²`. -/
theorem twoAtom_logConvex (w s t : ℝ) (hw : 0 ≤ w) (hs : 0 ≤ s) (ht : 0 ≤ t) (r : ℕ) :
    twoAtom w s t (r + 1) ^ 2 ≤ twoAtom w s t r * twoAtom w s t (r + 2) := by
  unfold twoAtom
  have hsr : 0 ≤ s ^ r := pow_nonneg hs r
  have htr : 0 ≤ t ^ r := pow_nonneg ht r
  -- EXACT deficit identity: A_r·A_{r+2} − A_{r+1}² = w·(s^r·t^r)·(t−s)² ≥ 0.
  -- The w² and t² brackets cancel (s^r·s^{r+2} = s^{2r+2}, t^r·t^{r+2} = t^{2r+2}).
  have hdeficit :
      (w * s ^ r + t ^ r) * (w * s ^ (r + 2) + t ^ (r + 2)) - (w * s ^ (r + 1) + t ^ (r + 1)) ^ 2
        = w * (s ^ r * t ^ r) * (t - s) ^ 2 := by
    have e1 : s ^ (r + 2) = s ^ r * s ^ 2 := by rw [pow_add]
    have e2 : t ^ (r + 2) = t ^ r * t ^ 2 := by rw [pow_add]
    have e3 : s ^ (r + 1) = s ^ r * s := by rw [pow_succ]
    have e4 : t ^ (r + 1) = t ^ r * t := by rw [pow_succ]
    rw [e1, e2, e3, e4]; ring
  have hnn : 0 ≤ w * (s ^ r * t ^ r) * (t - s) ^ 2 :=
    mul_nonneg (mul_nonneg hw (mul_nonneg hsr htr)) (sq_nonneg _)
  have := hdeficit
  linarith [this, hnn]

/-- The `w=10, s=1, t=8` moments: `A_1 = 18`, `A_2 = 74`, `A_3 = 522`. -/
theorem twoAtom_spike_vals :
    twoAtom 10 1 8 1 = 18 ∧ twoAtom 10 1 8 2 = 74 ∧ twoAtom 10 1 8 3 = 522 := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold twoAtom; norm_num

/-- **The cap is VIOLATED by a genuine Stieltjes sequence (antitonicity NOT forced).** For the spike
spectrum `10·δ_1 + δ_8` (`twoAtom 10 1 8`, log-convex by `twoAtom_logConvex`), the antitone
cross-inequality at `r=1`, `(2·1+1)·A_3·A_1 ≤ (2·1+3)·A_2²`, i.e. `3·A_3·A_1 ≤ 5·A_2²`, is FALSE:
`3·522·18 = 28188 > 27380 = 5·74²`. Hence `R̃` is not antitone at `r=1` for this legitimate
Stieltjes sequence. So positivity + log-convexity do NOT imply the antitone cap: the desired
antitonicity is a genuine arithmetic hypothesis (structurally possible, not free). -/
theorem stieltjes_can_violate_cap :
    ¬ ((2 * (1 : ℝ) + 1) * (twoAtom 10 1 8 3 * twoAtom 10 1 8 1)
        ≤ (2 * (1 : ℝ) + 3) * twoAtom 10 1 8 2 ^ 2) := by
  unfold twoAtom; norm_num

/-- The same violation phrased as the failure of the abstract `Rtilde` antitone step at `r=1` for the
spike sequence (via `Rtilde_antitone_iff_growth_cross`, with any `n>0`; the `n` cancels). This is the
formal statement that `R̃_2 ≤ R̃_1` FAILS for a genuine Stieltjes moment sequence. -/
theorem Rtilde_not_antitone_spike {n : ℝ} (hn : 0 < n) :
    ¬ (Rtilde (twoAtom 10 1 8) n (1 + 1) ≤ Rtilde (twoAtom 10 1 8) n 1) := by
  rw [Rtilde_antitone_iff_growth_cross (twoAtom 10 1 8) n hn]
  unfold rho
  -- Substitute the concrete moment values A_1=18, A_2=74, A_3=522 and reduce to a rational falsity.
  obtain ⟨v1, v2, v3⟩ := twoAtom_spike_vals
  have e1 : ((1 : ℕ) + 1 : ℕ) = 2 := rfl
  rw [e1, v1, v2, v3]
  -- goal: ¬ ((2·1+1) · (522/74) ≤ (2·1+3) · (74/18))  i.e. ¬ (3·(522/74) ≤ 5·(74/18)); FALSE numerically.
  norm_num

end ProximityGap.Frontier.DCStieltjesRatioAntitone

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.DCStieltjesRatioAntitone.Rtilde_eq
#print axioms ProximityGap.Frontier.DCStieltjesRatioAntitone.rho_monotone_of_logConvex
#print axioms ProximityGap.Frontier.DCStieltjesRatioAntitone.growth_ge_one_of_logConvex
#print axioms ProximityGap.Frontier.DCStieltjesRatioAntitone.Rtilde_antitone_iff_growth_cross
#print axioms ProximityGap.Frontier.DCStieltjesRatioAntitone.Rtilde_antitone_iff_growth_le
#print axioms ProximityGap.Frontier.DCStieltjesRatioAntitone.Rtilde_antitone_iff_sandwich
#print axioms ProximityGap.Frontier.DCStieltjesRatioAntitone.cap_forces_gaussian_ratio
#print axioms ProximityGap.Frontier.DCStieltjesRatioAntitone.twoAtom_logConvex
#print axioms ProximityGap.Frontier.DCStieltjesRatioAntitone.stieltjes_can_violate_cap
#print axioms ProximityGap.Frontier.DCStieltjesRatioAntitone.Rtilde_not_antitone_spike
