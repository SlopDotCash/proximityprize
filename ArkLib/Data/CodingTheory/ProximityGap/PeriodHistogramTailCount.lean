/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PeriodTailMarkov
import ArkLib.Data.CodingTheory.ProximityGap.CumulantGaussPeriodBound

/-!
# The explicit period-histogram tail count, DC-subtracted (#407)

`PeriodTailMarkov.card_filter_mul_le_sum_pow` is the abstract `r`-th order Markov step
(`#{b : T < a b}·T^r ≤ ∑_b (a b)^r`). This file *composes* it with the in-tree cumulant moment
identity `CumulantGaussPeriodBound.cumulant_eq` (`∑_{b≠0} ‖η_b‖^{2r} = q·E_r(G) − |G|^{2r}`) to
produce the concrete **far-frequency tail count** the EVT/floor route consumes:

> **`card_period_gt_mul_le_cumulant`** — for `0 < T`,
> `#{b ≠ 0 : ‖η_b‖² > T}·T^r ≤ q·E_r(G) − |G|^{2r}`,
>
> **`card_period_gt_le_cumulant_div`** — quotient form
> `#{b ≠ 0 : ‖η_b‖² > T} ≤ (q·E_r(G) − |G|^{2r}) / T^r`.

The mathematical content is the elementary identity `(‖η_b‖²)^r = ‖η_b‖^{2r}` — the histogram
variable `a_b = ‖η_b‖²` raised to the `r`-th Markov power *is* the `2r`-th period moment over the FAR
frequencies, so the Markov tail count is bounded by the **cumulant** (DC-subtracted) moment.

**Why DC-subtracted (the honest object).** The non-DC moment `∑_{b} ‖η_b‖^{2r} = q·E_r(G)` *includes*
the principal term `‖η_0‖^{2r} = |G|^{2r}`, which DOMINATES at the prize scale: `E_r ≥ |G|^{2r}/q`, and
the in-tree correction (commit `404c60988`, `prize-407-fresh-conjectures.md`) records that
`E_r ≫ Wick` for `n ≥ 64` at `r ≈ log q`, so the raw `q·E_r ≤ q·Wick` relaxation is FALSE / vacuous at
the prize. The genuinely-true prize input is the **DC-subtracted** `A_r := E_r − |G|^{2r}/q ≤ Wick`,
i.e. the cumulant `q·E_r − |G|^{2r} = q·A_r` bounded by `q·Wick`. The tail count proved here is stated
DIRECTLY against this DC-subtracted total, so under the correct hypothesis `A_r ≤ Wick` it gives the
NON-vacuous sub-exponential tail `#{b ≠ 0 : ‖η_b‖² > t·n} ≤ q·e^{−ct}`, whence `M ≤ √(c⁻¹·n·ln q)`.
(This file does NOT assume `A_r ≤ Wick`; the count is unconditional, the energy bound stays the open
content = BGK.)

**Non-vacuity.** Probed over proper 2-power subgroups `μ_n ⊊ F_p*`
(`scripts/probes/probe_period_tail_count.py`, `p = 193..12289`, `n = 16, 64`), the filtered set
`{b ≠ 0 : ‖η_b‖² > T}` is nonempty at the prize thresholds `T = n, 2n` (16–4096 bad frequencies), so
the inequality bounds a real tail, not a trivial `0 ≤ S`.

Issue #407.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.CumulantGaussPeriodBound
open ArkLib.ProximityGap.PeriodTailMarkov

namespace ArkLib.ProximityGap.PeriodHistogramTailCount

variable {ι : Type*} [DecidableEq ι]

/-- **Finset-general Markov tail bound (`r`-th moment).** For `a : ι → ℝ` nonnegative on `s`, `0 < T`,
the number of `s`-indices with `a b > T` times `T^r` is at most the `r`-th power-sum over `s`:
`#{b ∈ s : T < a b}·T^r ≤ ∑_{b ∈ s} (a b)^r`. The finset analogue of `card_filter_mul_le_sum_pow`
(which is the `s = univ` case); needed to localize the count to the *far* frequencies `b ≠ 0` (a
proper subfinset `univ.erase 0`), so the bound lands on the DC-subtracted cumulant total. -/
theorem card_filter_mul_le_sum_pow_finset (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (T : ℝ) (hT : 0 < T) (r : ℕ) :
    (((s.filter (fun b => T < a b)).card : ℝ)) * T ^ r ≤ ∑ b ∈ s, (a b) ^ r := by
  set t := s.filter (fun b => T < a b) with ht
  calc ((t.card : ℝ)) * T ^ r
      = ∑ _b ∈ t, T ^ r := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b ∈ t, (a b) ^ r := by
        refine Finset.sum_le_sum (fun b hb => ?_)
        have hbT : T < a b := (Finset.mem_filter.mp hb).2
        exact pow_le_pow_left₀ hT.le hbT.le r
    _ ≤ ∑ b ∈ s, (a b) ^ r :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ s)
          (fun i hi _ => pow_nonneg (ha i hi) r)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The explicit far-frequency tail count (DC-subtracted / cumulant form).** For a primitive `ψ`,
every threshold `0 < T` and every order `r`, the number of NONZERO frequencies whose period mass
exceeds `T` satisfies
  `#{b ≠ 0 : ‖η_b‖² > T}·T^r ≤ q·E_r(G) − |G|^{2r}`.

This is the bridge whose prose appears in `PeriodTailMarkov` ("instantiated with `a_b = |η_b|²` ...
`#{b≠0 : |η_b|² > T} ≤ q·A_r / T^r`"), now stated against the DC-subtracted total `q·A_r = q·E_r −
|G|^{2r}` — the object that is TRUE at the prize scale (the raw `q·E_r` overshoots Wick by the
principal term; see file header).

Proof: instantiate the finset-general Markov bound (`card_filter_mul_le_sum_pow_finset`) at
`s = univ.erase 0`, `a_b = ‖η_b‖²`, rewrite `(‖η_b‖²)^r = ‖η_b‖^{2r}`, and apply the cumulant identity
`cumulant_eq`. The histogram variable raised to the Markov power is exactly the `2r`-th far-frequency
period moment. Unconditional; the open content is the energy bound `A_r ≤ Wick` (= BGK). -/
theorem card_period_gt_mul_le_cumulant {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (T : ℝ) (hT : 0 < T) (r : ℕ) :
    (((Finset.univ.erase (0 : F)).filter
        (fun b => T < ‖eta ψ G b‖ ^ 2)).card : ℝ) * T ^ r
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  have hmarkov := card_filter_mul_le_sum_pow_finset (Finset.univ.erase (0 : F))
    (fun b => ‖eta ψ G b‖ ^ 2) (fun i _ => sq_nonneg _) T hT r
  have hpow : ∀ b : F, (‖eta ψ G b‖ ^ 2) ^ r = ‖eta ψ G b‖ ^ (2 * r) := by
    intro b; rw [← pow_mul, Nat.mul_comm]
  rw [Finset.sum_congr rfl (fun b _ => hpow b)] at hmarkov
  rw [cumulant_eq hψ G r] at hmarkov
  exact hmarkov

/-- **The far-frequency tail count, quotient form.** For `0 < T`, `0 < r`,
`#{b ≠ 0 : ‖η_b‖² > T} ≤ (q·E_r(G) − |G|^{2r}) / T^r`. The direct DC-subtracted `q·A_r / T^r` bridge
as stated in the `PeriodTailMarkov` docstring; with the open input `A_r ≤ Wick` and `T = t·n`,
`r ≈ ln q`, this is the sub-exponential far-frequency tail count. -/
theorem card_period_gt_le_cumulant_div {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (T : ℝ) (hT : 0 < T) (r : ℕ) :
    (((Finset.univ.erase (0 : F)).filter
        (fun b => T < ‖eta ψ G b‖ ^ 2)).card : ℝ)
      ≤ ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) / T ^ r := by
  have hTr : (0 : ℝ) < T ^ r := pow_pos hT r
  rw [le_div_iff₀ hTr]
  exact card_period_gt_mul_le_cumulant hψ G T hT r

/-- **Tail count under the DC-subtracted energy bound (`A_r ≤ Wick`).** Supplying the genuinely-open,
true-at-prize input `q·E_r − |G|^{2r} ≤ q·(2r−1)‼·|G|^r` (= `A_r ≤ Wick`, the cumulant bound) turns the
count into the Wick form `#{b ≠ 0 : ‖η_b‖² > T}·T^r ≤ q·(2r−1)‼·|G|^r`. Stated as a consumer of the
named in-tree `CumulantEnergyBound` so the open content is explicit and the bound is non-vacuous at the
prize (unlike the raw `q·E_r ≤ q·Wick`, which is false for `n ≥ 64`). -/
theorem card_period_gt_mul_le_wick_of_cumulantBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (T : ℝ) (hT : 0 < T) (r : ℕ) (hWick : CumulantEnergyBound G r) :
    (((Finset.univ.erase (0 : F)).filter
        (fun b => T < ‖eta ψ G b‖ ^ 2)).card : ℝ) * T ^ r
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  refine le_trans (card_period_gt_mul_le_cumulant hψ G T hT r) ?_
  exact hWick

end ArkLib.ProximityGap.PeriodHistogramTailCount

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.PeriodHistogramTailCount.card_filter_mul_le_sum_pow_finset
#print axioms ArkLib.ProximityGap.PeriodHistogramTailCount.card_period_gt_mul_le_cumulant
#print axioms ArkLib.ProximityGap.PeriodHistogramTailCount.card_period_gt_le_cumulant_div
#print axioms ArkLib.ProximityGap.PeriodHistogramTailCount.card_period_gt_mul_le_wick_of_cumulantBound
