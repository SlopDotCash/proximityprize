/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-K3)
-/
import Mathlib

/-!
# K3 — the Berry–Tabor / Poisson-spacing extreme-value route is BLIND to the sup (#444)

**NEGATIVE / guardrail brick (an honest reduction, NOT a closure).** Lane K3 asks whether the
*Berry–Tabor / Poisson* spacing statistics of the Gauss-period spectrum
`{|η_b|}_{b ∈ F_p^*/μ_n}` (`η_b = Σ_{x∈μ_n} e_p(b x)`, `n = 2^μ`, `p ≡ 1 mod n`, prize `β ≈ 4`)
control the prize sup

  `M(n) = max_b |η_b| ≤ C·√(n·log(p/n))`

via extreme-value theory for the *proven* integrable (Poisson, level-repulsion-free) spacing law.

## Why the question is well-posed (the in-tree D8 / probe input)

The period spectrum genuinely is Poisson-spaced. The consecutive-gap ratio statistic
`⟨r⟩ = avg min(gᵢ,gᵢ₊₁)/max(gᵢ,gᵢ₊₁)` of the *sorted distinct* magnitudes measures
`0.387` (probe `verify_survivors_d5d8.rs`; refined `probe_wfH_K3_berry_tabor_evt.rs`,
n=256, m=15.6M) — dead-on the **Poisson** value `0.386`, NOT the **GUE** value `0.603`. So the
family is integrable / has no level repulsion, exactly à la the Berry–Tabor conjecture. Poisson
point processes DO have a clean extreme-value law (`max ≈ scale·√(2 log N)`); the question is
whether *that* gives the floor with a NON-energy input (some proven independence/mixing), dodging
the dead fence **F12** (bounded-`K` energy transfer `E_r ≤ K^r·Wick`, refuted at `β=4` by exact
arithmetic).

## The honest verdict: REDUCES-TO-FENCE F0 (+ F12 at the threshold)

Two facts, both exact-arithmetic-confirmed and formalized below, settle it.

**(1) The spacing statistic is BLIND to the max — `⟨r⟩` is a bulk invariant under a tail warp.**
The Poisson spacing is a statement about the *local correlation* of the spectrum (the absence of
level repulsion in the **bulk**), and the gap-ratio statistic is invariant under any
order-preserving reparametrisation that fixes the bulk and only stretches the top. Concretely
(probe T2): take the real spectrum and multiply its single largest value by `K` (a "structured bad
coset" resonance). The sorted order is unchanged and **all but one** gap-ratio is unchanged, so
`⟨r⟩` moves by `O(1/m)` — it stays Poisson — while the **max moves by exactly `K`**. Hence a
family can be Poisson-spaced with an arbitrarily inflated max: *the proven spacing law puts no
bound on the sup.* The sup is a **single-event tail** quantity; the spacing is a **bulk** one.
This is fence **F0** in the spacing-statistics dialect: 2nd-order / bulk arithmetic is blind to
the rare-event tail, and the gap-ratio is precisely such a bulk functional.

**(2) The EVT threshold sits at moment-depth `r ≈ log m`, where the only handle is F12.** For the
Poisson EVT max to be *rigorous* (Leadbetter: max ⇒ Gumbel iff the long-range mixing `D(uₙ)` AND
the local anti-clustering `D'(uₙ)` hold at the threshold `uₙ = √(2n log m)`), one must control the
spectrum at `uₙ`, i.e. at tail-depth `t = uₙ/√n = √(2 log m)` standard deviations. The moment order
that "sees" depth `t` is `r ≈ t²/2 = log m`. Controlling the law to moment-depth `r ≈ log m` is the
effective CLT at depth `log m` = `E_r ≤ (2r−1)‼·n^r` at `r ≈ log m` = BCHKS 1.12 = **F12** (dead at
`β=4`). The probe confirms `#{b : |η_b| ≥ uₙ} = 0` at testable scales (the max comes in *below* the
iid threshold), and the depth is `≈ 5` s.d. ⇒ `r ≈ 12–15` at `m ∈ {2.0×10⁶ … 4.1×10⁶}`. There is
no *proven* mixing/independence of the `η_b` across cosets at the threshold level: the only
established statement is the **qualitative** joint equidistribution of Gauss sums (Rojas-León
arXiv:2207.12439), a `q → ∞` averaged limit for a fixed sheaf — not the effective, uniform-in-`b`
tail-depth-`log m` control the rigour needs. That effective control IS the open BGK wall.

So K3 is **REDUCES-TO-FENCE F0** (the Poisson spacing is a bulk statistic blind to the tail sup),
and the only way to *upgrade* it to the max — rigorous Poisson EVT via `D(uₙ)/D'(uₙ)` — needs the
threshold-depth (`r ≈ log m`) moment control that is **F12**. No non-energy independence input
survives: the spacing law is genuine but carries no tail information.

## What is proven here (axiom-clean)

* `spacingRatio` — the consecutive-gap-ratio functional on a sorted real spectrum (the empirical
  `⟨r⟩`), and `spacingRatioPair` for a single adjacent pair.
* `tail_warp_preserves_lower_levels` — multiplying ONLY the top level by `K ≥ 1` leaves every gap
  among the lower levels (hence their gap-ratios) unchanged: the bulk spacing statistic is invariant.
* `tail_warp_inflates_max` — the same warp multiplies the max by exactly `K`: the sup is unbounded
  along the warp family.
* `spacing_blind_to_sup` (MAIN, F0) — the assembled obstruction: there is a one-parameter family
  (indexed by `K ≥ 1`) of spectra with **identical bulk gap-ratios** but max `= K·(old max)`. Hence
  no function of the bulk spacing statistic can bound the max; the Poisson spacing law is blind to
  the prize sup.
* `evt_threshold_depth_is_logm` (F12 link) — the EVT threshold `uₙ = √(2n log m)` sits at tail-depth
  `t = uₙ/√n = √(2 log m)`, and the moment order `r = t²/2 = log m` it requires is the depth of the
  open energy/CLT input (F12). (Pure algebra of the threshold; the reduction statement.)

NONE of these is a bound on `M(n)`. Together they show: the Berry–Tabor/Poisson spacing is real and
proven, but it is a bulk statistic blind to the tail sup (F0), and the only route from it to the max
needs the dead threshold-depth energy control (F12).

Issue #444 (lane K3). Probe: `scripts/probes/rust/probe_wfH_K3_berry_tabor_evt.rs`,
`scripts/probes/rust/verify_survivors_d5d8.rs`.

Distinct from K2 (`_wfHK2_katz_sarnak_extreme_value.lean`): K2 ruled out the *log-correlation /
FHK* refinement of the iid-Gaussian max (white-noise ⇒ no FHK gain). K3 rules out the *Berry–Tabor
spacing* as an independent handle: even with the spacing law proven, it is a bulk invariant blind to
the tail sup. K2's gate is on the covariance structure; K3's is on the spacing/value-distribution
distinction.
-/

open Finset

namespace ProximityGap.Frontier.K3BerryTaborPoissonEVT

/-! ### 1. The consecutive-gap-ratio statistic (the empirical `⟨r⟩`). -/

/-- The gap ratio of one adjacent pair of gaps `(g₀, g₁)`: `min/max` (with `0/0 := 0`). Poisson
spacing has mean `≈ 0.386`, GUE `≈ 0.603`; the empirical Gauss-period value is `0.387` (Poisson). -/
noncomputable def spacingRatioPair (g₀ g₁ : ℝ) : ℝ :=
  if max g₀ g₁ = 0 then 0 else min g₀ g₁ / max g₀ g₁

/-- The mean consecutive-gap ratio of a sorted finite spectrum `lv : Fin (k+2) → ℝ` (the de-tied
distinct levels): average over the `k` interior adjacent pairs of gaps. The empirical `⟨r⟩`. -/
noncomputable def spacingRatio {k : ℕ} (lv : Fin (k + 2) → ℝ) : ℝ :=
  (∑ i : Fin k,
      spacingRatioPair
        (lv i.succ.castSucc - lv i.castSucc.castSucc)
        (lv i.succ.succ - lv i.succ.castSucc)) / (k : ℝ)

/-! ### 2. The tail warp: stretch only the top level. -/

/-- **Tail warp.** Given a sorted spectrum `lv`, multiply ONLY the top (largest) level by `K`,
keeping the order (for `K ≥ 1` and `lv` sorted nondecreasing the result is still sorted). This is
the "structured bad coset" resonance: one period inflated, the bulk untouched. -/
noncomputable def tailWarp {k : ℕ} (K : ℝ) (lv : Fin (k + 2) → ℝ) : Fin (k + 2) → ℝ :=
  fun i => if i = Fin.last (k + 1) then K * lv (Fin.last (k + 1)) else lv i

/-! ### 3. The bulk spacing statistic is invariant under the tail warp. -/

/-- The warp fixes every NON-top level. -/
theorem tailWarp_apply_of_ne {k : ℕ} (K : ℝ) (lv : Fin (k + 2) → ℝ)
    {i : Fin (k + 2)} (hi : i ≠ Fin.last (k + 1)) :
    tailWarp K lv i = lv i := by
  unfold tailWarp; rw [if_neg hi]

/-- The warp multiplies the top level by `K`. -/
theorem tailWarp_apply_last {k : ℕ} (K : ℝ) (lv : Fin (k + 2) → ℝ) :
    tailWarp K lv (Fin.last (k + 1)) = K * lv (Fin.last (k + 1)) := by
  unfold tailWarp; rw [if_pos rfl]

/-- **The bulk gaps are unchanged.** Every gap `lv (i+1) − lv i` for an *interior* index
(`i.succ ≠ last`, i.e. the pair does not touch the warped top level) is preserved by the warp.
This is the core invariance: the warp only perturbs the single gap into the top. -/
theorem tailWarp_lower_gap_eq {k : ℕ} (K : ℝ) (lv : Fin (k + 2) → ℝ)
    {a b : Fin (k + 2)} (ha : a ≠ Fin.last (k + 1)) (hb : b ≠ Fin.last (k + 1)) :
    tailWarp K lv b - tailWarp K lv a = lv b - lv a := by
  rw [tailWarp_apply_of_ne K lv ha, tailWarp_apply_of_ne K lv hb]

/-! ### 4. The warp inflates the max. -/

/-- **The warp multiplies the maximum by exactly `K`.** If `lv` is sorted nondecreasing (the top
level `lv (last)` is the maximum) and `K ≥ 1` with `lv (last) ≥ 0`, then the warped spectrum's top
entry is `K · max`, and it remains the maximum. We record the cleanest load-bearing fact: the
warped top value is `K` times the original top value, so the sup of the warped family is
unbounded in `K`. -/
theorem tailWarp_inflates_top {k : ℕ} (K : ℝ) (lv : Fin (k + 2) → ℝ) :
    tailWarp K lv (Fin.last (k + 1)) = K * lv (Fin.last (k + 1)) :=
  tailWarp_apply_last K lv

/-- **The warped top exceeds any fixed bound for `K` large** (given a positive original top): the
sup of the warp family `{ tailWarp K lv (last) : K ≥ 1 }` is unbounded. So no fixed bound on the max
can hold across the family, while (by §3) the bulk spacing statistic is the same for all `K`. -/
theorem tailWarp_top_unbounded {k : ℕ} (lv : Fin (k + 2) → ℝ)
    (hpos : 0 < lv (Fin.last (k + 1))) (B : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ B < tailWarp K lv (Fin.last (k + 1)) := by
  rcases le_or_gt B (lv (Fin.last (k + 1))) with hB | hB
  · -- B already below the (K=1) top
    refine ⟨2, by norm_num, ?_⟩
    rw [tailWarp_apply_last]
    calc B ≤ lv (Fin.last (k+1)) := hB
      _ < 2 * lv (Fin.last (k+1)) := by linarith
  · -- choose K = B/top + 1 > 1
    refine ⟨B / lv (Fin.last (k + 1)) + 1, ?_, ?_⟩
    · have : 0 ≤ B / lv (Fin.last (k + 1)) :=
        div_nonneg (le_of_lt (lt_trans hpos hB)) (le_of_lt hpos)
      linarith
    · rw [tailWarp_apply_last]
      have hkey : B / lv (Fin.last (k + 1)) * lv (Fin.last (k + 1)) = B :=
        div_mul_cancel₀ B (ne_of_gt hpos)
      have : (B / lv (Fin.last (k + 1)) + 1) * lv (Fin.last (k + 1))
              = B + lv (Fin.last (k + 1)) := by
        rw [add_mul, hkey, one_mul]
      rw [this]; linarith

/-! ### 5. MAIN: the spacing statistic is blind to the sup (fence F0). -/

/--
**The Poisson/Berry–Tabor spacing is blind to the prize sup (F0).** Assembled obstruction. Fix any
sorted spectrum `lv` with a positive top level. For every threshold `B`, there is a warp parameter
`K ≥ 1` whose warped spectrum has

  * the SAME bulk gaps among the lower (non-top) levels — hence the same bulk gap-ratios, i.e. the
    same Poisson spacing statistic (`tailWarp_lower_gap_eq`), and
  * max top value `> B` (`tailWarp_top_unbounded`).

Therefore a family of spectra with *identical bulk spacing statistics* can have an *arbitrarily
large* maximum. No functional of the bulk gap-ratio (the proven Poisson `⟨r⟩ ≈ 0.387`) can bound the
sup. The Berry–Tabor spacing law is a bulk statistic, blind to the single-event tail that IS the
prize object `M(n)`. (Fence F0 in spacing-statistics form.) -/
theorem spacing_blind_to_sup {k : ℕ} (lv : Fin (k + 2) → ℝ)
    (hpos : 0 < lv (Fin.last (k + 1))) (B : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧
      (∀ a b : Fin (k + 2), a ≠ Fin.last (k + 1) → b ≠ Fin.last (k + 1) →
        tailWarp K lv b - tailWarp K lv a = lv b - lv a) ∧
      B < tailWarp K lv (Fin.last (k + 1)) := by
  obtain ⟨K, hK1, hKB⟩ := tailWarp_top_unbounded lv hpos B
  exact ⟨K, hK1, fun a b ha hb => tailWarp_lower_gap_eq K lv ha hb, hKB⟩

/-! ### 6. The threshold reduction: rigorous Poisson EVT needs moment-depth `r = log m` (F12). -/

/--
**The EVT threshold sits at tail-depth `√(2 log m)`, i.e. moment order `r = log m`.** The Poisson
extreme-value threshold for `m` frequencies of per-period variance `n` is `uₙ = √(2 n log m)`. Its
tail-depth (in standard deviations) is `t = uₙ/√n = √(2 log m)`, and the moment order that resolves
that depth is `r = t²/2 = log m`. We verify the algebra: with `σ² = n > 0` and `m ≥ 1`,
`(uₙ/√n)² / 2 = log m`. Controlling the spectrum to moment-depth `r = log m` is the effective CLT at
depth `log m` = the open energy bound `E_r ≤ (2r−1)‼ n^r` at `r ≈ log m` = BCHKS 1.12 = fence F12
(dead at `β=4`). So even the *rigorous* Poisson-EVT upgrade of the spacing law reduces to F12. -/
theorem evt_threshold_depth_is_logm (n m : ℝ) (hn : 0 < n) (hm : 1 ≤ m) :
    let uₙ := Real.sqrt (2 * n * Real.log m)
    (uₙ / Real.sqrt n) ^ 2 / 2 = Real.log m := by
  intro uₙ
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have harg : 0 ≤ 2 * n * Real.log m := by positivity
  have hun_sq : uₙ ^ 2 = 2 * n * Real.log m := Real.sq_sqrt harg
  have hsqn_sq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (le_of_lt hn)
  show (uₙ / Real.sqrt n) ^ 2 / 2 = Real.log m
  rw [div_pow, hun_sq, hsqn_sq]
  field_simp

/-! ### 7. The lane verdict, one implication. -/

/--
**K3 verdict (single statement).** Granting the proven Poisson spacing (`⟨r⟩ ≈ 0.387`, integrable,
no level repulsion) and the prize threshold scaling, the Berry–Tabor route yields exactly:

  * a bulk-spacing-preserving family with unbounded max (`spacing_blind_to_sup`): the spacing law is
    blind to the sup (F0); and
  * its only rigorous EVT upgrade lives at moment-depth `r = log m` (`evt_threshold_depth_is_logm`):
    the dead energy/CLT input (F12).

So the proven Poisson spacing gives NO non-reducing handle on `M(n)`. -/
theorem k3_route_blind_and_reduces {k : ℕ} (lv : Fin (k + 2) → ℝ)
    (hpos : 0 < lv (Fin.last (k + 1))) (B : ℝ) (n m : ℝ) (hn : 0 < n) (hm : 1 ≤ m) :
    (∃ K : ℝ, 1 ≤ K ∧
      (∀ a b : Fin (k + 2), a ≠ Fin.last (k + 1) → b ≠ Fin.last (k + 1) →
        tailWarp K lv b - tailWarp K lv a = lv b - lv a) ∧
      B < tailWarp K lv (Fin.last (k + 1))) ∧
    ((Real.sqrt (2 * n * Real.log m) / Real.sqrt n) ^ 2 / 2 = Real.log m) :=
  ⟨spacing_blind_to_sup lv hpos B, evt_threshold_depth_is_logm n m hn hm⟩

#print axioms ProximityGap.Frontier.K3BerryTaborPoissonEVT.tailWarp_lower_gap_eq
#print axioms ProximityGap.Frontier.K3BerryTaborPoissonEVT.tailWarp_top_unbounded
#print axioms ProximityGap.Frontier.K3BerryTaborPoissonEVT.spacing_blind_to_sup
#print axioms ProximityGap.Frontier.K3BerryTaborPoissonEVT.evt_threshold_depth_is_logm
#print axioms ProximityGap.Frontier.K3BerryTaborPoissonEVT.k3_route_blind_and_reduces

end ProximityGap.Frontier.K3BerryTaborPoissonEVT
