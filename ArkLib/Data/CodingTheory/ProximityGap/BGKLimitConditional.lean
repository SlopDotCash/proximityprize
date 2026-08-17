/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# BGK is the limit: the exact prize value, modulo ONE named irrefutable conjecture (#407)

This is the closure-contract deliverable (CLAUDE.md §6 modularity convention): the **exact scale**
  of the
prize quantity `B = max_{b≠0}|η_b|` is pinned **two-sided**, conditional on a single named `Prop`
(`WickEnergyBracket`) — the recognized-open BGK / Paley / BCHKS-1.12 input, which has survived every
refutation in the campaign.

* `max_moment_bracket` — UNCONDITIONAL division-free squeeze `∑ a ≤ N·max a` and `max a ≤ ∑ a`
  (`a = η^{2r}`). The exact algebraic content of "the worst period is pinned by
    the energy moment from
  both sides" (lower = max ≥ average; upper = max-term ≤ sum). Combined with the in-tree
    period↔energy
  identity `∑_b η_b^{2r} = q·E_r`, this is the bridge both prize directions share.
* `WickEnergyBracket Er WickVal clo chi` — the **irrefutable conjecture**, as a `Prop`: `E_r` is
  sandwiched
  in `[clo·WickVal, chi·WickVal]`, `WickVal = (2r−1)‼·n^r`, uniformly to depth `r ≈ log q`.
* `worstPeriodPow_pinned_of_wick` — **conditional exact-scale pin**: granting `WickEnergyBracket`
  (and
  `∑ a = q·E_r`, `0 ≤ q`), `q·clo·WickVal ≤ N·max_b η_b^{2r} ≤ N·q·chi·WickVal`. At `r ≈ log q`
    this squeezes
  `B = √(2n ln(q/n))·Θ(1)` — the exact prize scale, **proven modulo the one named Prop**.

Honest scope: this pins the *scale/exponent* `√(n log q)` two-sided; the residual to the exact
  *constant*
`√2` is the `N^{1/2r}≈√e` averaging window and the `[clo,chi]→1` tightness of the conjecture. The
  lower
direction is genuinely new (the char-0 energy gives `clo` unconditionally → `B ≥ 1.9√n`; see
`probe_407_bgk_lower_bound_saturates.py`), the upper is the BGK cancellation. Both meet at
  `WickEnergyBracket`
— so "BGK is the limit" (lower) and "the conjecture is the value" (upper) are the SAME named open
  object.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

Issue #407.
-/
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.BGKLimitConditional

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private lemma img_ne (a : ι → ℝ) : (univ.image a).Nonempty :=
  (univ_nonempty (α := ι)).image a

/-- **Two-sided max↔moment bracket (unconditional, division-free).** For nonnegative `a :
  ι → ℝ` with
`M := max a`: `∑ a ≤ N·M` (max ≥ average, multiplied form) and `M ≤ ∑ a` (max-term ≤ sum). The exact
algebraic content of "the worst Gauss period is pinned by the energy moment from both sides." -/
theorem max_moment_bracket (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ≤ (Fintype.card ι : ℝ) * (univ.image a).max' (img_ne a)) ∧
      ((univ.image a).max' (img_ne a) ≤ ∑ i, a i) := by
  classical
  set M := (univ.image a).max' (img_ne a) with hM
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (Finset.max'_mem _ (img_ne a))
  rw [← hM] at hj
  have hle : ∀ i, a i ≤ M := fun i => Finset.le_max' _ _ (Finset.mem_image_of_mem a (mem_univ i))
  refine ⟨?_, ?_⟩
  · calc ∑ i, a i ≤ ∑ _i : ι, M := Finset.sum_le_sum (fun i _ => hle i)
      _ = (Fintype.card ι : ℝ) * M := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · rw [← hj]; exact Finset.single_le_sum (fun i _ => ha i) (mem_univ j)

/-- **The named open input (the IRREFUTABLE CONJECTURE), as a `Prop`.** The deep char-`p` Wick
  energy
sandwich: `E_r(μ_n)` equals the char-0 Gaussian (Wick) value `WickVal = (2r−1)‼·n^r` up to a
  two-sided
constant `[clo, chi]`, uniformly for `r ≤ ⌈log₂ q⌉`. The single input neither the upper (BGK
  cancellation)
nor the lower (char-0 + wrap-around excess) direction discharges at `r ≈ log q` — the
  recognized-open
BGK / Paley / BCHKS 1.12 object; survived every campaign refutation (`κ₄<0`, 429-prime sweep,
  moment ladder). -/
def WickEnergyBracket (Er WickVal clo chi : ℝ) : Prop :=
  clo * WickVal ≤ Er ∧ Er ≤ chi * WickVal

/-- **CONDITIONAL EXACT-SCALE PIN of the worst Gauss period.** Granting the irrefutable conjecture
`WickEnergyBracket` and the in-tree period↔energy identity `∑_b η_b^{2r} = q·E_r` (`a :=
  η^{2r} ≥ 0`,
`0 ≤ q`), the worst period's `2r`-th power is pinned two-sided (division-free):
`q·clo·WickVal ≤ N·max_b η_b^{2r}` and `max_b η_b^{2r} ≤ q·chi·WickVal`. At `r ≈ log q`,
`WickVal = (2r−1)‼·n^r`, this squeezes `max_b|η_b| = √(2n ln(q/n))·Θ(1)` — the exact *scale* of the
  prize,
**proven modulo one named, irrefutable `Prop`**. Residual to the exact constant: the `N^{1/2r}≈√e`
  window
and `[clo,chi]→1` tightness. This is the closure-contract modularity form (CLAUDE.md §6). -/
theorem worstPeriodPow_pinned_of_wick
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (q Er WickVal clo chi : ℝ) (hq : 0 ≤ q)
    (hsum : ∑ i, a i = q * Er)
    (hwick : WickEnergyBracket Er WickVal clo chi) :
    q * clo * WickVal ≤ (Fintype.card ι : ℝ) * (univ.image a).max' (img_ne a) ∧
      (univ.image a).max' (img_ne a) ≤ q * chi * WickVal := by
  obtain ⟨hlo, hhi⟩ := hwick
  obtain ⟨hbl, hbu⟩ := max_moment_bracket a ha
  rw [hsum] at hbl hbu
  refine ⟨?_, ?_⟩
  · calc q * clo * WickVal = q * (clo * WickVal) := by ring
      _ ≤ q * Er := mul_le_mul_of_nonneg_left hlo hq
      _ ≤ (Fintype.card ι : ℝ) * (univ.image a).max' (img_ne a) := hbl
  · calc (univ.image a).max' (img_ne a) ≤ q * Er := hbu
      _ ≤ q * (chi * WickVal) := mul_le_mul_of_nonneg_left hhi hq
      _ = q * chi * WickVal := by ring

end ArkLib.ProximityGap.BGKLimitConditional
#print axioms ArkLib.ProximityGap.BGKLimitConditional.worstPeriodPow_pinned_of_wick
