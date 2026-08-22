/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfL3_char0_prize_moment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS5_theta_count_wick

/-!
# wf-S5↔L3 weld: the UNCONDITIONAL below-girth char-`p` prize transfer (#444, lane wf-S5/L3)

## What this file welds (and why it is not redundant)

The energy route to the per-frequency prize has TWO proven halves that, on the **unconditional**
(no spurious mass) corner, were never theorem-connected:

* **wf-L3** (`_wfL3_char0_prize_moment.lean`) proves the char-`0` prize moment bound
  `char0_prize_moment_bound_sq`: from the formal-period moment identity `M^{2r} ≤ Q · E(2r)` and the
  Lam–Leung char-`0` energy bound `E(2r) = zeroSumCount G (2r) ≤ (2r−1)‼·n^r`, the saddle yields
  `M² ≤ 2e·|G|·r`. Its docstring names the **char-`p` transfer** as "the sole gap": the char-`0`
  energy bound transfers to `F_p` only while no short cyclotomic `±1`-relation vanishes mod `p`.

* **wf-S5/S6** localize that transfer precisely: char-`p` additive `2r`-energy equals the char-`0`
  Wick value EXACTLY when the spurious mass is zero (girth `> 2r`, i.e. `p` above the cyclotomic
  threshold `(2r)^{n/2}`); `_wfS5_theta_count_wick.energy_eq_wick_when_no_spur` and
  `_wfS6_toric_config_betti.energy_charp_eq_char0_of_no_spur` both state this no-spur identity.

NO file composes them. wf-L3 produces a char-`0` prize bound from a char-`0` energy; wf-S5/S6 produce
a char-`p` = char-`0` energy *identity* in the no-spur regime — but the char-`p` prize conclusion that
falls out of feeding the second into the first was never written. This file writes it: in the no-spur
regime the **char-`p`** formal-period sup obeys the prize √-shape `M² ≤ 2e·n·r` with **no conjectural
input** (no `ThetaShellGeometric`, no measured constant). The opus wf-S5↔S1 weld handles the *geometric*
(conjectural-`ThetaShellGeometric`) corner; this is the disjoint *unconditional* (spur = 0) corner.

## Honest scope — this is NOT a CORE closure

The no-spur hypothesis `E_charp(r) = zeroSumCount G (2r)` is UNCONDITIONALLY TRUE only while
`p > (2r)^{n/2}` (the cyclotomic-norm girth). At the prize scale (`n = 2^30`, `q = 2^158`,
`r ≈ ln q ≈ 110`) this threshold is `(220)^{2^29}` — astronomically larger than `q`, so the no-spur
regime EXCLUDES the prize depth. The probe (`probe_nospur_prize_weld.py`) exhibits the boundary
directly: at `n=8, p=17, r=2` the threshold `4^4=256 > 17` is violated, spurious mass appears
(`E_charp = 264 > 168 = E_char0`), and the char-`0` bound is exceeded — exactly the BGK wall. So this
theorem covers `r < ½·log_{2r} p` (small `r` / large `p`) and is provably silent at the prize regime.
What it DOES contribute: it makes "the char-`0` prize bound transfers char-`p` **unconditionally below
the girth**" a single citable theorem, sharpening the wf-L3 "sole gap" remark into an exact
hypothesis (`spur = 0`) with the open content isolated to "`spur = 0` fails at prize depth".

NON-MOMENT in the prize sense (the open content is the cyclotomic girth / short-relation count, not an
average); EXTEND-proven (consumes `char0_prize_moment_bound_sq` and the no-spur energy identity
verbatim); the ONLY new content is the substitution of the no-spur identity into the char-`0` bound.
No capacity / beyond-Johnson / cliff-at-`n/2` / `δ*→0` claim — the constant `2e` and the law `n·r` are
the proven char-`0` shape, asserted ONLY on the spur-free corner.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

set_option linter.style.longLine false


open Finset Nat
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.Frontier.WFS5L3NoSpur

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- **THE UNCONDITIONAL BELOW-GIRTH PRIZE TRANSFER (squared form).**

Let `G ⊆ μ_{2^k}` (`k ≥ 1`) in a characteristic-zero field, and let `Echarp : ℕ → ℕ` be the char-`p`
additive `2r`-energy of the corresponding thin subgroup. Suppose:

* `hnospur`: the no-spur identity `Echarp r = zeroSumCount G (2r)` (TRUE while `p > (2r)^{n/2}`;
  this is `wfS5.energy_eq_wick_when_no_spur` / `wfS6.energy_charp_eq_char0_of_no_spur`); and
* `hmoment`: the formal-period moment identity `M^{2r} ≤ Q · Echarp r` (the char-`p`
  `subgroup_gaussSum_moment` ∘ `single_le_sum`; field-independent counting).

Then at the optimal depth `r ≥ max(1, log Q)` the **char-`p`** per-frequency sup obeys the prize
square-root shape `M² ≤ 2e·|G|·r`, with NO conjectural input. The whole open content is folded into
`hnospur` (which FAILS at the prize depth — see the file docstring / probe). -/
theorem prize_sq_of_no_spur {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    (Echarp : ℕ → ℕ) {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hnospur : Echarp r = zeroSumCount G (2 * r))
    (hmoment : M ^ (2 * r) ≤ Q * (Echarp r : ℝ)) :
    M ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) := by
  -- rewrite the char-p moment identity into the char-0 zeroSumCount, then invoke wf-L3 verbatim
  have hmoment0 : M ^ (2 * r) ≤ Q * (zeroSumCount G (2 * r) : ℝ) := by
    rw [hnospur] at hmoment; exact hmoment
  exact WFL3.char0_prize_moment_bound_sq hk G hG hM hQ hr hrQ hmoment0

/-- **THE UNCONDITIONAL BELOW-GIRTH PRIZE TRANSFER (norm form).** Square-root of `prize_sq_of_no_spur`:
in the no-spur regime the char-`p` formal-period sup obeys `M ≤ √(2e·|G|·r)`, explicit constant
`√(2e)`. At `r = ⌈log Q⌉` this is `M ≤ √(2e)·√(|G|·log Q)` — the Gaussian/Ramanujan per-frequency
target — but ONLY on the spur-free corner (the prize depth violates `hnospur`). -/
theorem prize_of_no_spur {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    (Echarp : ℕ → ℕ) {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hnospur : Echarp r = zeroSumCount G (2 * r))
    (hmoment : M ^ (2 * r) ≤ Q * (Echarp r : ℝ)) :
    M ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) := by
  have hsq := prize_sq_of_no_spur hk G hG Echarp hM hQ hr hrQ hnospur hmoment
  calc M = Real.sqrt (M ^ 2) := (Real.sqrt_sq hM).symm
    _ ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) := Real.sqrt_le_sqrt hsq

/-- **The energy form of the no-spur input, restated for citation.** When the char-`p` energy equals
the char-`0` zero-sum count, the Lam–Leung char-`0` bound applies to it directly: `Echarp r ≤ (2r−1)‼·n^r`.
This is the exact statement "below the cyclotomic girth, char-`p` energy is Wick-bounded with NO
conjectural slack" (cf. wf-S5 `energy_eq_wick_when_no_spur`, here cast to `ℝ` against the wf-L3 energy
bound), and it is the SOLE hypothesis the prize transfer needs beyond the field-independent moment
identity. -/
theorem charpEnergy_le_wick_of_no_spur {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    (Echarp : ℕ → ℕ) (hnospur : Echarp r = zeroSumCount G (2 * r)) :
    (Echarp r : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  rw [hnospur]; exact WFL3.char0_energy_bound hk G hG

/-! ## The below-girth BAND: no-spur is monotone, so the prize bound holds at ALL depths ≤ r -/

open ArkLib.ProximityGap.wfS5ThetaCountWick in
/-- **The cumulative spurious count is MONOTONE in the depth.** `cumTheta` is a sum of non-negative
shell counts over `range (W+1)`, so a deeper cutoff dominates a shallower one. This is the structural
fact (never stated) that makes the no-spur regime a genuine BAND rather than a single depth: if the
spurious mass vanishes at depth `2r`, it vanishes at every depth below. -/
theorem cumTheta_mono {d : ℕ} (p : ℕ) (g : Fin d → ℤ)
    (dom : Finset (Fin d → ℤ)) {W₁ W₂ : ℕ} (hW : W₁ ≤ W₂) :
    cumTheta p g dom W₁ ≤ cumTheta p g dom W₂ := by
  unfold cumTheta
  apply Finset.sum_le_sum_of_subset
  intro w hw
  rw [Finset.mem_range] at hw ⊢
  omega

open ArkLib.ProximityGap.wfS5ThetaCountWick in
/-- **Girth `> 2r` ⟹ no spurious mass at EVERY depth `s ≤ r`.** From `cumTheta (2r) = 0` and
monotonicity, `cumTheta (2s) = 0` for all `s ≤ r`: the below-girth band is downward-closed. This is the
exact hypothesis under which the no-spur prize transfer holds simultaneously across the whole depth
range `1 ≤ s ≤ r` (not just at the single endpoint `r`). -/
theorem cumTheta_zero_band {d : ℕ} (p : ℕ) (g : Fin d → ℤ)
    (dom : Finset (Fin d → ℤ)) {r s : ℕ} (hsr : s ≤ r)
    (h : cumTheta p g dom (2 * r) = 0) :
    cumTheta p g dom (2 * s) = 0 :=
  Nat.le_zero.mp (h ▸ cumTheta_mono p g dom (by omega))

end ArkLib.ProximityGap.Frontier.WFS5L3NoSpur

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only. -/
#print axioms ArkLib.ProximityGap.Frontier.WFS5L3NoSpur.prize_sq_of_no_spur
#print axioms ArkLib.ProximityGap.Frontier.WFS5L3NoSpur.prize_of_no_spur
#print axioms ArkLib.ProximityGap.Frontier.WFS5L3NoSpur.charpEnergy_le_wick_of_no_spur
#print axioms ArkLib.ProximityGap.Frontier.WFS5L3NoSpur.cumTheta_mono
#print axioms ArkLib.ProximityGap.Frontier.WFS5L3NoSpur.cumTheta_zero_band
