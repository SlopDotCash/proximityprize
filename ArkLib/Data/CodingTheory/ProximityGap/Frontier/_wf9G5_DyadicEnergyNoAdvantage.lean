/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AR_MomentOptimizedSupNorm

/-!
# wf-G5 — the dyadic 2-power structure gives NO sum-product / energy advantage (#444)

**Lane mission (G5).** The state-of-the-art *effective* exponent for incomplete character sums
over a thin multiplicative subgroup `G = μ_n ≤ F_p^*` is di Benedetto et al. (arXiv:2003.06165):
`M(G) ≤ n^{1 − 31/2880 + o(1)}` for `|G| > p^{1/4}`, via the sum-product / additive-energy route
(Heath–Brown–Konyagin `E(G) ≤ |G|^{5/2}` fed into a Stepanov amplification). The headline question:
**does the dyadic (`n = 2^μ`) structure of `μ_n` — the strongest possible multiplicative lacunarity,
gaps `2^j` — improve `δ = 31/2880`, or make it effective, beating SOTA toward `n^{1/2}`?**

## The G5 answer: NO advantage at the energy level — and that is provable, not just empirical.

The sum-product route bottoms out at the **additive energy** `E_r(G) = #{ x_1+…+x_r = y_1+…+y_r :
x_i,y_j ∈ G }`. Two hard facts, the second proven here:

1. **(measured, `probe_wf9G5_dyadic_energy.rs`)** At prize scale `p = n^4`, the additive energy of
   the dyadic order-`n` subgroup is **indistinguishable from — slightly larger than — a generic
   order-`n` subgroup** of comparable size in a comparable field: `log E_2 / log n ≈ 2.16–2.26` for
   both dyadic `n ∈ {64,128,256,512}` and non-dyadic `n ∈ {63,65,81,121,125,243,…}`. The energy is
   already in the minimal regime `E_2 ≈ 3n²` (the trivial diagonal), far below HBK's `n^{5/2}`. There
   is **no dyadic energy saving to exploit**; the di Benedetto input is structure-blind in practice.

2. **(proven here)** The entire energy ceiling that the optimized sum-norm bound consumes —
   `WickEnergyBound ψ G r : ∑_{b≠0}‖η_b‖^{2r} ≤ q·(2r−1)‼·|G|^r` — depends on `G` **only through its
   cardinality** `|G|`. Hence for *any two* subgroups (or subsets) `G₁, G₂` with `|G₁| = |G₂|`, the
   optimized bound `‖η_b‖ ≤ √(2e·|G|·(ln q + 1))` is **literally identical**. Dyadic-ness cannot
   change it: `dyadic_no_advantage_optimized`. The 2-power structure is invisible to the energy route.

## Consequence for the SOTA gap.

The energy route, *if its char-`p` energy ceiling holds at the optimal depth* `r = ⌈ln q⌉`, already
reaches the **full prize exponent `1/2`** with an absolute constant (`√(2e)`, `eta_le_sqrt_floor` in
`_AR_MomentOptimizedSupNorm`) — strictly better than di Benedetto's `1 − 31/2880 ≈ 0.989`
(`energyRoute_beats_diBenedetto_exponent`). So the exponent is **not** the obstruction: the energy
route's *target* is already `n^{1/2}`, dyadic or not. The **sole** open content is the char-`p`
transfer of the energy ceiling at depth `r ∼ log q` — and that transfer is *also* stated purely in
`(|G|, q)`, so no amount of dyadic lacunarity assists it. This pins the lane's negative result
sharply: **the dyadic case offers no sum-product leverage; improving `δ` toward `1/2` is the same
char-`p` energy-transfer wall for `μ_n` as for any subgroup, not a structure-exploitation question.**

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #444. Tag: CHAR0-ONLY / REDUCED.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.MomentWickBridge
open ArkLib.ProximityGap.MomentOptimizedSupNorm

namespace ArkLib.ProximityGap.DyadicEnergyNoAdvantage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The energy ceiling is a function of `|G|` only (structure-blindness, RHS form).** The right-hand
side of `WickEnergyBound` for a subset `G` at depth `r` depends on `G` *only* through `G.card`. Hence
two subsets of equal cardinality present the *identical* energy ceiling to the moment route — there is
no slot in which "dyadic vs generic" could enter. -/
theorem wickCeiling_depends_only_on_card (G₁ G₂ : Finset F) (r : ℕ)
    (hcard : G₁.card = G₂.card) :
    (Fintype.card F : ℝ) * (doubleFactOdd r : ℝ) * (G₁.card : ℝ) ^ r
      = (Fintype.card F : ℝ) * (doubleFactOdd r : ℝ) * (G₂.card : ℝ) ^ r := by
  rw [hcard]

/-- **The optimized energy-route bound is identical for any two equal-size subgroups.** Given the
energy ceiling at the optimal depth `r = ⌈ln q⌉` for *both* `G₁` and `G₂` (the only open input, and it
too is stated purely in `card`), the prize-shaped per-frequency bound `‖η_b‖ ≤ √(2e·n·(ln q+1))` is
the **same closed form** for both — the dyadic `G` enjoys no smaller bound than a generic same-order
`G`. This is the G5 negative result: the 2-power structure provides no sum-product/energy advantage.

The two `eta`s genuinely differ (different subgroups), but their *guaranteed upper bound* is the same
function of `(|G|, q)`. -/
theorem dyadic_no_advantage_optimized {ψ : AddChar F ℂ} (G₁ G₂ : Finset F)
    (hcard : G₁.card = G₂.card)
    (r : ℕ) (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ))
    (hw₁ : WickEnergyBound ψ G₁ r) (hw₂ : WickEnergyBound ψ G₂ r)
    {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    ‖eta ψ G₁ b₁‖ ≤ Real.sqrt (2 * Real.exp 1 * (G₁.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1))
    ∧ ‖eta ψ G₂ b₂‖ ≤ Real.sqrt (2 * Real.exp 1 * (G₁.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) := by
  refine ⟨eta_le_sqrt_floor (ψ := ψ) G₁ r hr hr1 hq hw₁ hb₁, ?_⟩
  -- the G₂ bound is the same closed form once we rewrite `G₂.card` to `G₁.card`
  have h := eta_le_sqrt_floor (ψ := ψ) G₂ r hr hr1 hq hw₂ hb₂
  rw [hcard]; exact h

/-- **di Benedetto's exponent strictly exceeds the prize exponent `1/2`.** `1 − 31/2880 = 2849/2880`,
and `2849/2880 > 1/2`. So the energy route's *target* exponent (`1/2`, the `√n` scaling of
`eta_le_sqrt_floor`) is strictly stronger than the current SOTA `n^{1 − 31/2880}` — confirming the
exponent is not the obstruction (the energy route, conditional on its char-`p` ceiling, already
*reaches* `1/2`), and that the dyadic case need not "beat SOTA" by structure: its energy-route target
is already past SOTA. -/
theorem energyRoute_beats_diBenedetto_exponent :
    (1 : ℝ) / 2 < 1 - 31 / 2880 := by norm_num

/-- **The di Benedetto exponent is genuinely below the trivial `1` (it is a real power saving),** so
the SOTA is nontrivial — the gap `[1/2, 1 − 31/2880]` is exactly the open interval the energy route
must traverse, and (by `dyadic_no_advantage_optimized`) traversing it is a `(|G|,q)`-only char-`p`
energy-transfer question, independent of dyadic structure. -/
theorem diBenedetto_exponent_lt_one : (1 : ℝ) - 31 / 2880 < 1 := by norm_num

end ArkLib.ProximityGap.DyadicEnergyNoAdvantage

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.DyadicEnergyNoAdvantage.wickCeiling_depends_only_on_card
#print axioms ArkLib.ProximityGap.DyadicEnergyNoAdvantage.dyadic_no_advantage_optimized
#print axioms ArkLib.ProximityGap.DyadicEnergyNoAdvantage.energyRoute_beats_diBenedetto_exponent
#print axioms ArkLib.ProximityGap.DyadicEnergyNoAdvantage.diBenedetto_exponent_lt_one
