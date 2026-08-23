/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.MCAExactPin

/-!
# The deployed-regime `δ*` reduced to ONE named obligation (#357)

This is the capstone of the bracket-meet programme. The KKH26 family supplies the **upper**
bracket *unconditionally and in-tree*: for the explicit smooth-domain evaluation code
`C = evalCode g n ((r−2)m)` (rate `ρ = ((r−2)m+1)/n` over a smooth multiplicative domain of
order `n = 2^μ·m`), `kkh26_mcaDeltaStar_le` proves

  `mcaDeltaStar(C, ε*) ≤ 1 − r/2^μ`   (the bad lines near capacity force the threshold down).

The grand challenge — meeting brackets at a deployed-regime interior `δ*` — is therefore exactly
the **lower** bracket *up to* that radius: the count stays good *below* it,

  `ε_mca(C, δ) ≤ ε*` for every `δ < 1 − r/2^μ`   (`InteriorCeiling`).

`kkh26_deltaStar_pin_of_interior_ceiling` proves that this one obligation **pins `δ*` exactly**:
`mcaDeltaStar(C, ε*) = 1 − r/2^μ`. The reduction is axiom-clean; the obligation is the genuine
open core — *the explicit-RS list count stays below `ε*·q` up to the KKH26 radius*, equivalently
"the bad-scalar witnesses are algebraically forced below the middle antichain layer", the
25-year beyond-Johnson list-decoding problem for explicit codes. No known technique discharges
it (CS25/BCHKS25 couple any progress here to that problem; three independent groups confirm the
at-capacity conjectures are false, sharpening — not solving — the interior).

**What this file delivers:** the deployed prize is now *one* machine-stated `Prop` plus a proven
reduction. Any future sharp interior ceiling (a derandomized random-RS bound, an additive-
combinatorial inverse theorem, a syndrome-space degree bound) lands as `InteriorCeiling` and
the pin is immediate.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26

namespace ProximityGap.KKH26DeltaStarReduction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The closed-point exact-pin combinator (ceiling form).** A proven *upper* bracket
`δ* ≤ δ₀` together with a *good point at `δ₀`* (`ε_mca(C, δ₀) ≤ ε*`) pins `δ* = δ₀`. This is the
dual of the open-interval combinator: here `δ₀` itself is good (the threshold is attained). -/
theorem mcaDeltaStar_eq_of_le_of_good
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ₀ : ℝ≥0}
    (hle : mcaDeltaStar (F := F) (A := A) C εstar ≤ δ₀)
    (hδ₀ : δ₀ ≤ 1)
    (hgood : epsMCA (F := F) (A := A) C δ₀ ≤ εstar) :
    mcaDeltaStar (F := F) (A := A) C εstar = δ₀ :=
  le_antisymm hle (le_mcaDeltaStar_of_good (F := F) (A := A) C εstar hδ₀ hgood)

/-- **The interior-ceiling obligation** for the KKH26 family: the bad-scalar count stays below
`ε*·q` for *every radius strictly below* the ceiling `1 − r/2^μ`. This — and only this — is the
open core for the deployed prize; the bad point *at* the ceiling (and hence above, by
monotonicity) is **in-tree** (`kkh26_epsMCA_lower_bound`). The radius `1 − r/2^μ` itself is *bad*,
so the good set is the open interval `[0, 1 − r/2^μ)` whose supremum is the pin — the obligation is
"the explicit-RS list stays small *up to* the near-capacity radius", the 25-year open problem. -/
def InteriorCeiling (p n : ℕ) [Fact p.Prime] [NeZero n] (g : ZMod p) (μ m r : ℕ)
    (εstar : ℝ≥0∞) : Prop :=
  ∀ δ : ℝ≥0, δ < 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) →
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) δ ≤ εstar

/-- **THE DEPLOYED-REGIME REDUCTION.** For the explicit KKH26 smooth-domain code, the entire
grand-challenge pin reduces to the single `InteriorCeiling` obligation: granting it,

  `mcaDeltaStar(evalCode g n ((r−2)m), ε*) = 1 − r/2^μ`

— `δ*` pinned exactly at the KKH26 ceiling radius (an interior point of the window, sitting
`(2m−1)/n` below capacity). The bad side is **in-tree and unconditional**: `kkh26_epsMCA_lower_bound`
makes `1 − r/2^μ` bad, and `epsMCA_mono` propagates it to every larger radius. The good side is the
obligation (`InteriorCeiling`, good *below* the ceiling). The two meet at the jump via the
open-interval combinator. This is the cleanest statement of "what is left to win the Proximity
Prize": one named good-below-the-ceiling obligation at the explicit near-capacity radius. -/
theorem kkh26_deltaStar_pin_of_interior_ceiling
    {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    (hceiling : InteriorCeiling p n g μ m r εstar) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  -- the ceiling radius is bad (KKH26 lower bound); monotonicity makes every `δ ≥` it bad too
  have hbad_at : εstar < epsMCA (F := ZMod p) (A := ZMod p)
      (evalCode g n ((r - 2) * m)) (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) :=
    lt_of_lt_of_le hεstar (kkh26_epsMCA_lower_bound hμ hm hn hg hp hr2 hr)
  refine mcaDeltaStar_eq_of_good_below_of_bad_above
    (evalCode g n ((r - 2) * m)) εstar tsub_le_self hceiling
    (fun δ hδ => lt_of_lt_of_le hbad_at
      (epsMCA_mono (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) hδ))

end ProximityGap.KKH26DeltaStarReduction

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.KKH26DeltaStarReduction.mcaDeltaStar_eq_of_le_of_good
#print axioms ProximityGap.KKH26DeltaStarReduction.kkh26_deltaStar_pin_of_interior_ceiling
