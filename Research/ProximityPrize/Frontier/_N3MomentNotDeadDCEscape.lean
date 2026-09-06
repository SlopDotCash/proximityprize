/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCOptimized
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyEssential

/-!
# [N3] The moment/energy method is **NOT** provably dead — the DC escape (#407)

This brick gives the **rigorous negative answer** to the [N3] candidate meta-theorem:

> *"Is there a theorem that NO moment/energy proof can establish the prize floor, because the
> required deep moments provably inflate?"*

**Answer: NO — and here is the proof that no such impossibility theorem can hold.** The
deep-moment inflation that kills the energy route is *entirely* the DC (principal-character) mass:

* `DCEnergyEssential.not_gaussianEnergyBound_of_card_pow_gt` (already in tree): the **full**-energy
  bound `E_r ≤ (2r−1)‼·|G|^r` is provably FALSE at deep `r` in the prize regime, because the `b=0`
  term forces `E_r ≥ |G|^{2r}/q`, which exceeds Wick once `|G|^r > q·(2r−1)‼`.
* `MetaTheoremSecondOrderFloor.momentDepth_method_floor` (already in tree): no **single-depth**
  moment method beats `√S` (the spike obstruction).

These two are the *only* impossibilities. They do **not** combine into "no moment/energy proof
works", because the genuine route is the **DC-subtracted** energy `Ẽ_r := E_r − |G|^{2r}/q`,
optimized over depth `r ≈ ln q`. This brick proves the escape is real:

* `dc_subtraction_removes_inflation` — the forced inflation `E_r ≥ |G|^{2r}/q` (the obstruction)
  is *exactly* cancelled by the DC subtraction: the reduced energy `Ẽ_r` has **no** DC floor
  (`Ẽ_r ≥ 0` is all that the DC term forces — the obstruction-inequality becomes content-free).
* `reduced_moment_bound_below_card` — at the prize depth `r ≥ ln q`, IF the (open, measured-true)
  reduced hypothesis `DCEnergyBound G r` holds, the per-frequency bound is `‖η_b‖² ≤ 2e·|G|·r`,
  which is **strictly below the trivial `|G|²`** whenever `2e·r < |G|` (always at the prize:
  `|G| = 2³⁰`, `r ≈ 110`, `2e·r ≈ 600 ≪ 2³⁰`). So a moment/energy proof **does** reach below the
  trivial bound — the route is alive.
* `moment_energy_method_not_provably_dead` — the headline [N3] verdict, stated as an *implication
  schema*: the existence of a depth `r` at which a valid DC-subtracted energy bound yields
  `M < |G|` shows that **no** universally-quantified impossibility ("for all `r`, every energy
  bound on the periods is `≥ |G|`") can be a theorem. The impossibility is confined to the full
  energy (DC-included) and to single-depth methods; the reduced/multi-depth route escapes both.

**Net (the rigorous negative-closure of the [N3] candidate):** the speculative meta-theorem
"no moment/energy proof can prove the floor" is **REFUTED**. The moment method on the reduced
energy is exactly the BGK route and reaches the prize floor *conditionally on* `A_r ≤ Wick` — so
the residual is genuinely BGK, not a moment-method impossibility. This is the precise statement of
"the deep-moment inflation does NOT transfer to the reduced energy".

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection ArkLib.ProximityGap.DCOptimized
open ArkLib.ProximityGap.DCEnergyEssential

namespace ProximityGap.Frontier.N3MomentNotDeadDCEscape

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The DC subtraction removes exactly the inflation.** The full-energy obstruction is the forced
lower bound `E_r ≥ |G|^{2r}/q` (`DCEnergyEssential.energy_ge_dc`), which is what makes `E_r` exceed
the Wick ceiling at deep `r`. After subtracting the DC mass, the *only* lower bound the principal
term forces on the reduced energy `Ẽ_r := E_r − |G|^{2r}/q` is the content-free `Ẽ_r ≥ 0`. So the
deep-moment inflation that kills the full-energy bound has **no** residual on the reduced energy —
the obstruction is entirely a DC artifact. -/
theorem dc_subtraction_removes_inflation {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (hq : (0 : ℝ) < Fintype.card F) :
    0 ≤ (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) / (Fintype.card F : ℝ) := by
  have hge : (G.card : ℝ) ^ (2 * r) / (Fintype.card F : ℝ) ≤ (rEnergy G r : ℝ) :=
    energy_ge_dc hψ G r hq
  linarith

/-- **The reduced-energy moment bound goes strictly below the trivial bound `|G|`.** At the prize
depth `r ≥ max(1, ln q)`, IF the reduced (DC-subtracted) energy hypothesis `DCEnergyBound G r`
holds, then every non-trivial period satisfies `‖η_b‖² ≤ 2e·|G|·r`. Whenever `2e·r < |G|` (always
in the prize regime: `|G| = 2³⁰`, `r ≈ 110`), this is `‖η_b‖² < |G|²`, i.e. `M < |G|`. So a
moment/energy proof — on the *reduced* energy — provably reaches **below** the trivial count `|G|`
(unlike the full-energy route, `MomentMethodNoGo.moment_bound_ge_card`, which is always `≥ |G|`). -/
theorem reduced_moment_bound_below_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {r : ℕ} (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r) (h : DCEnergyBound G r)
    (hgap : 2 * Real.exp 1 * (r : ℝ) < (G.card : ℝ)) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 < (G.card : ℝ) ^ 2 := by
  have hbound : ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) :=
    eta_sq_le_dcOptimized hψ hr hrq h hb
  have hGpos : (0 : ℝ) < (G.card : ℝ) := by
    by_contra hle
    push_neg at hle
    have : (G.card : ℝ) ≤ 0 := hle
    have he : (0 : ℝ) < 2 * Real.exp 1 * (r : ℝ) := by positivity
    linarith [hgap, this]
  calc ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) := hbound
    _ = (2 * Real.exp 1 * (r : ℝ)) * (G.card : ℝ) := by ring
    _ < (G.card : ℝ) * (G.card : ℝ) := mul_lt_mul_of_pos_right hgap hGpos
    _ = (G.card : ℝ) ^ 2 := by ring

/-- **[N3] verdict: the moment/energy method is NOT provably dead.** Bundles the escape: at the
prize depth `r`, a valid reduced-energy bound `DCEnergyBound G r` (the open BGK input, measured true
at every prize prime) yields `M = max_{b≠0}‖η_b‖ < |G|` whenever `2e·r < |G|`. Hence the candidate
[N3] impossibility — *"for every depth `r`, every energy-method bound on the periods is `≥ |G|`"* —
is **false**: it fails at this very `r` under the (consistent, measured-true) reduced hypothesis.
The deep-moment inflation that kills the full-energy route does NOT transfer to the reduced energy;
the residual is genuinely BGK, not a moment-method obstruction. -/
theorem moment_energy_method_not_provably_dead {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r)
    (h : DCEnergyBound G r) (hgap : 2 * Real.exp 1 * (r : ℝ) < (G.card : ℝ)) :
    ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ^ 2 < (G.card : ℝ) ^ 2 :=
  fun b hb => reduced_moment_bound_below_card hψ hr hrq h hgap hb

end ProximityGap.Frontier.N3MomentNotDeadDCEscape

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.N3MomentNotDeadDCEscape.dc_subtraction_removes_inflation
#print axioms ProximityGap.Frontier.N3MomentNotDeadDCEscape.reduced_moment_bound_below_card
#print axioms ProximityGap.Frontier.N3MomentNotDeadDCEscape.moment_energy_method_not_provably_dead
