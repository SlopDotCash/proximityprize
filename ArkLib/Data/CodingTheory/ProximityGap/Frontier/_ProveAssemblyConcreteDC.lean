/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NubsCarson
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ProveAssemblyConcrete

/-!
# The DC-CORRECT concrete assembly: prize floor from the DC-SUBTRACTED energy residual (#444 / #407)

`_ProveAssemblyConcrete.period_le_prizeFloor` reduces the worst-period prize floor to the single
hypothesis `hEnergy : rEnergy G r ≤ (2r·|G|)^r` on the **raw, DC-included** energy `E_r`, by dropping
the `−|G|^{2r}` DC term from the proven moment bound before applying the envelope. But that residual is
**provably FALSE at prize scale**: `DCEnergyEssential.energy_ge_dc` gives `E_r ≥ |G|^{2r}/q`
unconditionally, so at the saddle depth `r ≈ log q` (forced by `q ≤ exp r`) the DC mass `|G|^{2r}/q`
exceeds `(2r·|G|)^r` by an astronomical margin — the conditional is vacuously discharged exactly in the
regime that matters. (This is the pre-#407 DC-drop that DISPROOF_LOG flagged as fatal.)

This file supplies the **DC-correct** form: the residual is carried on the **DC-subtracted** `b≠0`
moment `S_r = q·E_r − |G|^{2r} = ∑_{b≠0}‖η_b‖^{2r}`, which is the genuine open core (the BGK/Paley
wall, satisfiable; cf. `_PrizeConditionalCapstone.prize_of_saddleEnergyBound` and
`DCEnergyCorrection.DCEnergyBound`). The `−|G|^{2r}` is **kept inside the hypothesis**, never dropped.

> `period_le_prizeFloor_dc` : for the real Gauss period `eta ψ G b₀` (`b₀ ≠ 0`), assuming the single
> DC-subtracted energy inequality `hSr : q·E_r − |G|^{2r} ≤ q·(2r·|G|)^r` and depth `q ≤ exp r`,
> the worst period obeys the prize floor `‖eta‖ ≤ √e·√(2r·|G|)`.

Proof: the worst term is `≤` the full `b≠0` moment `= q·E_r − |G|^{2r}` (`single_le_sum` +
`sum_nonzero_moment`), `hSr` bounds that by `q·(2r·|G|)^r`, then the in-tree `saddle_floor`.

**Honest status.** This is NOT a proof of the prize. `hSr` at `r ≈ log q` IS the open core (the
DC-subtracted `S_r/(q) ≤ Wick` = the char-`p` energy wall, equivalent to BGK). What this file fixes is
the *object*: the carried hypothesis is now the genuinely-open DC-subtracted inequality rather than the
DC-refuted raw-energy bound, so the conditional is a real reduction (not vacuous) at the prize scale.
Issue #444 / #407.
-/

namespace ArkLib.ProximityGap.Frontier.ProveAssemblyConcreteDC

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.Frontier.ProveAssemblyConcrete

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The DC-correct concrete prize floor.** For the real Gauss period `eta ψ G b₀` (`b₀ ≠ 0`),
assuming ONLY the DC-subtracted energy inequality `hSr` (the genuine open BGK/Paley core) and the
depth constraint `hdepth`, the worst nonzero period obeys the prize floor `√e·√(2r·|G|)`. Unlike
`period_le_prizeFloor`, the `−|G|^{2r}` DC term is kept inside the hypothesis, so the residual is the
DC-subtracted `S_r` bound (satisfiable / open) rather than the DC-included raw `E_r` bound
(refuted at prize scale by `DCEnergyEssential.energy_ge_dc`). -/
theorem period_le_prizeFloor_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ}
    (hr : 0 < r) {b₀ : F} (hb₀ : b₀ ≠ 0)
    (hSr : (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
              ≤ (Fintype.card F : ℝ) * (2 * r * (G.card : ℝ)) ^ r)
    (hdepth : (Fintype.card F : ℝ) ≤ Real.exp r) :
    ‖eta ψ G b₀‖ ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * (G.card : ℝ)) := by
  have hb₀mem : b₀ ∈ univ.erase (0 : F) := mem_erase.mpr ⟨hb₀, mem_univ _⟩
  -- worst nonzero term ≤ the full b≠0 moment
  have hsingle : ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r)) (fun b _ => by positivity) hb₀mem
  -- the proven DC-subtracted moment identity: the b≠0 sum IS q·E_r − |G|^{2r} (DC kept, not dropped)
  rw [sum_nonzero_moment hψ G r] at hsingle
  -- chain the DC-subtracted residual directly — no DC-drop
  have hWick : ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (2 * r * (G.card : ℝ)) ^ r := le_trans hsingle hSr
  exact saddle_floor hr (norm_nonneg _) (by positivity) (by positivity) hWick hdepth

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms period_le_prizeFloor_dc

end ArkLib.ProximityGap.Frontier.ProveAssemblyConcreteDC
