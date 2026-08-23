/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sol
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyEssential
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ProveAssemblyConcreteDC

/-!
# The DC-CORRECT prize floor at the worst-`b` SUP level (#444 / #407)

The adversarial audit (`DISPROOF_LOG.md`, 2026-06-19) found that the sup-level capstones
(`_SupBoundCapstone`, `_ThesisCapstone.subPoisson_variance_implies_prizeFloor`) route through the
**raw, DC-included** energy `E_r ≤ (2r·|G|)^r`, which
`DCEnergyEssential.not_gaussianEnergyBound_of_deep` proves is **FALSE at prize depth**
(`r ≈ log q`): the DC mass `|G|^{2r}/q` alone exceeds Wick, so the conditional is vacuously
discharged exactly where the prize lives. Fix #1 of the audit recommendation: *restate the
capstone on the DC-subtracted moment* `S_r = q·E_r − |G|^{2r} = ∑_{b≠0}‖η_b‖^{2r}`.

`_ProveAssemblyConcreteDC.period_le_prizeFloor_dc` did this for a FIXED nonzero frequency `b₀`. This
file lifts it to the actual prize object — the **worst-`b` supremum**
`M(G) = max_{b ≠ 0} ‖η_b‖` (`worstPeriod`) — keeping the DC term inside the hypothesis:

> `worstPeriod_le_prizeFloor_dc` : assuming ONLY the DC-subtracted energy bound `hSr` (the genuine
> open BGK/Paley core) and the saddle depth `hdepth`, the worst nonzero period over the thin set
> obeys the prize floor `M(G) ≤ √e·√(2r·|G|)`.

A companion guard makes the DC-correction explicit and non-bypassable:

> `raw_energy_hypothesis_vacuous_at_prize` — at any depth where the DC mass beats Wick
> (`q·(2r−1)‼·|G|^r < |G|^{2r}`, true for all `n ≥ 64`, `r ≈ log q` per the `n=64` crossover probe),
> the raw-energy hypothesis `GaussianEnergyBound G r` is FALSE — so a sup capstone phrased on it is
> vacuous-at-prize and the DC-subtracted phrasing here is the only non-vacuous one.

**Honest status.** This is NOT a proof of the prize. `hSr` at `r ≈ log q` IS the open core — the
char-`p` energy / BGK / thin-subgroup √-cancellation wall, satisfiable but unproven. What this file
contributes is the audit-recommended *honesty hardening*: the prize-object (worst-`b` sup) capstone
now carries the genuinely-open DC-subtracted residual instead of the DC-refuted raw `E_r` bound,
with a kernel-checked guard that the raw phrasing is vacuous at the prize scale. No CORE /
cancellation / completion / anti-concentration / moment-saving / capacity claim.

Issue #444 / #407.
-/

namespace ArkLib.ProximityGap.Frontier.DCCorrectSupCapstone

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyEssential
open ArkLib.ProximityGap.Frontier.ProveAssemblyConcreteDC
open ArkLib.ProximityGap.GaussPeriodMomentBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `univ.erase 0` is nonempty over a nontrivial field (there is a nonzero element). -/
theorem erase_zero_nonempty [Nontrivial F] : (univ.erase (0 : F)).Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : F)
  exact ⟨x, mem_erase.mpr ⟨hx, mem_univ _⟩⟩

/-- The prize object: the worst nonzero-frequency period norm `M(G) = max_{b ≠ 0} ‖η_b‖` over the
thin set `G`, as the Finset max over `univ.erase 0`. -/
noncomputable def worstPeriod [Nontrivial F] (ψ : AddChar F ℂ) (G : Finset F) : ℝ :=
  (univ.erase (0 : F)).sup' erase_zero_nonempty (fun b => ‖eta ψ G b‖)

/-- **The DC-correct prize floor at the worst-`b` SUP level.** Assuming ONLY the DC-subtracted
energy inequality `hSr` (the genuine open BGK/Paley core, `S_r = q·E_r − |G|^{2r} ≤ q·(2r·|G|)^r`)
and the
saddle depth `hdepth`, the prize object `worstPeriod = max_{b ≠ 0} ‖η_b‖` obeys the prize floor
`√e·√(2r·|G|)`. The `−|G|^{2r}` DC term is kept inside `hSr` (never dropped), so the residual is the
satisfiable/open DC-subtracted bound rather than the DC-refuted raw `E_r` bound. Lifts
`_ProveAssemblyConcreteDC.period_le_prizeFloor_dc` from a fixed `b₀` to the whole worst-`b` sup. -/
theorem worstPeriod_le_prizeFloor_dc [Nontrivial F] {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {r : ℕ} (hr : 0 < r)
    (hSr : (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
              ≤ (Fintype.card F : ℝ) * (2 * r * (G.card : ℝ)) ^ r)
    (hdepth : (Fintype.card F : ℝ) ≤ Real.exp r) :
    worstPeriod ψ G ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * (G.card : ℝ)) := by
  refine Finset.sup'_le erase_zero_nonempty _ ?_
  intro b hb
  have hb0 : b ≠ (0 : F) := (mem_erase.mp hb).1
  exact period_le_prizeFloor_dc hψ G hr hb0 hSr hdepth

/-- **The raw-energy sup hypothesis is vacuous at the prize scale.** Whenever the DC mass beats Wick
(`q·(2r−1)‼·|G|^r < |G|^{2r}`, the `n ≥ 64`, `r ≈ log q` regime per the crossover probe), the
raw-energy hypothesis `GaussianEnergyBound G r` (which the audited-vacuous sup capstones consume) is
FALSE. So those capstones are vacuously discharged at the prize, and the DC-subtracted phrasing in
`worstPeriod_le_prizeFloor_dc` is the only non-vacuous one. (Re-export of
`DCEnergyEssential.not_gaussianEnergyBound_of_deep` at the sup level, naming the obstruction.) -/
theorem raw_energy_hypothesis_vacuous_at_prize {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ)
    (hdeep : (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
      < (G.card : ℝ) ^ (2 * r)) :
    ¬ GaussianEnergyBound G r :=
  not_gaussianEnergyBound_of_deep hψ G r hdeep

end ArkLib.ProximityGap.Frontier.DCCorrectSupCapstone

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.DCCorrectSupCapstone in
#print axioms erase_zero_nonempty
open ArkLib.ProximityGap.Frontier.DCCorrectSupCapstone in
#print axioms worstPeriod_le_prizeFloor_dc
open ArkLib.ProximityGap.Frontier.DCCorrectSupCapstone in
#print axioms raw_energy_hypothesis_vacuous_at_prize
