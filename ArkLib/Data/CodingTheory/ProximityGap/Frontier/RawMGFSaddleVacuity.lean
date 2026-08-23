/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CoshMGFIdentity
import ArkLib.Data.CodingTheory.ProximityGap.EnergyCharacterTransport

/-!
# The raw even-moment MGF saddle hypothesis is VACUOUS at the prize (#444 §8 / DCEnergyEssential)

The in-tree cosh-MGF saddle consumer (`_CoshMGFSaddle.period_le_of_mgfBound`,
`CoshMGFSaddleAssembled.period_le_saddle_closedForm`, and the bridge
`NearRamanujanFromSaddle.prizeFloor_of_saddle` built on them) takes as its single hypothesis the **raw**
even-moment MGF bound

    `RawMGF(y) := ∑_r q·E_r(G)/(2r)!·y^{2r}  ≤  q·exp(n y²/2)`   (at the saddle `y*² = 2 log q/n`, RHS = `q²`).

But by the in-tree identity `coshMGF_eq_evenMoment_tsum`, `RawMGF(y) = ∑_{b∈F} cosh(‖η_b‖·y)` — a sum over
**all** `b`, INCLUDING the `b = 0` DC term `cosh(‖η_0‖·y) = cosh(n·y)` (since `‖η_0‖ = |G| = n` by
`eta_zero`).  So `RawMGF(y) ≥ cosh(n·y)` unconditionally.  This file proves that lower bound and its
immediate consequence:

> **`rawMGF_ge_dc`** — `cosh(n·y) ≤ RawMGF(y)` for every `y` (the DC term dominates from below).
> **`raw_saddle_hyp_false_of_dc_gt`** — if `q·exp(n y²/2) < cosh(n·y)` then the raw saddle hypothesis
>   `RawMGF(y) ≤ q·exp(n y²/2)` is FALSE (`¬ ...`).  At the saddle `y*` this triggers exactly when
>   `cosh(n y*) > q²`, i.e. `n y* = √(2n log q) > 2 log q + log 2`, i.e. roughly `n > 2 log q`.

**Probe-verified** (`scripts/probes/probe_rawmgf_saddle_vacuity.py`): in the prize regime `q = n^β`,
`β ∈ {4,5}`, the DC term log-scale `n y* = √(2n log q)` exceeds `log(q²) = 2 log q` for **every** `n ≥ 2^6`
(by ~27× at `n = 2^16`; crossover `n = 2^4→2^6`).  So the raw saddle hypothesis is unsatisfiable for all
prize-regime `n` — the saddle-consumer conditionals (and `prizeFloor_of_saddle`) are true but on a
**vacuous premise** at the prize.

## Honest scope (rule 4, rule 6)
This is a **refutation-with-mechanism / constraint lemma**, not a CORE closure.  It does NOT break the
saddle/bridge theorems (they remain valid conditionals); it **localizes the genuine open target**: the
non-vacuous form is the **DC-subtracted** `A_r = E_r − n^{2r}/q` MGF (`Σ_r q·A_r/(2r)!·y^{2r} ≤ exp(n y²/2)`,
the `Φ_p − DC` form), exactly as #444 §8 / `DCEnergyEssential.lean` already mandate.  The raw-`E_r` saddle
hypothesis must be replaced by the DC-subtracted one for any honest prize attack.  CORE stays OPEN.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.EnergyCharacterTransport
open ProximityGap.Frontier.CoshMGFIdentity

namespace ProximityGap.Frontier.RawMGFSaddleVacuity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The DC lower bound on the raw even-moment MGF.**  Applying `cosh_period_le_evenMoment_tsum`
at the frequency `b₀ = 0` and rewriting `‖η_0‖ = |G|` (`eta_zero`), the raw even-moment MGF dominates
its `b = 0` DC term: `cosh(n·y) ≤ ∑_r q·E_r/(2r)!·y^{2r}`. -/
theorem rawMGF_ge_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (y : ℝ) :
    Real.cosh ((G.card : ℝ) * y)
      ≤ ∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ) := by
  have h := cosh_period_le_evenMoment_tsum (F := F) hψ G y 0
  -- ‖η_0‖ = |G| (real norm), so cosh(‖η_0‖ y) = cosh(n y)
  have hnorm : ‖eta ψ G (0 : F)‖ = (G.card : ℝ) := by
    rw [eta_zero]; simp
  rwa [hnorm] at h

/-- **Vacuity of the raw saddle hypothesis.**  If the saddle right-hand side `q·exp(n y²/2)` is
strictly below the DC term `cosh(n·y)`, then the raw even-moment MGF saddle hypothesis
`RawMGF(y) ≤ q·exp(n y²/2)` is impossible (its left side is `≥ cosh(n y) >` the right side).  In the
prize regime this strict inequality holds at the saddle for every `n ≥ 2^6` (probe-verified), so the
raw-`E_r` saddle hypothesis is vacuous there — the live open target is the DC-subtracted form. -/
theorem raw_saddle_hyp_false_of_dc_gt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (y : ℝ)
    (hgt : (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2) < Real.cosh ((G.card : ℝ) * y)) :
    ¬ ((∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
        ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) := by
  intro hhyp
  have hdc := rawMGF_ge_dc (F := F) hψ G y
  -- cosh(n y) ≤ RawMGF ≤ q·exp(...) < cosh(n y) — contradiction
  exact absurd (lt_of_le_of_lt (le_trans hdc hhyp) hgt) (lt_irrefl _)

end ProximityGap.Frontier.RawMGFSaddleVacuity

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx):
#print axioms ProximityGap.Frontier.RawMGFSaddleVacuity.rawMGF_ge_dc
#print axioms ProximityGap.Frontier.RawMGFSaddleVacuity.raw_saddle_hyp_false_of_dc_gt
