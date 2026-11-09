/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MomentWickBridge

/-!
# Moment-ratio peak: the prize reduces to "the Wick ratio peaks at the PROVEN r=2" (#444)

The open content of the prize floor is `WickEnergyBound ψ G r` at depth `r ∼ log q`
(`∑_{b≠0}‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ`).  The depth scan `probe_dsar_threshold_vs_depth` /
`probe_dsar_thin_allr_scan` found a sharp empirical structure: for **thin proper** primes the
normalised **Wick ratio**

> `wickRatio r := (∑_{b≠0}‖η_b‖^{2r}) / (q·(2r−1)‼·nʳ)`

is **maximised at `r = 2`** (value `1 − 1/n < 1`, the exact second/fourth-moment value
`∑_{b≠0}‖η_b‖⁴ = q(3n²−3n)`), and is *increasingly slack* for larger `r` (`wickRatio r → 0`).
The only places `wickRatio r > 1` are the **excluded** degenerate primes (full-group `μ_n = F_q^×`,
or thick `β < 2`).

This file records that structural reframing as a clean conditional: if the Wick ratio peaks at `r = 2`
(`MomentRatioPeakAtTwo`, verified at every computable depth for thin primes) and the `r = 2` anchor
`wickRatio 2 ≤ 1` holds (the **proven** fourth-moment bound `∑_{b≠0}‖η_b‖⁴ ≤ q·3n²`, in-tree
`FourthMomentCLT`), then **`WickEnergyBound` holds at every `r`** — and hence (via
`MomentOptimizedSupNorm`) the prize floor `M ≤ √(2e·n·log q)` follows.

So the prize is reduced to **one** statement — *the deep moments never exceed the proven second-moment
ratio* — which pins the worst case to the already-closed `r = 2`.  Honest scope: `MomentRatioPeakAtTwo`
at `r ∼ log q` is the **deep-moment concentration** statement, equivalent to the BGK/Paley
√-cancellation wall; this brick does NOT discharge it — it is the sharpest *reframing* (worst-case at
the proven anchor), with the implication `peak ⟹ all-r Wick` proven axiom-clean here.

Axiom-clean.  Issue #444.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.MomentWickBridge

namespace ArkLib.ProximityGap.MomentRatioPeak

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The normalised Wick ratio at depth `r`: `(∑_{b≠0}‖η_b‖^{2r}) / (q·(2r−1)‼·nʳ)`. -/
noncomputable def wickRatio (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : ℝ :=
  (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r))
    / ((Fintype.card F : ℝ) * (doubleFactOdd r : ℝ) * (G.card : ℝ) ^ r)

/-- The Wick denominator `q·(2r−1)‼·nʳ` is positive when `q ≥ 1` and `G` is nonempty. -/
theorem wick_denom_pos (G : Finset F) (r : ℕ)
    (hq : 1 ≤ Fintype.card F) (hG : G.Nonempty) :
    (0 : ℝ) < (Fintype.card F : ℝ) * (doubleFactOdd r : ℝ) * (G.card : ℝ) ^ r := by
  have h1 : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have h2 : (0 : ℝ) < (doubleFactOdd r : ℝ) := by
    have : 0 < doubleFactOdd r := by
      unfold doubleFactOdd; exact Finset.prod_pos (fun i _ => by positivity)
    exact_mod_cast this
  have h3 : (0 : ℝ) < (G.card : ℝ) ^ r := by
    have : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hG
    positivity
  positivity

/-- `wickRatio ψ G r ≤ 1` gives `WickEnergyBound ψ G r` (denominator positive). -/
theorem wickEnergyBound_of_ratio_le_one {ψ : AddChar F ℂ} (G : Finset F) (r : ℕ)
    (hq : 1 ≤ Fintype.card F) (hG : G.Nonempty) (h : wickRatio ψ G r ≤ 1) :
    WickEnergyBound ψ G r := by
  have h' : wickRatio ψ G r ≤ 1 := h
  unfold wickRatio at h'
  exact (div_le_one (wick_denom_pos G r hq hG)).mp h'

/-- **The peak hypothesis (the sharpest open core).**  `MomentRatioPeakAtTwo` says the Wick ratio at
every depth `r ≥ 1` is at most its value at `r = 2`.  Verified at every computable depth for thin proper
primes (`probe_dsar_*`); at `r ∼ log q` it is the deep-moment concentration = the BGK wall. -/
def MomentRatioPeakAtTwo (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  ∀ r : ℕ, 1 ≤ r → wickRatio ψ G r ≤ wickRatio ψ G 2

/-- **The reframing (proven).**  If the Wick ratio peaks at `r = 2` and the `r = 2` anchor holds
(`wickRatio 2 ≤ 1`, the proven fourth-moment bound), then `WickEnergyBound` holds at **every** `r ≥ 1`.
So the entire `∀r` Wick hypothesis (hence the prize floor, via `MomentOptimizedSupNorm`) collapses to the
single statement "deep moments don't exceed the proven second-moment ratio". -/
theorem wickEnergyBound_of_peak {ψ : AddChar F ℂ} (G : Finset F)
    (hq : 1 ≤ Fintype.card F) (hG : G.Nonempty)
    (hpeak : MomentRatioPeakAtTwo ψ G) (hanchor : wickRatio ψ G 2 ≤ 1) :
    ∀ r : ℕ, 1 ≤ r → WickEnergyBound ψ G r := by
  intro r hr
  exact wickEnergyBound_of_ratio_le_one G r hq hG ((hpeak r hr).trans hanchor)

/-- **Corollary — the per-frequency ceiling at every depth from the peak.**  Under the peak hypothesis
and the proven `r=2` anchor, every nonzero frequency obeys `‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ` at every `r ≥ 1`
(via the moment-method bridge).  Feeding `r = ⌈ln q⌉` into `MomentOptimizedSupNorm` gives the prize
floor `M ≤ √(2e·n·log q)`.  The sole open input is `MomentRatioPeakAtTwo` at `r ∼ log q`. -/
theorem eta_pow_le_of_peak {ψ : AddChar F ℂ} (G : Finset F)
    (hq : 1 ≤ Fintype.card F) (hG : G.Nonempty)
    (hpeak : MomentRatioPeakAtTwo ψ G) (hanchor : wickRatio ψ G 2 ≤ 1)
    {r : ℕ} (hr : 1 ≤ r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (doubleFactOdd r : ℝ) * (G.card : ℝ) ^ r :=
  eta_pow_le_of_wick G r (wickEnergyBound_of_peak G hq hG hpeak hanchor r hr) hb

end ArkLib.ProximityGap.MomentRatioPeak

#print axioms ArkLib.ProximityGap.MomentRatioPeak.wickEnergyBound_of_ratio_le_one
#print axioms ArkLib.ProximityGap.MomentRatioPeak.wickEnergyBound_of_peak
#print axioms ArkLib.ProximityGap.MomentRatioPeak.eta_pow_le_of_peak
