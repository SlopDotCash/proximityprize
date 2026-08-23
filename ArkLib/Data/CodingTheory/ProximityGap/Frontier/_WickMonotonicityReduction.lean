/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.WickMomentCapability
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SecondMomentExact

/-!
# Reframing the #407 prize floor as a single-step Wick monotonicity (#407, comment c.318)

The prize floor — the deep-moment finite-field inequality `A_r ≤ Wick_r` **for all** `r` (in the
thin prize regime, at depth `r ≈ log q`) — is the BGK / anomaly-suppression core. Here

* `A_r := (1/q)·∑_{b≠0} ‖η_b‖^{2r}` is the **DC-subtracted** `2r`-th Gauss-period moment
  (`eta`, `sum_nonzero_moment`); equivalently `A_r = E_r(G) − |G|^{2r}/q`.
* `Wick_r := (2r-1)‼·|G|^r` is the **Wick value** (the `2r`-th moment of a real Gaussian of
  variance `|G|`; the odd coefficient is `WickMomentCapability.oddWickCoeff`).

This file formalizes the **reduction** of comment c.318, NOT the floor. Define `f r = A_r / Wick_r`.
The reframing is the elementary monotonicity ladder

> `f 1 ≤ 1`  **AND**  (`∀ r ≥ 1, f (r+1) ≤ f r`)  ⟹  `∀ r ≥ 1, f r ≤ 1`  ⟹  `A_r ≤ Wick_r ∀ r ≥ 1`.

The **base case `f 1 ≤ 1`** is the in-tree proven lemma
`ProximityGap.Frontier.SecondMomentExact.base_case_strict` (`∑_{b≠0}‖η_b‖² < q·|G|`, i.e.
`A_1 < |G| = Wick_1`); we consume the REAL base case here — no re-proof.

The **single-step monotonicity** `f (r+1) ≤ f r` — i.e. `A_{r+1}/Wick_{r+1} ≤ A_r/Wick_r` — is the
remaining OPEN BGK content (`WickMonotonicity`, an explicit named `Prop`, never a `sorry` and never
vacuously discharged: honesty contract §6). It is **thinness-essential**: the probe
`scripts/probes/probe_407_ArWick_monotone_thinness.py` exhibits, by exact integer FFT, that
`f 1 ≤ 1 ∧ (f monotone-decreasing)` HOLDS in the thin prize window but FAILS in the thick window
(at the maximally-structured `n=32`, `F_4129`, `β=2.40`: `A_2 = 3490 > Wick = 3072`, and `f` rises
to `1.705` at `r=5`). So a floor proof routed through `[base] + [single-step monotonicity]` is
automatically thinness-essential — exactly the rule-3 property a real lever must have.

**Deliverable = the reduction (open core ⟹ floor), not the floor.** Two layers:
1. `antitone_le_one_of_base` — the abstract `ℕ → ℝ` monotonicity ladder (trivial induction).
2. `floorViaWick_of_monotonicity` — its specialization wiring the REAL `eta`/`rEnergy`/Wick and the
   REAL `base_case_strict`, producing `A_r ≤ Wick_r ∀ r ≥ 1` conditional on the named
   `WickMonotonicity`.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

namespace ProximityGap.Frontier.WickMonotonicityReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Layer 1 — the abstract monotonicity ladder

A purely real-analytic fact: an antitone-from-the-base sequence `f : ℕ → ℝ` that starts `≤ 1` at
`r = 1` stays `≤ 1` for all `r ≥ 1`. This is the load-bearing logical content of the reduction;
everything else is plumbing the prize objects into it. -/

/-- **The abstract ladder.** If `f 1 ≤ 1` and `f` is single-step antitone from `r = 1` onward
(`∀ r ≥ 1, f (r+1) ≤ f r`), then `f r ≤ 1` for every `r ≥ 1`. Plain induction on the gap `r - 1`. -/
theorem antitone_le_one_of_base (f : ℕ → ℝ) (hbase : f 1 ≤ 1)
    (hstep : ∀ r, 1 ≤ r → f (r + 1) ≤ f r) :
    ∀ r, 1 ≤ r → f r ≤ 1 := by
  intro r hr
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  clear hr
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
      exact le_trans (hstep (k + 1) (by omega)) ih

/-! ## Layer 2 — the named prize objects and the reduction

`Ar`, `Wick`, and the ratio `wickRatio = Ar / Wick` are the concrete instantiations over the REAL
in-tree Gauss period `eta` and additive energy. `base_case_strict` (in-tree, proven) supplies
`wickRatio 1 ≤ 1`; the open core is the named `WickMonotonicity`. -/

/-- The **DC-subtracted `2r`-th Gauss-period moment**, normalized by `q`:
`A_r = (1/q)·∑_{b≠0} ‖η_b‖^{2r}`. The prize object whose deep-`r` (depth `r ≈ log q`) control is the
floor. By `sum_nonzero_moment`, `A_r = E_r(G) − |G|^{2r}/q`. -/
noncomputable def Ar (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : ℝ :=
  (1 / (Fintype.card F : ℝ)) * ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)

/-- The **Wick value** `Wick_r = (2r-1)‼·|G|^r` — the `2r`-th moment of a real Gaussian of variance
`|G|` (`WickMomentCapability.oddWickCoeff`). The floor `A_r ≤ Wick_r` says the Gauss-period family
is sub-Gaussian in its DC-subtracted moments. -/
noncomputable def Wick (G : Finset F) (r : ℕ) : ℝ :=
  (WickMomentCapability.oddWickCoeff r : ℝ) * (G.card : ℝ) ^ r

/-- The ratio `f r = A_r / Wick_r` whose monotonicity is the reframed open core. -/
noncomputable def wickRatio (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : ℝ :=
  Ar ψ G r / Wick G r

/-- `(2r-1)‼ > 0`: the odd Wick coefficient is a product of strictly-positive odd numbers. -/
theorem oddWickCoeff_pos (r : ℕ) : 0 < WickMomentCapability.oddWickCoeff r := by
  rw [WickMomentCapability.oddWickCoeff]
  exact Finset.prod_pos (fun i _ => Nat.succ_pos _)

/-- `Wick_r > 0` for nonempty `G`: both `(2r-1)‼ > 0` and `|G|^r > 0`. -/
theorem Wick_pos {G : Finset F} (hG : G.Nonempty) (r : ℕ) : 0 < Wick G r := by
  have hcard : 0 < G.card := Finset.card_pos.mpr hG
  have hdf : (0 : ℝ) < (WickMomentCapability.oddWickCoeff r : ℝ) := by
    exact_mod_cast oddWickCoeff_pos r
  have hpow : (0 : ℝ) < (G.card : ℝ) ^ r := by positivity
  unfold Wick
  positivity

/-- `Wick_1 = |G|`: the base Wick value is exactly the cardinality (`(2·1−1)‼ = 1!! = 1`). -/
theorem Wick_one (G : Finset F) : Wick G 1 = (G.card : ℝ) := by
  unfold Wick
  simp [WickMomentCapability.oddWickCoeff]

/-- **The base case, wired to the in-tree proven lemma.** `wickRatio 1 = A_1 / Wick_1 ≤ 1`.
This consumes the REAL `base_case_strict` (`∑_{b≠0}‖η_b‖² < q·|G|`): dividing by `q > 0` gives
`A_1 < |G| = Wick_1`, so `f 1 = A_1/Wick_1 < 1`. (No re-proof of the base case — it is the
in-tree exact second-moment result.) -/
theorem wickRatio_one_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} (hG : G.Nonempty) :
    wickRatio ψ G 1 ≤ 1 := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have := Fintype.card_pos (α := F)
    exact_mod_cast this
  -- A_1 = (1/q)·∑_{b≠0}‖η_b‖²  and  base_case_strict : ∑_{b≠0}‖η_b‖² < q·|G|
  have hbase := ProximityGap.Frontier.SecondMomentExact.base_case_strict hψ G hG
  have hA1 : Ar ψ G 1 < (G.card : ℝ) := by
    unfold Ar
    rw [show (2 * 1) = 2 from rfl, one_div, ← div_eq_inv_mul, div_lt_iff₀ hq]
    linarith [hbase]
  -- f 1 = A_1 / Wick_1 = A_1 / |G| < 1 ≤ 1
  unfold wickRatio
  rw [Wick_one]
  have hcardpos : (0 : ℝ) < (G.card : ℝ) := by
    have : 0 < G.card := Finset.card_pos.mpr hG
    exact_mod_cast this
  rw [div_le_one hcardpos]
  linarith [hA1]

/-- **The open BGK core — the single-step Wick monotonicity (a named hypothesis, NOT proven here).**
`A_{r+1}/Wick_{r+1} ≤ A_r/Wick_r` for every `r ≥ 1`. This is the deep-moment inequality at depth
`r ≈ log q`; the probe `probe_407_ArWick_monotone_thinness.py` shows it holds in the thin prize
window but FAILS in the thick window — so it is **thinness-essential**. It remains OPEN (= BGK
content); we never `sorry` it nor discharge it vacuously. -/
def WickMonotonicity (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  ∀ r, 1 ≤ r → wickRatio ψ G (r + 1) ≤ wickRatio ψ G r

/-- The same open core with denominators cleared. This is often the exact algebraic form one wants
to attack: the next DC-subtracted moment, weighted by the present Wick value, is at most the present
moment weighted by the next Wick value. It is only a definition here, not a proof of the inequality. -/
def WickStepCross (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  ∀ r, 1 ≤ r → Ar ψ G (r + 1) * Wick G r ≤ Ar ψ G r * Wick G (r + 1)

/-- Clearing the positive Wick denominators: ratio monotonicity implies the cross-multiplied step. -/
theorem wickStepCross_of_monotonicity {ψ : AddChar F ℂ} {G : Finset F} (hG : G.Nonempty)
    (hmono : WickMonotonicity ψ G) : WickStepCross ψ G := by
  intro r hr
  have hWr : 0 < Wick G r := Wick_pos hG r
  have hWnext : 0 < Wick G (r + 1) := Wick_pos hG (r + 1)
  have h := hmono r hr
  unfold wickRatio at h
  calc
    Ar ψ G (r + 1) * Wick G r
        = (Ar ψ G (r + 1) / Wick G (r + 1)) * (Wick G (r + 1) * Wick G r) := by
            field_simp [ne_of_gt hWnext]
    _ ≤ (Ar ψ G r / Wick G r) * (Wick G (r + 1) * Wick G r) := by
            exact mul_le_mul_of_nonneg_right h (le_of_lt (mul_pos hWnext hWr))
    _ = Ar ψ G r * Wick G (r + 1) := by
            field_simp [ne_of_gt hWr]

/-- Conversely, the cross-multiplied step is exactly ratio monotonicity once the Wick denominators
are known positive (here supplied by `G.Nonempty`). -/
theorem monotonicity_of_wickStepCross {ψ : AddChar F ℂ} {G : Finset F} (hG : G.Nonempty)
    (hcross : WickStepCross ψ G) : WickMonotonicity ψ G := by
  intro r hr
  have hWr : 0 < Wick G r := Wick_pos hG r
  have hWnext : 0 < Wick G (r + 1) := Wick_pos hG (r + 1)
  have h := hcross r hr
  unfold wickRatio
  calc
    Ar ψ G (r + 1) / Wick G (r + 1)
        = (Ar ψ G (r + 1) * Wick G r) / (Wick G (r + 1) * Wick G r) := by
            field_simp [ne_of_gt hWr, ne_of_gt hWnext]
    _ ≤ (Ar ψ G r * Wick G (r + 1)) / (Wick G (r + 1) * Wick G r) := by
            exact div_le_div_of_nonneg_right h (le_of_lt (mul_pos hWnext hWr))
    _ = Ar ψ G r / Wick G r := by
            field_simp [ne_of_gt hWr, ne_of_gt hWnext]

/-- The ratio and denominator-cleared formulations of the single open step are equivalent. -/
theorem wickMonotonicity_iff_wickStepCross {ψ : AddChar F ℂ} {G : Finset F} (hG : G.Nonempty) :
    WickMonotonicity ψ G ↔ WickStepCross ψ G :=
  ⟨wickStepCross_of_monotonicity hG, monotonicity_of_wickStepCross hG⟩

/-- **The prize floor (as a named target).** `A_r ≤ Wick_r` for all `r ≥ 1`: the DC-subtracted
Gauss-period moments are sub-Gaussian at every depth. This is what the reduction PRODUCES from the
open core. -/
def FloorViaWick (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  ∀ r, 1 ≤ r → Ar ψ G r ≤ Wick G r

/-- **THE REDUCTION (open core ⟹ floor).** The single-step `WickMonotonicity` plus the in-tree
proven base case `wickRatio_one_le` together give the full floor `FloorViaWick`
(`A_r ≤ Wick_r ∀ r ≥ 1`).

Mechanism: `antitone_le_one_of_base` lifts `[f 1 ≤ 1] + [f (r+1) ≤ f r]` to `f r ≤ 1 ∀ r ≥ 1`;
then `f r = A_r/Wick_r ≤ 1` with `Wick_r > 0` unfolds to `A_r ≤ Wick_r`. The floor is therefore
**exactly** the single named open inequality `WickMonotonicity` — this is the c.318 reframing. -/
theorem floorViaWick_of_monotonicity {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hG : G.Nonempty) (hmono : WickMonotonicity ψ G) :
    FloorViaWick ψ G := by
  -- Step 1: the ratio f r = wickRatio ψ G r stays ≤ 1 for all r ≥ 1.
  have hratio : ∀ r, 1 ≤ r → wickRatio ψ G r ≤ 1 :=
    antitone_le_one_of_base (wickRatio ψ G) (wickRatio_one_le hψ hG) hmono
  -- Step 2: f r ≤ 1 with Wick_r > 0 unfolds to A_r ≤ Wick_r.
  intro r hr
  have hWpos : 0 < Wick G r := Wick_pos hG r
  have hle := hratio r hr
  unfold wickRatio at hle
  rwa [div_le_one hWpos] at hle

/-- **Denominator-cleared consumer form.** It is enough to prove the cross-multiplied Wick step
`A_{r+1} * Wick_r ≤ A_r * Wick_{r+1}` for every `r ≥ 1`; together with the proven Parseval
base case, that gives the full floor. This is just `floorViaWick_of_monotonicity` after the
positive-denominator equivalence above, so the only open input is still the same step inequality. -/
theorem floorViaWick_of_wickStepCross {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hG : G.Nonempty) (hcross : WickStepCross ψ G) :
    FloorViaWick ψ G :=
  floorViaWick_of_monotonicity hψ hG (monotonicity_of_wickStepCross hG hcross)

end ProximityGap.Frontier.WickMonotonicityReduction

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ProximityGap.Frontier.WickMonotonicityReduction.antitone_le_one_of_base
#print axioms ProximityGap.Frontier.WickMonotonicityReduction.wickRatio_one_le
#print axioms ProximityGap.Frontier.WickMonotonicityReduction.wickMonotonicity_iff_wickStepCross
#print axioms ProximityGap.Frontier.WickMonotonicityReduction.floorViaWick_of_monotonicity
#print axioms ProximityGap.Frontier.WickMonotonicityReduction.floorViaWick_of_wickStepCross
