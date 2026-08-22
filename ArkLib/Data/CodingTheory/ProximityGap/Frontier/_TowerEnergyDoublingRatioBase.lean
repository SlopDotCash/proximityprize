/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-!
# Door (iv): the char-0 BASE of the tower-doubling energy recursion `Q_r(N)` (#444)

This file FORMALIZES the char-0 base of Shaw's tower-energy recursion seed
(`scripts/probes/_tower_energy_recursion_v1.py`, commit `a3f17c745`), which was so far ONLY a
Python probe with no Lean object.

## The object (Shaw's seed)

For the thin 2-power subgroup `μ_N ⊊ F_q*`, the doubling `μ_N ↪ μ_{2N}` gives the spectral splitting
`η_b(μ_{2N}) = η_b(μ_N) + η_{gb}(μ_N)` (`g` a coset rep of `μ_N` in `μ_{2N}`). Taking `2r`-th
moments, the per-level **tower-doubling ratio** is

  `Q_r(N) := E_r(μ_{2N}) / (2^r · E_r(μ_N))`,

where `E_r(G) = #{(x₁,…,x_{2r}) ∈ G^{2r} : Σ xᵢ = 0}` is the `r`-th additive energy. Shaw's seed
observed (numerically, float64) that **`Q_r(N) → 1` as `N → ∞`** — the doubled halves DECOHERE on
average, so the per-level energy factor approaches the variance-adding value `2^r` from above. This
is the OPPOSITE of the SUP, where the worst-`b` coherence stays pinned at `+1` (that is the open
wall). Shaw's synthesis: **AIC ⟺ `∏_levels Q_r ≤ K^r r!`**; the char-0 bottom supplies the `r!`
(Bessel/Lam–Leung proven), and the **thin-level `Q_r → 1` decay rate is the open part**.

## What THIS file does (the PROVABLE char-0 base, kernel-clean)

Shaw separated a provable char-0 base from the open thin-level coherence. This file pins that base
EXACTLY, using the in-tree kernel-proven char-0 energy closed forms (the `B2_closed`/`B4_closed`
ladder, `CharZeroEnergyThreeExact`): with `n = 2m`,

* `E₁(μ_n) = n = 2m`               (Parseval / diagonal),
* `E₂(μ_n) = 3n² − 3n = 12m² − 6m`.

The doubling `μ_N → μ_{2N}` is `m → 2m` on the antipodal-class count. We prove, AT THE CHAR-0 BASE:

* `towerRatio_one_eq_one`    : `Q₁(m) = 1` **EXACTLY** for all `m ≥ 1` — the `r = 1` level is
  Parseval-rigid (doubling exactly doubles the diagonal energy, the `2¹` cancels). No decoherence
  slack at all at the bottom moment.
* `towerRatio_two_eq`        : `Q₂(m) = (4m − 1) / (4m − 2)` **EXACTLY** (closed form).
* `towerRatio_two_gt_one`    : `Q₂(m) > 1` for all `m ≥ 1` — the doubled energy STRICTLY exceeds the
  variance-adding value `2²·E₂`, by the positive coherence excess.
* `towerRatio_two_sub_one`   : `Q₂(m) − 1 = 1 / (4m − 2)` — the EXACT excess; the decoherence rate.
* `towerRatio_two_le`        : `Q₂(m) ≤ 1 + 1/(4m − 2)` (= equality; the `→ 1` upper envelope).
* `towerRatio_two_antitone`  : `Q₂(m+1) < Q₂(m)` — STRICTLY DECREASING in `m` (monotone decoherence
  down the tower, the `1.50, 1.17, 1.07, 1.03, …` of Shaw's seed).
* `towerRatio_two_tendsto_one` : `Q₂(m) → 1` as `m → ∞` (the seed's central observation, made exact
  at the char-0 base via `Q₂ − 1 = 1/(4m−2) → 0`).

## Honest status (a char-0 BASE pin, NOT a CORE closure)

This is the **char-0 base** of the tower recursion — exactly the half Shaw flagged as provable. The
OPEN content is the SUP / thin-level (char-`p`) coherence: whether the worst-`b` `Q_r` (not the
average char-0 `Q_r`) also decays, which is the deep BGK/Paley wall and is UNTOUCHED here. The
average char-0 `Q_r → 1` proven here is a per-level energy (L²-averaged) statement; it does NOT
bound the SUP, and a `+1`-pinned worst-`b` coherence is fully compatible with `Q_r → 1` on average
(the average decoheres while the worst case may not). No CORE / cancellation / completion /
anti-concentration / moment-saving / capacity claim. The prize CORE stays OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.TowerEnergyDoublingRatioBase

/-- The char-0 depth-1 additive energy of `μ_n` (`n = 2m`): `E₁(μ_n) = n = 2m`. In-tree this is the
diagonal/Parseval energy `REnergyTwoExact` (`E₁ = |μ_n| = n`). -/
def E1 (m : ℝ) : ℝ := 2 * m

/-- The char-0 depth-2 additive energy of `μ_n` (`n = 2m`): `E₂(μ_n) = 3n² − 3n = 12m² − 6m`.
In-tree this is the kernel-proven `B4_closed` / `REnergyTwoExact.mu_n_rEnergy_two_eq`. -/
def E2 (m : ℝ) : ℝ := 12 * m ^ 2 - 6 * m

/-- The **tower-doubling ratio at depth 1**: `Q₁(m) = E₁(μ_{2n}) / (2¹ · E₁(μ_n))`, i.e. with the
doubling `m → 2m` on the antipodal-class count, `Q₁(m) = E1 (2m) / (2 · E1 m)`. -/
noncomputable def towerRatioOne (m : ℝ) : ℝ := E1 (2 * m) / (2 * E1 m)

/-- The **tower-doubling ratio at depth 2**: `Q₂(m) = E₂(μ_{2n}) / (2² · E₂(μ_n))`, i.e.
`Q₂(m) = E2 (2m) / (4 · E2 m)`. -/
noncomputable def towerRatioTwo (m : ℝ) : ℝ := E2 (2 * m) / (4 * E2 m)

/-- **`Q₁(m) = 1` EXACTLY** for `m ≥ 1`. The depth-1 (Parseval) level is rigid under doubling: the
diagonal energy exactly doubles, and the `2¹` normalization cancels it. No decoherence slack at the
bottom moment. -/
theorem towerRatio_one_eq_one {m : ℝ} (hm : 1 ≤ m) : towerRatioOne m = 1 := by
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm
  have hne : (0 : ℝ) < 2 * E1 m := by unfold E1; positivity
  unfold towerRatioOne
  rw [div_eq_one_iff_eq (ne_of_gt hne)]
  unfold E1; ring

/-- **`Q₂(m) = (4m − 1)/(4m − 2)` EXACTLY** for `m ≥ 1`. The closed form of the depth-2
tower-doubling ratio at the char-0 base. -/
theorem towerRatio_two_eq {m : ℝ} (hm : 1 ≤ m) :
    towerRatioTwo m = (4 * m - 1) / (4 * m - 2) := by
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm
  have hE2 : (0 : ℝ) < E2 m := by unfold E2; nlinarith [hmpos, hm]
  have hd : (0 : ℝ) < 4 * m - 2 := by nlinarith
  have h4 : (4 : ℝ) * E2 m ≠ 0 := by positivity
  rw [towerRatioTwo, div_eq_div_iff h4 (ne_of_gt hd)]
  unfold E2
  ring

/-- **`Q₂(m) − 1 = 1/(4m − 2)`** for `m ≥ 1` — the EXACT coherence excess (the per-level decoherence
rate at the char-0 base). -/
theorem towerRatio_two_sub_one {m : ℝ} (hm : 1 ≤ m) :
    towerRatioTwo m - 1 = 1 / (4 * m - 2) := by
  have hd : (4 * m - 2 : ℝ) ≠ 0 := by nlinarith
  rw [towerRatio_two_eq hm]
  field_simp
  ring

/-- **`Q₂(m) > 1`** for `m ≥ 1`. The doubled depth-2 energy strictly exceeds the variance-adding
value `2²·E₂` — the positive (decohering) coherence excess. -/
theorem towerRatio_two_gt_one {m : ℝ} (hm : 1 ≤ m) : 1 < towerRatioTwo m := by
  have hd : (0 : ℝ) < 4 * m - 2 := by nlinarith
  have h := towerRatio_two_sub_one hm
  have hpos : (0 : ℝ) < 1 / (4 * m - 2) := by positivity
  linarith [h ▸ hpos]

/-- **`Q₂(m) ≤ 1 + 1/(4m − 2)`** for `m ≥ 1` (in fact equality) — the explicit `→ 1` upper envelope
of the char-0 tower-doubling ratio. -/
theorem towerRatio_two_le {m : ℝ} (hm : 1 ≤ m) :
    towerRatioTwo m ≤ 1 + 1 / (4 * m - 2) := by
  have h := towerRatio_two_sub_one hm
  linarith

/-- **`Q₂` is STRICTLY DECREASING**: `Q₂(m+1) < Q₂(m)` for `m ≥ 1`. Monotone decoherence down the
tower (`1.50, 1.17, 1.07, 1.03, …` of Shaw's seed). -/
theorem towerRatio_two_antitone {m : ℝ} (hm : 1 ≤ m) :
    towerRatioTwo (m + 1) < towerRatioTwo m := by
  have hm1 : (1 : ℝ) ≤ m + 1 := by linarith
  have hd0 : (0 : ℝ) < 4 * m - 2 := by nlinarith
  have hd1 : (0 : ℝ) < 4 * (m + 1) - 2 := by nlinarith
  have e0 := towerRatio_two_sub_one hm
  have e1 := towerRatio_two_sub_one hm1
  have hlt : 1 / (4 * (m + 1) - 2) < 1 / (4 * m - 2) := by
    apply one_div_lt_one_div_of_lt hd0
    linarith
  linarith [e0, e1]

/-- **`Q₂(m) → 1` as `m → ∞`** (the seed's central observation, exact at the char-0 base).
Proven via the exact excess `Q₂(m) − 1 = 1/(4m − 2) → 0`. -/
theorem towerRatio_two_tendsto_one :
    Filter.Tendsto (fun m : ℝ => towerRatioTwo m) Filter.atTop (nhds 1) := by
  have hev : ∀ᶠ m : ℝ in Filter.atTop, towerRatioTwo m = 1 + 1 / (4 * m - 2) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    have := towerRatio_two_sub_one hm
    linarith
  rw [Filter.tendsto_congr' hev]
  have h1 : Filter.Tendsto (fun m : ℝ => 4 * m - 2) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
  have h2 : Filter.Tendsto (fun m : ℝ => 1 / (4 * m - 2)) Filter.atTop (nhds 0) := by
    simpa using h1.inv_tendsto_atTop
  have h3 : Filter.Tendsto (fun m : ℝ => 1 + 1 / (4 * m - 2)) Filter.atTop (nhds (1 + 0)) :=
    Filter.Tendsto.const_add 1 h2
  simpa using h3

end ProximityGap.Frontier.TowerEnergyDoublingRatioBase

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBase.towerRatio_one_eq_one
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBase.towerRatio_two_eq
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBase.towerRatio_two_sub_one
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBase.towerRatio_two_gt_one
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBase.towerRatio_two_le
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBase.towerRatio_two_antitone
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBase.towerRatio_two_tendsto_one
