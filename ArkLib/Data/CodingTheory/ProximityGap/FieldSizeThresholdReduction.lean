/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld

/-!
# The field-size lever for the deployed δ* pin (#389)

The deployed-regime reduction `interiorCeiling_of_censusDomination` consumes a census bound `K`
through the hypothesis `(K : ℝ≥0∞)/p ≤ ε*`. This file isolates the **field-size dependence** of
that hypothesis as a machine-checked theorem: a census bound `K` that is **independent of the
field size** `p` (the only kind the curve-sparsity / additive-energy routes produce — those bound
the list by a function of `n` alone) discharges the obligation **for every field with
`p ≥ K · D`**, where `D = 1/ε*` (`= 2^{128}` at the prize budget).

> **`censusDomination_pin_largeField`** — if `ε* = D⁻¹`, `K · D ≤ p`, and
> `CensusDomination` holds with the `n`-only bound `K`, then `InteriorCeiling` holds, hence the
> pin `δ* = 1 − r/2^μ`.

**Why this matters for the prize (see `docs/kb/deltastar-prize-regime-reduction-2026-06-13.md`).**
The open core is the census/list bound `K`. The Mérai–Shparlinski curve-sparsity route would give
a `q`-independent `K ≈ n^{3/2}`; the additive-energy route targets `K ≈ n`. This theorem says: the
*larger* the field, the *weaker* the list bound that suffices — at `p ≈ n·2^{128}` (deployed) one
needs `K ≲ n` (the sharp `n^{2+o(1)}` energy), but at `p ≳ n^{3/2}·2^{128}` an `n^{3/2}` list bound
already closes the window. It cleanly separates the prize by field size and turns the informal
"large field ⇒ weaker requirement" into a proven reduction; the residual is exactly the
`n`-only census bound `K`, nothing else.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open scoped ENNReal
open ProximityGap.KKH26DeltaStarReduction

namespace ProximityGap.Ownership

variable {p : ℕ} [Fact p.Prime]

/-- **The field-size lever.** A field-size-independent census bound `K` discharges the interior
ceiling for every field large enough that `K · D ≤ p`, where `ε* = D⁻¹`. So the list/census bound
needed to pin `δ* = 1 − r/2^μ` weakens as the field grows: `K ≤ p/D = p·ε*`. -/
theorem censusDomination_pin_largeField
    {μ m r : ℕ} (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hr2 : 2 ≤ r) {n : ℕ} (hn : n = 2 ^ μ * m)
    [NeZero n] {g : ZMod p} (hg : orderOf g = n) {K D : ℕ} (hD : 0 < D)
    {εstar : ℝ≥0∞} (hε : εstar = (D : ℝ≥0∞)⁻¹) (hp : K * D ≤ p)
    (hdom : CensusDomination (smoothDom g n hg) ((r - 2) * m + 1) (r * m + 1) K) :
    InteriorCeiling p n g μ m r εstar := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hppos.ne'
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hD0 : (D : ℝ≥0∞) ≠ 0 := by exact_mod_cast hD.ne'
  have hDt : (D : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top D
  -- the field-size hypothesis K·D ≤ p gives (K:ℝ≥0∞)/p ≤ D⁻¹ = ε*
  have hK : (K : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar := by
    rw [hε]
    have h1 : (D : ℝ≥0∞) * (K : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by
      rw [mul_comm]; exact_mod_cast hp
    have hKle : (K : ℝ≥0∞) ≤ (D : ℝ≥0∞)⁻¹ * (p : ℝ≥0∞) := by
      calc (K : ℝ≥0∞) = (D : ℝ≥0∞)⁻¹ * ((D : ℝ≥0∞) * (K : ℝ≥0∞)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDt, one_mul]
        _ ≤ (D : ℝ≥0∞)⁻¹ * (p : ℝ≥0∞) := mul_le_mul_left' h1 _
    exact ENNReal.div_le_of_le_mul hKle
  exact interiorCeiling_of_censusDomination hμ hm hr2 hn hg εstar hK hdom

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.censusDomination_pin_largeField
