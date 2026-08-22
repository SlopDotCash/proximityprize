/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The DC-centered fluctuation sharpening of the prize criterion (#444)

This brick sharpens the corrected (DC-subtracted) prize criterion `ρ_r ≤ 1` of `_RhoDecomposition`
into a **centered-fluctuation bound**, exploiting the DC lower bound on the `2r`-th energy.

Setup (over `F_p`, `n = 2^a`, depth `r`, `Wick = (2r−1)‼·n^r`, all reals):
* `E_r = E0 + W` — char-`p` energy = char-0 energy `E0` plus wraparound `W ≥ 0` (`_RhoDecomposition`).
* `S_r = p·E_r − n^{2r} = Σ_{b≠0}‖η_b‖^{2r}` (the DC-subtracted `2r`-th moment).
* `ρ_r = S_r / ((p−1)·Wick)` — prize criterion (`ρ_r ≤ 1 ⟹ M ≤ √e·√(2rn)`).
* **DC lower bound** `E_r ≥ n^{2r}/p` — Cauchy–Schwarz over the `p` residue classes of the moment sum
  (the principal/DC class `η_0 = n` contributes `n^{2r}/p` after averaging): the energy can never fall
  below its DC floor.  This is the standing hypothesis `hDC : n2r / p ≤ E_r`.

## The sharpening

The key identity (`rho_le_one_iff_fluctuation_le`, proven from `_RhoDecomposition`'s algebra by clearing
the denominator `p`; needs `1 < p`, true for the prime `p`) is the **exact** equivalence

  `ρ_r ≤ 1  ⟺  (E_r − n^{2r}/p) ≤ Wick·(p−1)/p`.

Reading: `E_r − n^{2r}/p` is the **energy fluctuation above the DC floor** — by `hDC` it is `≥ 0`
(`fluctuation_nonneg`), a genuine *centered* quantity.  The prize criterion is precisely that this
fluctuation stays within the budget `Wick·(p−1)/p = Wick·(1 − 1/p)`, which is **strictly below `Wick`**
(`budget_lt_wick`).  So at prize scale the open core is a *sub-Wick fluctuation bound*, not a bound on the
raw (DC-dominated) energy `E_r` itself.

Centered on the wraparound: substituting `E_r = E0 + W` recovers exactly `W ≤ slack` of `_RhoDecomposition`
(`fluctuation_form_eq_wraparound_form`), so the two forms are equivalent — but the DC-centered LHS
`E_r − n^{2r}/p` is the one that is **manifestly nonnegative** under `hDC` and is compared against a budget
**below `Wick`**.  That is the sharp quantified statement of growing-order equidistribution: the centered
energy fluctuation above its own DC floor must not exceed `(1 − 1/p)·Wick`.

This is not a closure — bounding the fluctuation at deep `r ≈ log p` in the thin regime is the open wall —
but it is the cleanest *centered* exact reduction, isolating a nonnegative fluctuation against a sub-Wick budget.

`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace ProximityGap.FluctuationSharpening

/-- The DC-subtracted moment `S_r = p·E_r − n^{2r}` with `E_r = E0 + W`. -/
def dcMoment (p E0 W n2r : ℝ) : ℝ := p * (E0 + W) - n2r

/-- The prize criterion ratio `ρ_r = S_r / ((p−1)·Wick)`. -/
noncomputable def rho (p E0 W n2r Wick : ℝ) : ℝ := dcMoment p E0 W n2r / ((p - 1) * Wick)

/-- The energy fluctuation above the DC floor: `E_r − n^{2r}/p` (with `E_r = E0 + W`). -/
noncomputable def fluctuation (p E0 W n2r : ℝ) : ℝ := (E0 + W) - n2r / p

/-- The fluctuation budget `Wick·(p−1)/p = Wick·(1 − 1/p)`. -/
noncomputable def budget (p Wick : ℝ) : ℝ := Wick * (p - 1) / p

/-- **The DC-centered fluctuation form of the prize criterion.**  With `1 < p` and `Wick > 0`, the corrected
criterion `ρ_r ≤ 1` is *exactly equivalent* to the centered bound `(E_r − n^{2r}/p) ≤ Wick·(p−1)/p`: the
energy fluctuation above its DC floor is at most `(1 − 1/p)·Wick`. -/
theorem rho_le_one_iff_fluctuation_le
    (p E0 W n2r Wick : ℝ) (hp : 1 < p) (hW : 0 < Wick) :
    rho p E0 W n2r Wick ≤ 1 ↔ fluctuation p E0 W n2r ≤ budget p Wick := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hden : (0 : ℝ) < (p - 1) * Wick := mul_pos hp1 hW
  rw [rho, dcMoment, fluctuation, budget, div_le_one hden]
  -- clear the `/p` on the fluctuation side by multiplying through by `p > 0`
  have key : ((E0 + W) - n2r / p ≤ Wick * (p - 1) / p)
      ↔ (p * ((E0 + W) - n2r / p) ≤ p * (Wick * (p - 1) / p)) :=
    (mul_le_mul_iff_of_pos_left hp0).symm
  have e1 : p * ((E0 + W) - n2r / p) = p * (E0 + W) - n2r := by field_simp
  have e2 : p * (Wick * (p - 1) / p) = (p - 1) * Wick := by field_simp
  rw [key, e1, e2]

/-- **The fluctuation is nonnegative under the DC lower bound.**  If the `2r`-th energy obeys its DC floor
`E_r ≥ n^{2r}/p` (Cauchy–Schwarz over the `p` residue classes), then the fluctuation `E_r − n^{2r}/p` is
`≥ 0` — so the criterion bounds a genuine *centered* (nonnegative) quantity. -/
theorem fluctuation_nonneg
    (p E0 W n2r : ℝ) (hDC : n2r / p ≤ E0 + W) :
    0 ≤ fluctuation p E0 W n2r := by
  rw [fluctuation]; linarith

/-- **The fluctuation budget is strictly below `Wick`.**  For `1 < p` and `Wick > 0`,
`Wick·(p−1)/p < Wick`: the centered energy fluctuation must stay *below* the full Wick value, even though
the raw energy `E_r` is DC-dominated and far exceeds `Wick`. -/
theorem budget_lt_wick (p Wick : ℝ) (hp : 1 < p) (hW : 0 < Wick) :
    budget p Wick < Wick := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  rw [budget, div_lt_iff₀ hp0]
  nlinarith [hW, hp0, hp]

/-- **The budget equals `Wick·(1 − 1/p)`.**  An explicit closed form for the fluctuation budget. -/
theorem budget_eq (p Wick : ℝ) (hp : 1 < p) :
    budget p Wick = Wick * (1 - 1 / p) := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  rw [budget]; field_simp

/-- **Equivalence of the DC-centered and wraparound-centered forms.**  The fluctuation bound
`(E_r − n^{2r}/p) ≤ Wick·(p−1)/p` is *exactly* the wraparound bound `W ≤ (Wick − E0) + (n^{2r} − Wick)/p`
of `_RhoDecomposition` (`slack`).  So the sharpening adds no hypothesis and loses no information: it is a
*recentring* of the same criterion onto the manifestly-nonnegative DC-floor fluctuation. -/
theorem fluctuation_form_eq_wraparound_form
    (p E0 W n2r Wick : ℝ) (hp : 1 < p) :
    (fluctuation p E0 W n2r ≤ budget p Wick)
      ↔ (W ≤ (Wick - E0) + (n2r - Wick) / p) := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  rw [fluctuation, budget]
  have key : ((E0 + W) - n2r / p ≤ Wick * (p - 1) / p)
      ↔ (p * ((E0 + W) - n2r / p) ≤ p * (Wick * (p - 1) / p)) :=
    (mul_le_mul_iff_of_pos_left hp0).symm
  have key2 : (W ≤ (Wick - E0) + (n2r - Wick) / p)
      ↔ (p * W ≤ p * ((Wick - E0) + (n2r - Wick) / p)) :=
    (mul_le_mul_iff_of_pos_left hp0).symm
  rw [key, key2]
  have e1 : p * ((E0 + W) - n2r / p) = p * (E0 + W) - n2r := by field_simp
  have e2 : p * (Wick * (p - 1) / p) = (p - 1) * Wick := by field_simp
  have e3 : p * ((Wick - E0) + (n2r - Wick) / p) = p * (Wick - E0) + (n2r - Wick) := by
    field_simp
  rw [e1, e2, e3]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **The sharpened prize criterion, packaged with the DC floor.**  Under the DC lower bound `hDC`, the
criterion `ρ_r ≤ 1` is equivalent to bounding the *nonnegative* fluctuation `0 ≤ E_r − n^{2r}/p` by the
*sub-Wick* budget `Wick·(p−1)/p < Wick`.  This is the centered-fluctuation form of the open core:
a nonnegative quantity bounded by a budget strictly below `Wick`. -/
theorem prize_criterion_is_centered_fluctuation_bound
    (p E0 W n2r Wick : ℝ) (hp : 1 < p) (hW : 0 < Wick) (hDC : n2r / p ≤ E0 + W) :
    (rho p E0 W n2r Wick ≤ 1)
      ↔ (0 ≤ fluctuation p E0 W n2r ∧ fluctuation p E0 W n2r ≤ budget p Wick) := by
  rw [rho_le_one_iff_fluctuation_le p E0 W n2r Wick hp hW]
  constructor
  · intro h; exact ⟨fluctuation_nonneg p E0 W n2r hDC, h⟩
  · intro h; exact h.2

end ProximityGap.FluctuationSharpening
