/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The step-ratio monotonicity reduction of the char-`p` Wick bound (#444)

Attacking the target `E_{r+1}(μ_n;F_p) ≤ (2r+1)·n·E_r` (the prize, equivalently `E_r ≤ (2r−1)‼·n^r`):
machine data (`crossterm2.py`) shows the **step ratio** `R(r) := E_{r+1}/((2r+1)·n·E_r)` is
`< 1` and **monotonically DECREASING** at prize-scale primes (`0.847, 0.791, 0.740, 0.695, 0.656, 0.623`
for `r=2..7`). This file lands the clean consequence: **if `R` is antitone and `R(r₀) ≤ 1`, then `R(r) ≤
1` for all `r ≥ r₀`** — so the entire char-`p` Wick bound reduces to (i) a finite base case `R(r₀) ≤ 1`
(machine-checkable) plus (ii) the **monotonicity** `R(r+1) ≤ R(r)`, a single structural inequality.

This is a genuinely new reduction target (the in-tree `_wf7W3` reduces to `R(r) ≤ 1` *pointwise for all r*;
here we further reduce to *monotonicity + one base case*, which the data strongly supports). The
monotonicity itself is the open input — but it is a sharper, lower-dimensional object than "bound a
character sum at every depth".

We work abstractly with a real sequence `R : ℕ → ℝ` (the step ratios). The connection to the energies
(`R(r) = E_{r+1}/((2r+1)·n·E_r)`, and `R(r) ≤ 1 ⟺ E_{r+1} ≤ (2r+1)·n·E_r`) is the in-tree
`_EnergyRatioMonotoneReduction` / `_wf7W3`; here we supply the monotonicity-suffices step.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.StepRatioMonotone

/-- **Monotonicity + base case ⟹ the step ratio stays `≤ 1`.** If the step-ratio sequence `R` is antitone
from `r₀` (`R(r+1) ≤ R(r)` for `r ≥ r₀`) and the base value `R(r₀) ≤ 1`, then `R(r) ≤ 1` for every
`r ≥ r₀`. Hence the char-`p` Wick bound (`R(r) ≤ 1 ∀r ≥ r₀`) reduces to ONE base check + monotonicity. -/
theorem stepRatio_le_one_of_antitone_base {R : ℕ → ℝ} {r₀ : ℕ}
    (hbase : R r₀ ≤ 1) (hmono : ∀ r, r₀ ≤ r → R (r + 1) ≤ R r) :
    ∀ r, r₀ ≤ r → R r ≤ 1 := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih => exact le_trans (hmono k hk) ih

/-- **The energy form: monotone step ⟹ the Wick step bound at every depth.** With `R(r) = E_{r+1}/c(r)`
where `c(r) = (2r+1)·n·E_r > 0`, `R(r) ≤ 1 ↔ E_{r+1} ≤ c(r)`. Combining with
`stepRatio_le_one_of_antitone_base`, antitone `R` + base `E_{r₀+1} ≤ c(r₀)` gives `E_{r+1} ≤ (2r+1)·n·E_r`
for all `r ≥ r₀` — the per-step char-`p` Wick bound, telescoping (in-tree `_wf7W3`) to `E_r ≤ (2r−1)‼·n^r`.
We record the clean `R(r) ≤ 1 ↔ E_{r+1} ≤ c(r)` bridge. -/
theorem stepRatio_le_one_iff_energy {Enext c R : ℝ} (hc : 0 < c) (hR : R = Enext / c) :
    R ≤ 1 ↔ Enext ≤ c := by
  subst hR
  rw [div_le_one hc]

/-- **Non-vacuity.** The hypotheses are jointly satisfiable (so the reduction is not a vacuous-hypothesis
artifact): any antitone sequence bounded by `1` at the base — here the constant `R ≡ 1` (`le_refl`) —
yields the conclusion. The measured step ratios `0.847 > 0.791 > … > 0.623 < 1` are a strict instance of
this shape. -/
theorem stepRatio_reduction_nonvacuous :
    ∀ r, 2 ≤ r → (fun _ : ℕ => (1 : ℝ)) r ≤ 1 :=
  stepRatio_le_one_of_antitone_base (R := fun _ => (1 : ℝ)) (r₀ := 2)
    (le_refl 1) (fun _ _ => le_refl 1)

end ArkLib.ProximityGap.StepRatioMonotone

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StepRatioMonotone.stepRatio_le_one_of_antitone_base
#print axioms ArkLib.ProximityGap.StepRatioMonotone.stepRatio_le_one_iff_energy
#print axioms ArkLib.ProximityGap.StepRatioMonotone.stepRatio_reduction_nonvacuous
