/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The Gaussian-tail energy decay law `A_r ≤ Wick·exp(−r²/2n)` ⟹ the prize (#444)

Machine finding (`probe_er_wick_decay.py`, conjecture #1 of the 30-conjecture set
`docs/kb/deltastar-444-30-conjectures-ErWick-decay-2026-06-17.md`): the DC-subtracted additive energy
`A_r = E_r(μ_n;F_p) − n^{2r}/p` follows a **Gaussian-tail decay law**
  `A_r / Wick ≈ exp(−r²/2n)`,   `Wick = (2r−1)‼·n^r`   (fitted constant `c → 1/2`, n=16 and n=32).

This file lands the **implication**: the Gaussian-tail decay law `A_r ≤ Wick·exp(−r²/2n)` IMPLIES the prize
bound `A_r ≤ Wick` — because the Gaussian-tail factor `exp(−r²/2n) ≤ 1` always. So if the (conjectural,
machine-favorable) decay law holds at the prize prime to depth `r ≈ log p`, the prize follows immediately.

This makes precise that the decay law is a STRONGER, structured target whose proof would close the
char-`p` Wick bound — and that it predicts the **knife-edge**: at prize scale (`r ≈ log p ≈ 89`,
`n = 2^30`) the exponent `r²/2n ≈ 3.7×10⁻⁶ → 0`, so `A_r/Wick → 1` (the bound holds with vanishing margin).
Real-analysis facts, no `sorry`; the decay law itself is the named open input.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.ErWickGaussianTailDecay

open Real

/-- **The Gaussian-tail factor is `≤ 1`.** `exp(−r²/2n) ≤ 1` for all `r, n` (the exponent is `≤ 0`). This is
the entire reason the decay law implies the prize. -/
theorem gaussianTail_le_one (r n : ℝ) (hn : 0 < n) :
    Real.exp (-(r^2) / (2 * n)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [sq_nonneg r]
  · positivity

/-- **The decay law ⟹ the prize (per `r`).** If the DC-subtracted energy obeys the Gaussian-tail decay
`A_r ≤ Wick·exp(−r²/2n)`, then `A_r ≤ Wick` (the char-`p` Wick bound = the prize at depth `r`), since the
Gaussian-tail factor is `≤ 1`. So the (machine-favorable) decay law is a sufficient structured input. -/
theorem prize_of_gaussianTail_decay {Ar wick r n : ℝ} (hn : 0 < n) (hwick : 0 ≤ wick)
    (hdecay : Ar ≤ wick * Real.exp (-(r^2) / (2 * n))) :
    Ar ≤ wick := by
  refine le_trans hdecay ?_
  calc wick * Real.exp (-(r^2) / (2 * n))
      ≤ wick * 1 := by
        apply mul_le_mul_of_nonneg_left (gaussianTail_le_one r n hn) hwick
    _ = wick := mul_one wick

/-- **The all-depth form.** If the Gaussian-tail decay holds at every depth `r` (the conjectural law at a
good prime), then the char-`p` Wick bound `A_r ≤ Wick` holds at every depth — i.e. the prize. The decay law
is the single named open input; this lemma is the (trivial, but crystallizing) bridge `decay ⟹ prize`. -/
theorem prize_of_gaussianTail_decay_all {A W : ℕ → ℝ} {n : ℝ} (hn : 0 < n)
    (hW : ∀ r, 0 ≤ W r)
    (hdecay : ∀ r, A r ≤ W r * Real.exp (-((r : ℝ)^2) / (2 * n))) :
    ∀ r, A r ≤ W r :=
  fun r => prize_of_gaussianTail_decay hn (hW r) (hdecay r)

/-- **The knife-edge: at prize scale the Gaussian-tail factor → 1.** As `r²/n → 0` (prize scale:
`r ≈ log p`, `n = 2^30`, `r²/n ≈ 7×10⁻⁶`), the factor `exp(−r²/2n) → 1`, so the decay-law bound `A_r ≤
Wick·exp(−r²/2n)` approaches the tight `A_r ≤ Wick` — the bound holds with VANISHING margin (the knife-edge
the campaign measured). Formally: the factor is `≥ 1 − r²/2n` (so within `r²/2n` of 1). -/
theorem gaussianTail_knife_edge (r n : ℝ) (hn : 0 < n) :
    1 - r^2 / (2 * n) ≤ Real.exp (-(r^2) / (2 * n)) := by
  have h := Real.add_one_le_exp (-(r^2) / (2 * n))
  have hid : -(r^2) / (2 * n) = -(r^2 / (2 * n)) := by rw [neg_div]
  linarith [hid ▸ h]

end ArkLib.ProximityGap.ErWickGaussianTailDecay

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ErWickGaussianTailDecay.gaussianTail_le_one
#print axioms ArkLib.ProximityGap.ErWickGaussianTailDecay.prize_of_gaussianTail_decay
#print axioms ArkLib.ProximityGap.ErWickGaussianTailDecay.prize_of_gaussianTail_decay_all
#print axioms ArkLib.ProximityGap.ErWickGaussianTailDecay.gaussianTail_knife_edge
