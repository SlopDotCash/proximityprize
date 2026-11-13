/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Bridge B02 [target E1] — Johnson-crossing <-> binding-depth bound (#444)

Purely real-algebraic unwinding of master gap identity E1 (CORRECTED 2026-06-16, off-by-one):
  deltaStar = 1 - rho - mstar/n
into the Johnson-window-crossing criterion.

⚠️ Was `1 - rho - (mstar - 1)/n` (off by one — see audit; `capacity − δ* = m*/n`, not `(m*−1)/n`).

Honest REDUCTION: E1 is consumed as a named hypothesis hE1; the biconditional is then
proved with ordered-field arithmetic only (no analysis). Side condition: 0 < n.
-/

namespace ArkLib.ProximityGap.BridgeB02

open Real

/-- Bridge B02 / E1 (CORRECTED). Given E1 `deltaStar = 1 - rho - mstar/n` and `0 < n`, the
threshold lies strictly above Johnson `1 - sqrt rho` iff `mstar < (sqrt rho - rho)*n`. -/
theorem deltaStar_gt_johnson_iff_mstar_lt
    (rho n mstar deltaStar : ℝ) (hn : 0 < n)
    (hE1 : deltaStar = 1 - rho - mstar / n) :
    (1 - Real.sqrt rho < deltaStar) ↔ (mstar < (Real.sqrt rho - rho) * n) := by
  rw [hE1]
  rw [show (1 - Real.sqrt rho < 1 - rho - mstar / n)
        ↔ (mstar / n < (Real.sqrt rho - rho)) by
        constructor <;> intro h <;> linarith]
  exact div_lt_iff₀ hn

#print axioms deltaStar_gt_johnson_iff_mstar_lt

end ArkLib.ProximityGap.BridgeB02
