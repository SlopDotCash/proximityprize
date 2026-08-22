/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G131: additive-lift saddle no-go

G102F proves the additive-lift Capstone-A envelope for the terminal small-difference count
`x = smallDiffPairs(C,W)`:

`x^2 <= n*x + 4*rho*W*n^2`.

This file records the exact obstruction to using that envelope as the arc-saddle certificate.
To certify a target `x <= T` from the envelope alone, the quadratic inequality must exclude
the witness `T+1`. Equivalently, `T+1` must fail the same envelope. At the production scale
`n = 2^30`, `p = 2^160`, and the valid arc window `K = 2^13`, `W = p/K = 2^147`, even the
impossibly strong collision value `rho = 1` leaves `T+1` admissible for the uniform-main target
`T = 2*n^2/K = 2^48`.

Thus the additive-lift crossing of `sqrt(p)` is real, but Capstone A by itself is far too weak
at the saddle. Closing the terminal object needs extra signed/modular cancellation beyond an
additive-collision bound, not merely `rho << n`.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.G131AdditiveLiftSaddleNoGo

/-- If the quadratic Capstone-A envelope still permits `T+1`, then that envelope cannot certify
`x <= T`. This is the exact one-line no-go test for any proposed parameter specialization. -/
theorem capstoneA_witness_blocks_certificate {n rho W T : ℕ}
    (hwit : (T + 1) ^ 2 ≤ n * (T + 1) + 4 * rho * W * n ^ 2) :
    ¬ (∀ x : ℕ, x ^ 2 ≤ n * x + 4 * rho * W * n ^ 2 → x ≤ T) := by
  intro hcert
  have hbad : T + 1 ≤ T := hcert (T + 1) hwit
  omega

/-- The additive-lift side condition is valid at the displayed production arc window:
`4W < p` for `W = 2^147`, `p = 2^160`. -/
theorem production_K8192_window : 4 * (2 ^ 147 : ℕ) < 2 ^ 160 := by
  norm_num

/-- The corresponding uniform-main target is `T = 2*n^2/K = 2^48`. -/
theorem production_K8192_uniform_target :
    2 * (2 ^ 30 : ℕ) ^ 2 / (2 ^ 13) = 2 ^ 48 := by
  norm_num

/-- Even with `rho = 1`, the witness one above the uniform-main target satisfies the
Capstone-A envelope at the production arc window. -/
theorem production_K8192_even_rho_one_witness :
    ((2 ^ 48 : ℕ) + 1) ^ 2
      ≤ (2 ^ 30 : ℕ) * ((2 ^ 48 : ℕ) + 1)
        + 4 * 1 * (2 ^ 147 : ℕ) * (2 ^ 30 : ℕ) ^ 2 := by
  norm_num

/-- **Production no-go.** At `n = 2^30`, `p = 2^160`, `K = 2^13`, `W = p/K`, the
G102F Capstone-A envelope cannot certify the terminal uniform-main target, even under the
best possible additive-collision value `rho = 1`. -/
theorem production_K8192_even_rho_one_not_certify_uniform :
    ¬ (∀ x : ℕ,
      x ^ 2 ≤ (2 ^ 30 : ℕ) * x + 4 * 1 * (2 ^ 147 : ℕ) * (2 ^ 30 : ℕ) ^ 2 →
      x ≤ 2 ^ 48) :=
  capstoneA_witness_blocks_certificate production_K8192_even_rho_one_witness

/-! ## Axiom audit -/
#print axioms capstoneA_witness_blocks_certificate
#print axioms production_K8192_window
#print axioms production_K8192_uniform_target
#print axioms production_K8192_even_rho_one_witness
#print axioms production_K8192_even_rho_one_not_certify_uniform

end ArkLib.ProximityGap.Frontier.G131AdditiveLiftSaddleNoGo
