/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.LinearizedKernel
import ArkLib.ToMathlib.LinearizedSupportStep

/-!
# q-power support is closed under the line-product

Combining the recursion engine `prod_sub_C_smul_eq` (`∏_{c∈F}(P - C(a·ι c)) = P^q - C(a^{q-1})P`)
with the support closure `isQPowSupported_kernel`: if `P` is q-power-supported then so is
`∏_{c∈F}(P - C(a·ι c))` for any `a ≠ 0`.

This is exactly the inductive step of the q-linearized-support theorem in **product form**: the
subspace-polynomial recursion `s_{V'⊕𝔽_q·u} = ∏_{c∈F}(s_{V'} - C(c·s_{V'}(u)))` (with `a = s_{V'}(u)`)
preserves q-power support, so by induction every subspace polynomial is q-power-supported.
-/

open Polynomial BigOperators

namespace ArkLib.LinearizedKernel

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [Algebra F K]

/-- **q-power support is closed under the 𝔽_q-line product.** If `P` is q-power-supported then so is
`∏_{c∈F}(P - C(a·ι c))` (`= P^q - C(a^{q-1})P`) for `a ≠ 0`. The product form of the linearized
recursion's inductive step. -/
theorem isQPowSupported_prod_sub_C_line {P : K[X]} (a : K) (ha : a ≠ 0)
    (hP : IsQPowSupported (F := F) P) :
    IsQPowSupported (F := F) (∏ c : F, (P - C (a * algebraMap F K c))) := by
  rw [prod_sub_C_smul_eq P a ha]
  exact isQPowSupported_kernel (a ^ (Fintype.card F - 1)) hP

end ArkLib.LinearizedKernel

-- Axiom audit.
#print axioms ArkLib.LinearizedKernel.isQPowSupported_prod_sub_C_line
