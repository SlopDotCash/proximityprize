/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.LinearizedHomogeneous
import ArkLib.ToMathlib.LinearizedProductClosure

/-!
# The assembled inductive step of the q-linearized-support theorem

For a q-power-supported polynomial `P` over an extension `K` of the finite field `F` (`q = |F|`),
with `P.eval u ≠ 0`, the product

`∏_{c∈F} (P - C (P.eval (ι c · u)))`

— the exact form the subspace-polynomial recursion produces, with `P = s_{V'}` — is again
q-power-supported.  Combining 𝔽_q-homogeneity (`isQPowSupported_eval_smul`, which rewrites
`P.eval (ι c · u) = ι c · P.eval u`) with the product-form closure
(`isQPowSupported_prod_sub_C_line`, valid since `P.eval u ≠ 0`).

This is the inductive step of BKR06's linearized-support theorem fully assembled from the verified
bricks; the only remaining input for the full theorem is the *recursion identity*
`s_{V'⊕𝔽_q·u} = ∏_{c∈F}(s_{V'} - C(s_{V'}(ι c · u)))` (the subspace coset decomposition).
-/

open Polynomial BigOperators

namespace ArkLib.LinearizedKernel

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [Algebra F K]

/-- **Assembled inductive step.** If `P` is q-power-supported and `P.eval u ≠ 0`, then
`∏_{c∈F} (P - C (P.eval (ι c · u)))` is q-power-supported. -/
theorem isQPowSupported_prod_eval_smul {P : K[X]} (hP : IsQPowSupported (F := F) P)
    (u : K) (hu : P.eval u ≠ 0) :
    IsQPowSupported (F := F) (∏ c : F, (P - C (P.eval (algebraMap F K c * u)))) := by
  have hrw : (∏ c : F, (P - C (P.eval (algebraMap F K c * u))))
      = ∏ c : F, (P - C (P.eval u * algebraMap F K c)) := by
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [isQPowSupported_eval_smul hP c u, mul_comm]
  rw [hrw]
  exact isQPowSupported_prod_sub_C_line (P.eval u) hu hP

end ArkLib.LinearizedKernel

-- Axiom audit.
#print axioms ArkLib.LinearizedKernel.isQPowSupported_prod_eval_smul
