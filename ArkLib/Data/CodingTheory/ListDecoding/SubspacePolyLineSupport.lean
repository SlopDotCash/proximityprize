/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyLinearized
import ArkLib.ToMathlib.LinearizedSupportStep

/-!
# The subspace polynomial of an 𝔽_q-line is q-power-supported

A verified instance of the BKR06 linearized-support property: combining
`BKR06.subspacePoly_line_eq` (the 1-D line subspace polynomial equals the linearized binomial
`X^q - C(a^{q-1})X`) with the q-power-support induction (`isQPowSupported_X` base case and
`isQPowSupported_kernel` closure), the subspace polynomial of the `𝔽_q`-line `{a·ι c}` has its
support on the `q`-powers — i.e. it is a genuine linearized polynomial `∑ aᵢ X^{q^i}`.

This realises the dimension-1 case of BKR06's linearized-support theorem end to end, on a real
`BKR06.subspacePoly`, from the verified kernel/recursion/support bricks.
-/

open Polynomial BigOperators

namespace ArkLib.LinearizedKernel

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra F K]

/-- **The subspace polynomial of an `𝔽_q`-line is q-power-supported.** For `a ≠ 0`, every exponent
in the support of `subspacePoly {a·ι c : c ∈ F}` is a power of `q = |F|`. -/
theorem isQPowSupported_subspacePoly_line (a : K) (ha : a ≠ 0) :
    IsQPowSupported (F := F)
      (BKR06.subspacePoly (Finset.image (fun c : F => a * algebraMap F K c) Finset.univ)) := by
  rw [BKR06.subspacePoly_line_eq a ha]
  exact isQPowSupported_kernel (a ^ (Fintype.card F - 1)) isQPowSupported_X

end ArkLib.LinearizedKernel

-- Axiom audit.
#print axioms ArkLib.LinearizedKernel.isQPowSupported_subspacePoly_line
