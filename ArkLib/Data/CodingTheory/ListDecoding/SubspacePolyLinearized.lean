/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly
import ArkLib.ToMathlib.LinearizedKernel

/-!
# Subspace polynomial of a 1-dimensional line is the linearized binomial

`BKR06.subspacePoly L = ∏ ℓ ∈ L, (X - C ℓ)` is the BKR06 subspace polynomial.  For the
`𝔽_q`-line `L = a · 𝔽_q = {a · c : c ∈ F}` (`a ≠ 0`) inside an extension `K`, this file proves
the explicit **linearized binomial** form

`subspacePoly (a · 𝔽_q) = X^q - C(a^{q-1}) · X`

directly from the linearized kernel `ArkLib.LinearizedKernel.prod_X_sub_C_smul_eq`.  This is the
base case (dimension 1) of the q-linearized-support induction for subspace polynomials — the
support theorem BKR06's tight list-size count consumes (`BKR06Pigeonhole` `hexp` residual): its
support `{1, q} = {q^0, q^1}` already sits on the `q`-powers.
-/

open Polynomial BigOperators

namespace BKR06

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra F K]

/-- **1-dimensional line subspace polynomial = linearized binomial.** For `a ≠ 0`, the subspace
polynomial of the `𝔽_q`-line `{a · ι c : c ∈ F}` is `X^q - C(a^{q-1}) · X`. -/
theorem subspacePoly_line_eq (a : K) (ha : a ≠ 0) :
    subspacePoly (Finset.image (fun c : F => a * algebraMap F K c) Finset.univ)
      = X ^ Fintype.card F - C (a ^ (Fintype.card F - 1)) * X := by
  classical
  have hinj : ∀ x ∈ (Finset.univ : Finset F), ∀ y ∈ (Finset.univ : Finset F),
      a * algebraMap F K x = a * algebraMap F K y → x = y :=
    fun x _ y _ hxy => (algebraMap F K).injective (mul_left_cancel₀ ha hxy)
  rw [subspacePoly, Finset.prod_image hinj]
  exact ArkLib.LinearizedKernel.prod_X_sub_C_smul_eq a ha

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePoly_line_eq
