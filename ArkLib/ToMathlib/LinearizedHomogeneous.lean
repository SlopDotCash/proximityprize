/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.LinearizedSupportStep

/-!
# q-power support implies 𝔽_q-homogeneity

A q-power-supported polynomial `P = ∑ aᵢ X^{q^i}` over an extension `K` of the finite field `F`
(`q = |F|`) is **𝔽_q-homogeneous**: `P(c·u) = c·P(u)` for every `c ∈ 𝔽_q` and `u ∈ K`.

This is the second half of the linearized-polynomial property (the first being additivity).  The
key arithmetic is Fermat's little theorem in `F`: `c^{q^i} = c` (`FiniteField.pow_card_pow`), so
`(ι c)^{q^i} = ι c` and every monomial `aᵢ (ι c · u)^{q^i} = ι c · aᵢ u^{q^i}` scales by `ι c`.

Together with q-power support this gives the full 𝔽_q-linearity of subspace polynomials, the
missing input that turns the subspace recursion `∏_{c∈F}(s_{V'} - C(s_{V'}(c·u)))` into the
linearized binomial `s_{V'}^q - C(s_{V'}(u)^{q-1}) s_{V'}` (because `s_{V'}(c·u) = c·s_{V'}(u)`).
-/

open Polynomial BigOperators

namespace ArkLib.LinearizedKernel

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [Algebra F K]

/-- **q-power support ⟹ 𝔽_q-homogeneity.** If `P` is q-power-supported then
`P.eval (ι c · u) = ι c · P.eval u` for `c : F`, `u : K` (`ι = algebraMap F K`). -/
theorem isQPowSupported_eval_smul {P : K[X]} (hP : IsQPowSupported (F := F) P) (c : F) (u : K) :
    P.eval (algebraMap F K c * u) = algebraMap F K c * P.eval u := by
  rw [eval_eq_sum, eval_eq_sum, Polynomial.sum, Polynomial.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  obtain ⟨i, rfl⟩ := hP n hn
  rw [mul_pow, ← map_pow, FiniteField.pow_card_pow]
  ring

end ArkLib.LinearizedKernel

-- Axiom audit.
#print axioms ArkLib.LinearizedKernel.isQPowSupported_eval_smul
