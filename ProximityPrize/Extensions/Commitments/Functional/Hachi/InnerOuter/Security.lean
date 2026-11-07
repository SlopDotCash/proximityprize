/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Security

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ProximityPrize.Extensions.Commitments.Functional.Hachi.InnerOuter.Correctness
import ProximityPrize.Extensions.Commitments.Functional.Hachi.InnerOuter.Arithmetic

/-!
# Weak-Binding Security of the Inner-Outer Ajtai Commitment

The Greyhound [NS24] / Hachi [NOZ26] weak-binding reduction over the cyclotomic ring `Rq Φ`
(`R = ZMod q`).
A weak opening carries, per block `i`, a message `sᵢ`, an inner-decomposition `t̂ᵢ`, and a
challenge `cᵢ`; the verifier `verify_weak` bounds each challenge (nonzero, `ℓ₁ ≤ κ`), bounds
each scaled message (`‖cᵢ·sᵢ‖₂² ≤ β²`), checks the inner gadget relation, and bounds and
checks the outer commitment.

The *definitions* (opening, verifier, experiment, advantage, reductions) are polymorphic in
the cyclotomic modulus `Φ`. The *security statements*, however, are pinned to the power-of-two
cyclotomic modulus `Φ = powTwoCyclotomic α` (`φ = X^{2^α} + 1`), abbreviated `𝓜(q, α)`,
because they invoke the two lemmas that only hold there: accepted challenges are
genuinely invertible via the Lyubashevsky–Seiler [LS18] result (`isUnit_of_l1Norm_le`), and
scaled messages stay short via the Micciancio/Young product bound
(`scalarVecMul_mul_l2NormSq_le`). The reductions therefore carry the remaining [LS18]
hypotheses: `q ≡ 5 (mod 8)` and `κ² < q`.

`outputToModuleSIS_valid` is the cryptographic heart: a winning pair of distinct weak
openings yields a valid inner *or* outer Module-SIS witness. `advantage_le_moduleSIS` wraps
it probabilistically.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp CommitmentScheme CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
  ArkLib.Lattices.Ajtai
open scoped ENNReal BigOperators

namespace ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ] (α : ℕ)
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}

-- `𝓜(q, α)` (the inner-outer commitment modulus `hachiModulus q α`) is the scoped notation from
-- `InnerOuter.Arithmetic`, active here since this namespace is nested in `…InnerOuter`.

/-! ## Generic helpers -/

/-- Boolean monotonicity of `pure` outcome probability into a disjunction. -/
theorem probOutput_pure_bool_le_or (win inner outer : Bool)
    (h : win = true → inner = true ∨ outer = true) :
    𝒟[(pure win : ProbComp Bool)] {true} ≤
      𝒟[(pure inner : ProbComp Bool)] {true} +
        𝒟[(pure outer : ProbComp Bool)] {true} :=
  evalDist_pure_apply_le_add_of_imp win inner outer h

/-- The zero fallback witness, used on the branch where the other matrix yields a witness. -/
def zeroSolution (cols : Nat) : ModuleSIS.Solution Φ cols := fun _ => 0

variable
  [SampleableType (Simple.PublicParams Φ innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))]

variable
  [SampleableType (Simple.PublicParams 𝓜(q, α) innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams 𝓜(q, α) outerRows (blocks * (innerRows * innerDigits)))]

end ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding
