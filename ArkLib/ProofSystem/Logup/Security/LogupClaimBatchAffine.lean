/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge

/-!
# The LogUp outer claim is affine in the batching scalars (issue #13, batching-binding entry)

Entry brick of the `hOuter@midLanguage` blueprint (issue #13): the outer sumcheck claim
`logupOuterSumcheckClaim` decomposes as `A + ∑_k batch_k · C_k(z)` — the helper mass `A`
(batch- and z-independent) plus batch-weighted coefficients. Consequences wired downstream:
the claim vanishes identically in the batching scalars iff `A = 0` and every `C_k(z) = 0`
(evaluate at `batch = 0` and at the standard basis vectors), which is the start of the
batching-binding chain (`claim ≡ 0` in `(z, batch)` ⟹ helper-consistency identities ⟹
grand-sum identity at `x`). Axiom-clean.
-/

open scoped BigOperators

namespace Logup

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n M : ℕ} {params : ProtocolParams M}

omit [Fintype F] [DecidableEq F] in
/-- **Affine-in-batch decomposition of the LogUp outer sumcheck claim.** The claim splits as the
helper mass (batch- and z-independent) plus the batch-weighted Lagrange-mixed domain-identity
terms: `claim = A + ∑_k batch_k · C_k(z)`. The claim is an affine function of the batching
scalars — the structural input to the batching-binding step of `hOuter@midLanguage`. -/
theorem logupOuterSumcheckClaim_affine_in_batch
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    logupOuterSumcheckClaim F n M params stmt oStmt
      = (∑ k : Fin params.numGroups, ∑ u : Hypercube n,
          evalOnHypercube (oStmt .helpers k) u)
        + ∑ k : Fin params.numGroups, stmt.batchingScalars k *
            (∑ u : Hypercube n, lagrangeKernel F u stmt.zChallenge *
              domainIdentityTerm (canonicalGroups params) (fun i => oStmt (.input i))
                (oStmt .multiplicity) (oStmt .helpers) stmt.xChallenge k u) := by
  unfold logupOuterSumcheckClaim qOnHypercube
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  ring

end Logup

#print axioms Logup.logupOuterSumcheckClaim_affine_in_batch
