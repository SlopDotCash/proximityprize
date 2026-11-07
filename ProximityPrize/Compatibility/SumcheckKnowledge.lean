/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# The actual per-round knowledge obligation for canonical sumcheck

The canonical verifier checks the prover's message polynomial. Its degree/cardinality knowledge
bound is a substantive mathematical obligation, independent of the completed lens/composition
constructions. This predicate names exactly that per-round bound for a fixed protocol instance;
it has no instance and supplies no proof automatically.
-/

open OracleComp OracleSpec
open scoped NNReal

namespace Sumcheck.Spec

/-- The knowledge bound of each actual canonical message-checking sumcheck round. -/
def RoundKnowledge (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R]
    [Fintype R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R) (n : ℕ)
    {ι : Type} (oSpec : OracleSpec ι) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) : Prop :=
  ∀ i : Fin n, (SingleRound.oracleVerifier R n deg D oSpec i).rbrKnowledgeSoundness init impl
    (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
    (fun _ => (deg : ℝ≥0) / Fintype.card R)

end Sumcheck.Spec
