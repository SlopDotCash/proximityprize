/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio

/-!
# Guarded `simulateQ` congruence — the H23-9 relational-lift engine (issue #316)

`simulateQ_congr_of_isQueryBoundP_zero`: two query implementations that agree on every
query index a computation can actually reach (formally: the computation makes **zero**
queries at indices where they might differ) induce the same simulation.

This is the engine of the Claim 5.23 trace lift (H23-9): the `Hyb₂`/`Hyb₃` outer
implementations differ only at decode-failure `gᵢ` keys, which the simulator's codec-image
guard (H23-2) makes unreachable — `IsQueryBoundP … 0` at the failure indices. Combined
with the per-query step coupling (`stepCoupling`, H23-8) supplying the agreement on
success keys, the full game runs coincide pointwise in the sampled table.

The proof is the by-now-standard free-monad induction (cf. the zero-budget logging brick
`queryLog_entries_not_p_of_isQueryBoundP_zero` and the bind splitter
`mem_support_loggingOracle_bind_split`), at an arbitrary lawful target monad.
-/

open OracleComp OracleSpec

namespace DuplexSpongeFS.Hyb23Bricks

universe u v

/-- **Guarded congruence for `simulateQ`**: if `oa` makes zero `p`-queries and the two
implementations agree off `p`, the simulations agree. -/
theorem simulateQ_congr_of_isQueryBoundP_zero
    {ι : Type} {spec : OracleSpec ι} {m : Type → Type v} [Monad m] [LawfulMonad m]
    {α : Type} {p : ι → Prop} [DecidablePred p]
    (hA hB : QueryImpl spec m)
    {oa : OracleComp spec α} (hbound : IsQueryBoundP oa p 0)
    (hagree : ∀ t : spec.Domain, ¬ p t → hA t = hB t) :
    simulateQ hA oa = simulateQ hB oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      have hpt : ¬ p t := hbound.1.resolve_right (by omega)
      rw [simulateQ_query_bind, simulateQ_query_bind]
      have ht' : hA (OracleSpec.query t).input = hB (OracleSpec.query t).input :=
        hagree _ hpt
      rw [ht']
      exact bind_congr fun u => ih _ (by simpa using hbound.2 _)

end DuplexSpongeFS.Hyb23Bricks

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.Hyb23Bricks.simulateQ_congr_of_isQueryBoundP_zero
