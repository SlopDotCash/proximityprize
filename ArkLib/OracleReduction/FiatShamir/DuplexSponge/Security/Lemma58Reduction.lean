/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BirthdayBoundPaper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma58Correspondence
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma58Extraction

/-!
# The eager side of CO25 Lemma 5.8: the repaired residual is a theorem (issue #316)

The lazy-side apexes (`ePaperReduction_holds`, `probEvent_EPaper_toReal_le_lemma5_8Bound`)
live in `Lemma58Correspondence.lean`. This module transfers them across the eager–lazy
bridge and discharges the eager surface:

- `lemma5_8EagerPaperResidual_holds` — the repaired R1f core
  (`BirthdayBoundPaper.Lemma5_8EagerPaperResidual`) is a theorem: one application of
  `lemma5_8EagerPaperResidual_of_lazy` to the lazy bound.
- `honestBad_birthday_unconditional` — the §5.6 → §5.8 channel with no residual
  hypotheses.
- `honestBad_claim5_21Bound_unconditional` — Claim 5.21 at the CO25 trace length
  `T = tₕ + 1 + tₚ + L + tₚᵢ`, the exact leaf the `Hyb₀ → Hyb₁` step consumes.
-/

open OracleComp OracleSpec

/-! ## The eager side: the repaired residual is a theorem, the channel is unconditional -/

namespace DuplexSpongeFS.BirthdayBoundPaper

open DuplexSpongeFS.BirthdayBound DuplexSpongeFS.Paper
open DuplexSpongeFS.KeyLemmaFoundations
open OracleSpec.QueryLog

variable {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
  [DecidableEq StmtIn] [Fintype StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]

/-- **The repaired Lemma 5.8 eager residual holds**: the lazy-side bound
`probEvent_EPaper_toReal_le_lemma5_8Bound` transfers across the eager–lazy bridge. -/
theorem lemma5_8EagerPaperResidual_holds : Lemma5_8EagerPaperResidual StmtIn U :=
  lemma5_8EagerPaperResidual_of_lazy fun P T hT =>
    DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound P T hT

/-- **The §5.6 → §5.8 channel, unconditional**: the honest bad events of the eager
`D_𝔖`-carrier game obey the birthday bound — no residual hypotheses. -/
theorem honestBad_birthday_unconditional
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) (st₀ : CanonicalSpongeState U) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        ∃ S : Backtrack.S_BT z.2 st₀,
          E_inv_honest z.2 st₀ S ∨ E_fork_honest z.2 st₀ S ∨ E_time_honest z.2 st₀ S |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ lemma5_8Bound U T :=
  honestBad_birthday_of_paperResidual lemma5_8EagerPaperResidual_holds P T hT st₀

/-- **Claim 5.21, unconditional**: at the CO25 trace length `T = tₕ + 1 + tₚ + L + tₚᵢ`,
the honest bad events are bounded by the exact `claim5_21Bound` consumed by the
`Hyb₀ → Hyb₁` step — no residual hypotheses. -/
theorem honestBad_claim5_21Bound_unconditional
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α)
    (tₕ tₚ tₚᵢ L : ℕ)
    (hT : IsTotalQueryBound P (tₕ + 1 + tₚ + L + tₚᵢ))
    (st₀ : CanonicalSpongeState U) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        ∃ S : Backtrack.S_BT z.2 st₀,
          E_inv_honest z.2 st₀ S ∨ E_fork_honest z.2 st₀ S ∨ E_time_honest z.2 st₀ S |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ claim5_21Bound U tₕ tₚ tₚᵢ L :=
  honestBad_claim5_21Bound_of_paperResidual lemma5_8EagerPaperResidual_holds
    P tₕ tₚ tₚᵢ L hT st₀

end DuplexSpongeFS.BirthdayBoundPaper

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.BirthdayBoundPaper.lemma5_8EagerPaperResidual_holds
#print axioms DuplexSpongeFS.BirthdayBoundPaper.honestBad_birthday_unconditional
#print axioms DuplexSpongeFS.BirthdayBoundPaper.honestBad_claim5_21Bound_unconditional
