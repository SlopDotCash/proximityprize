/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BirthdayBound
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma512Paper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma514Paper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma516Paper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.EagerLazyDS

/-!
# #314 wave-5 — the CO25 §5.6 → §5.8 channel over the paper-faithful event

`BirthdayBound.lean`'s honest-domination and assembly theorems consume the M2 residual
interfaces (`Lemma5_12/14/16HonestResidual`) over the deviant in-tree `E` — interfaces that
are refuted or trivialized as stated (`Lemma58EagerFalse`, `Lemma514ForkFalse`,
`Lemma516TimePFalse`).  This module re-keys the channel on the repaired event
`DuplexSpongeFS.Paper.EPaper` (CO25 Eq. 27 with the B1/B2 repairs), where the M2 block is
**proven** (`lemma512Paper`, `lemma514Paper`, `lemma516Paper`):

- `probEvent_honestBad_le_probEvent_EPaper` — the honest-domination theorem with **no**
  residual hypotheses: the probability of any honest §5.6 bad event is at most the
  probability of `EPaper`.
- `Lemma5_8EagerPaperResidual` — the repaired R1f core: the CO25 Lemma 5.8 birthday bound
  for `EPaper` over the eager `D_𝔖` carrier.  Unlike the refuted
  `Lemma5_8EagerBirthdayFalseStatement`, this statement survives the K1 single-inverse-query
  countermodel: an inverse entry fires the repaired `E_pinv` arm only through a genuine
  capacity coincidence (its disjunct 5 anchors on the *query* capacity per CO25 Eq. 26),
  so `Pr[EPaper]` is small for low-query adversaries.
- `honestBad_birthday_of_paperResidual` — the assembly: the repaired 5.8 residual ALONE
  bounds the honest bad events by `lemma5_8Bound U T` (= `claim5_21Bound` at the Hyb₀/Hyb₁
  trace length).  The M2 legs are theorems, no longer hypotheses.

The proof plan for `Lemma5_8EagerPaperResidual` is the 3-step program recorded on the old
residual (carrier coupling, event decomposition, budget recombination), now against a
statement that is no longer false.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog
open DuplexSpongeFS.KeyLemmaFoundations

namespace DuplexSpongeFS.BirthdayBoundPaper

open DuplexSpongeFS.BirthdayBound DuplexSpongeFS.Paper

variable {StmtIn U : Type} [SpongeUnit U] [SpongeSize]

/-- **Honest §5.6 bad events are dominated by the paper event — no residual hypotheses**
(CO25 Lemmas 5.12/5.14/5.16, all proven over `EPaper`): in any game producing a trace and
an end state, the probability that some backtrack family witnesses
`E_inv ∨ E_fork ∨ E_time` is at most the probability of `EPaper`. -/
theorem probEvent_honestBad_le_probEvent_EPaper
    {β : Type} (game : ProbComp β)
    (tr : β → QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (st : β → CanonicalSpongeState U) :
    Pr[ fun z => ∃ S : Backtrack.S_BT (tr z) (st z),
        E_inv_honest (tr z) (st z) S ∨ E_fork_honest (tr z) (st z) S
          ∨ E_time_honest (tr z) (st z) S | game]
      ≤ Pr[ fun z => EPaper (tr z) | game] := by
  refine probEvent_mono'' fun z hz => ?_
  obtain ⟨S, hS⟩ := hz
  by_contra hE
  rcases hS with h | h | h
  · exact lemma512Paper (tr z) (st z) S hE h
  · exact lemma514Paper (tr z) (st z) S hE h
  · exact lemma516Paper (tr z) (st z) S hE h

section EagerInstantiation

variable (StmtIn U : Type) [SpongeUnit U] [SpongeSize] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]

/-- **The repaired R1f core — CO25 Lemma 5.8 over the eager `D_𝔖` carrier and the paper
event**: for any `T`-query adversary against the duplex-sponge challenge oracle answered
by the once-sampled `(h, p, p⁻¹)` carrier `D_DS`, the logged trace realizes `EPaper` with
probability at most `(7T² − 3T)/(2|Σ|^c)`.

This replaces the refuted `Lemma5_8EagerBirthdayFalseStatement` (see `Lemma58EagerFalse.lean`):
over `EPaper` the B1 self-firing channel is closed, so the K1 single-inverse-query
countermodel does not apply — an inverse entry contributes only genuine capacity
coincidences.  Proof plan (CO25 Lemma 5.8): (1) carrier coupling — eager permutation table
vs fresh uniform draws, mediated by the paper dedup; (2) decomposition of `EPaper` into
the capacity-collision/landing families counted by the `7T²` numerator
(`probEvent_collision_freshUniformLog_le_tight`, `probEvent_hit_freshUniformHit_le`);
(3) budget recombination (`BudgetCover`). -/
def Lemma5_8EagerPaperResidual : Prop :=
  ∀ {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ),
    IsTotalQueryBound P T →
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => EPaper z.2 |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ lemma5_8Bound U T

variable {StmtIn U}

/-- **R1 assembly over the paper event** — the repaired Lemma 5.8 residual ALONE implies
the birthday bound for the honest §5.6 bad events: the M2 legs (CO25 Lemmas
5.12/5.14/5.16) are theorems over `EPaper`, so the only remaining hypothesis is the
probability core.  At the Hyb₀/Hyb₁ trace length `T = tₕ + 1 + tₚ + L + tₚᵢ` the bound is
exactly `claim5_21Bound` (`lemma5_8Bound_eq_claim5_21Bound`). -/
theorem honestBad_birthday_of_paperResidual
    (h58 : Lemma5_8EagerPaperResidual StmtIn U)
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) (st₀ : CanonicalSpongeState U) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        ∃ S : Backtrack.S_BT z.2 st₀,
          E_inv_honest z.2 st₀ S ∨ E_fork_honest z.2 st₀ S ∨ E_time_honest z.2 st₀ S |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ lemma5_8Bound U T := by
  refine le_trans (ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one) ?_) (h58 P T hT)
  exact probEvent_honestBad_le_probEvent_EPaper _
    (fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => z.2) (fun _ => st₀)

/-- **Claim 5.21 specialization** — the repaired Lemma 5.8 paper residual bounds the honest
bad events by the exact `claim5_21Bound` consumed by the `Hyb₀ → Hyb₁` step, after
instantiating the total query budget at the CO25 trace length
`T = tₕ + 1 + tₚ + L + tₚᵢ`. -/
theorem honestBad_claim5_21Bound_of_paperResidual
    (h58 : Lemma5_8EagerPaperResidual StmtIn U)
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
      ≤ claim5_21Bound U tₕ tₚ tₚᵢ L := by
  simpa [BirthdayBound.lemma5_8Bound_eq_claim5_21Bound] using
    honestBad_birthday_of_paperResidual (StmtIn := StmtIn) (U := U) h58 P
      (tₕ + 1 + tₚ + L + tₚᵢ) hT st₀

/-- **The Lemma 5.8 residual reduces to its lazy-side form** (via the eager–lazy
duplex-sponge bridge `evalDist_DDS_eq_lazyDSImpl`): it suffices to bound the `EPaper`
probability of the **lazy memoizing game**, where every query is a deterministic cache hit
or a fresh uniform draw — the regime of the per-step counting bricks. -/
theorem lemma5_8EagerPaperResidual_of_lazy
    [DecidableEq StmtIn] [Finite StmtIn]
    [Nonempty (StmtIn → Vector U SpongeSize.C)]
    [Nonempty (Equiv.Perm (CanonicalSpongeState U))]
    [Fintype (StmtIn → Vector U SpongeSize.C)]
    [Fintype (Vector U SpongeSize.C)] [Nonempty (Vector U SpongeSize.C)]
    [SampleableType (Vector U SpongeSize.C)]
    [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]
    [Fintype (CanonicalSpongeState U)]
    (h : ∀ {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ),
      IsTotalQueryBound P T →
      (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => EPaper z.2 |
        (simulateQ DuplexSpongeFS.EagerLazyDS.lazyDSImpl
          ((simulateQ loggingOracle P).run)).run' (∅, ([] :
            List (CanonicalSpongeState U × CanonicalSpongeState U)))]).toReal
        ≤ lemma5_8Bound U T) :
    Lemma5_8EagerPaperResidual StmtIn U := by
  intro α P T hT
  rw [DuplexSpongeFS.EagerLazyDS.probEvent_DDS_eq_lazyDSImpl]
  exact h P T hT

end EagerInstantiation

end DuplexSpongeFS.BirthdayBoundPaper

#print axioms DuplexSpongeFS.BirthdayBoundPaper.probEvent_honestBad_le_probEvent_EPaper
#print axioms DuplexSpongeFS.BirthdayBoundPaper.honestBad_birthday_of_paperResidual
#print axioms DuplexSpongeFS.BirthdayBoundPaper.honestBad_claim5_21Bound_of_paperResidual

#print axioms DuplexSpongeFS.BirthdayBoundPaper.lemma5_8EagerPaperResidual_of_lazy
