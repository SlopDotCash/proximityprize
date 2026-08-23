/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb34LogShapeFalse
import ArkLib.OracleReduction.FiatShamir.HVZKPerStateClose

/-!
# R3 discharged: every `Hyb₄` output carries a challenge-oracle entry (issue #316)

`hyb4ChallengeEntryResidual_holds` proves `Hyb4ChallengeEntryResidual`: whenever `pSpec`
has a challenge round, every `some`-output of the eager-rand basic Fiat-Shamir game has a
verifier log with at least one `fsChallengeOracle` entry.

The proof is the per-round log-suffix support induction forecast in the residual's
docstring, built from:

* `mem_support_loggingOracle_bind_split` — the generic logged-run bind splitter: a
  reachable log of `ca >>= cb` splits as `la ++ lb` with each half reachable for its
  stage (the existential dual of the in-tree zero-budget brick);
* `mem_support_loggingOracle_query_right_bind` — a logged right-summand query leaves a
  right entry in every reachable log;
* `deriveTranscriptSRAux_logged_right_entry` — the `Fin.induction` support induction:
  once a challenge round lies strictly below the cursor, every reachable log of the
  transcript derivation contains a right entry;
* the `Verifier.fiatShamir` unfolding: the verifier's logged run is the derivation's log
  followed by the lifted `V.verify` log, so the right entry persists by prefix.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb34LogShapeFalse

/-! ## Generic logged-run bricks -/

section LoggedBricks

/-- **Logged-run bind splitter** (existential dual of
`queryLog_entries_not_p_of_isQueryBoundP_zero`): every reachable `(value, log)` of a
logged bind factors through an intermediate value, with the log splitting as the two
stages' logs. -/
theorem mem_support_loggingOracle_bind_split
    {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {ca : OracleComp spec α} {cb : α → OracleComp spec β}
    {y : β} {log : QueryLog spec}
    (hmem : (y, log) ∈ support ((simulateQ loggingOracle (ca >>= cb)).run)) :
    ∃ a la lb, (a, la) ∈ support ((simulateQ loggingOracle ca).run) ∧
      (y, lb) ∈ support ((simulateQ loggingOracle (cb a)).run) ∧
      log = la ++ lb := by
  induction ca using OracleComp.inductionOn generalizing y log with
  | pure x =>
      rw [pure_bind] at hmem
      exact ⟨x, [], log, by simp [simulateQ_pure], hmem, rfl⟩
  | query_bind t mx ih =>
      rw [bind_assoc, run_simulateQ_loggingOracle_query_bind] at hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, hu, hmem⟩ := hmem
      rw [support_map] at hmem
      obtain ⟨⟨y', log'⟩, hy, heq⟩ := hmem
      obtain ⟨hx, hlog⟩ := Prod.mk.injEq .. ▸ heq
      subst hx
      subst hlog
      obtain ⟨a, la, lb, hca, hcb, hsplit⟩ := ih u hy
      refine ⟨a, ⟨t, u⟩ :: la, lb, ?_, hcb, by simp [hsplit]⟩
      rw [run_simulateQ_loggingOracle_query_bind, mem_support_bind_iff]
      refine ⟨u, hu, ?_⟩
      rw [support_map]
      exact ⟨(a, la), hca, rfl⟩

/-- A logged right-summand query leaves a right entry in every reachable log. -/
theorem mem_support_loggingOracle_query_right_bind
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {β : Type}
    {q : spec₂.Domain}
    {cb : spec₂.Range q → OracleComp (spec₁ + spec₂) β}
    {y : β} {log : QueryLog (spec₁ + spec₂)}
    (hmem : (y, log) ∈ support ((simulateQ loggingOracle
      ((query (spec := spec₂) q :
        OracleComp (spec₁ + spec₂) (spec₂.Range q)) >>= cb)).run)) :
    ∃ e ∈ log, e.1.isRight = true := by
  replace hmem : (y, log) ∈ support ((simulateQ loggingOracle
      ((liftM (OracleSpec.query (Sum.inr q)) :
        OracleComp (spec₁ + spec₂) ((spec₁ + spec₂).Range (Sum.inr q))) >>= cb)).run) :=
    hmem
  rw [run_simulateQ_loggingOracle_query_bind, mem_support_bind_iff] at hmem
  obtain ⟨u, -, hmem⟩ := hmem
  rw [support_map] at hmem
  obtain ⟨⟨y', log'⟩, -, heq⟩ := hmem
  obtain ⟨-, hlog⟩ := Prod.mk.injEq .. ▸ heq
  subst hlog
  exact ⟨⟨Sum.inr q, u⟩, List.mem_cons_self, by simp⟩

/-- A log with a right entry has a nonempty right projection. -/
lemma projectRightQueryLog_ne_nil_of_exists_isRight {ι₁ ι₂ : Type}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {log : QueryLog (spec₁ + spec₂)}
    (h : ∃ e ∈ log, e.1.isRight = true) :
    projectRightQueryLog log ≠ [] := by
  rcases h with ⟨⟨ql | qr, r⟩, he, hright⟩
  · simp at hright
  · intro hnil
    have hmem : (⟨qr, r⟩ : (t : spec₂.Domain) × spec₂.Range t)
        ∈ projectRightQueryLog log := by
      unfold projectRightQueryLog
      exact List.mem_filterMap.mpr ⟨⟨.inr qr, r⟩, he, rfl⟩
    rw [hnil] at hmem
    simp at hmem

end LoggedBricks

/-! ## The transcript-derivation support induction -/

section DeriveInduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- **Per-round log-suffix support induction**: once some challenge round lies strictly
below the cursor `j`, every reachable log of the partial transcript derivation contains a
right (challenge-oracle) entry. -/
theorem deriveTranscriptSRAux_logged_right_entry
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k)
    (j : Fin (k + 1)) :
    (∃ i₀ : pSpec.ChallengeIdx, (i₀.1 : ℕ) < (j : ℕ)) →
    ∀ z ∈ support ((simulateQ loggingOracle
      (MessagesUpTo.deriveTranscriptSRAux (oSpec := oSpec) stmt k messages j)).run),
      ∃ e ∈ z.2, e.1.isRight = true := by
  induction j using Fin.induction with
  | zero =>
      rintro ⟨i₀, hi₀⟩
      exact absurd hi₀ (Nat.not_lt_zero _)
  | succ i ih =>
      rintro ⟨i₀, hi₀⟩ ⟨y, log⟩ hz
      simp only [MessagesUpTo.deriveTranscriptSRAux] at hz
      rw [Fin.induction_succ] at hz
      obtain ⟨prev, la, lb, hla, hlb, hsplit⟩ :=
        mem_support_loggingOracle_bind_split hz
      subst hsplit
      revert hlb
      split
      · -- challenge round: the derivation itself queries the challenge oracle
        intro hlb
        obtain ⟨e, he, hright⟩ :=
          mem_support_loggingOracle_query_right_bind hlb
        exact ⟨e, List.mem_append_right _ he, hright⟩
      · -- message round: the witnessing challenge round lies strictly below `i`
        next hDir =>
        intro hlb
        have hlt : (i₀.1 : ℕ) < (i : ℕ) := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi₀ with hlt | heq
          · exact hlt
          · exfalso
            have hV : pSpec.dir (i.castLE (by omega)) = .V_to_P := by
              have h2 := i₀.2
              rwa [show i₀.1 = (i.castLE (by omega) : Fin n) from Fin.ext heq] at h2
            rw [hV] at hDir
            simp at hDir
        have hpure : lb = [] := by
          revert hlb
          simp only [simulateQ_pure]
          intro hlb
          simp only [WriterT.run, support_pure, Set.mem_singleton_iff] at hlb
          exact congrArg Prod.snd hlb
        subst hpure
        obtain ⟨e, he, hright⟩ := ih ⟨i₀, hlt⟩ (prev, la) hla
        exact ⟨e, by simpa using he, hright⟩

/-- Wrapper at the full-derivation level: with a challenge round present, every reachable
log of `deriveTranscriptFS` contains a right entry. -/
theorem deriveTranscriptFS_logged_right_entry
    (hne : Nonempty pSpec.ChallengeIdx)
    (stmt : StmtIn) (messages : pSpec.Messages)
    {z : pSpec.FullTranscript × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)}
    (hz : z ∈ support ((simulateQ loggingOracle
      (Messages.deriveTranscriptFS (oSpec := oSpec) stmt messages)).run)) :
    ∃ e ∈ z.2, e.1.isRight = true := by
  obtain ⟨i₀⟩ := hne
  exact deriveTranscriptSRAux_logged_right_entry stmt (Fin.last n) messages
    (Fin.last (Fin.last n : Fin (n + 1)).val) ⟨i₀, by simpa using i₀.1.isLt⟩ z hz

end DeriveInduction

/-! ## The verifier run carries a challenge entry -/

section VerifierRun

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- **The OptionT peel of the Fiat-Shamir verifier run**: the run is the transcript
derivation followed by the ambient-lifted underlying verifier. -/
theorem fiatShamir_verifier_run_peeled
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (messages : pSpec.Messages) :
    ((V.fiatShamir.run stmtIn
        (fun i => match i with | ⟨0, _⟩ => messages)).run
      : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut))
      = Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages >>= fun T =>
          ((V.verify stmtIn T).run.liftComp
            (oSpec + fsChallengeOracle StmtIn pSpec) >>= fun v => pure v) := by
  simp only [Verifier.run, Verifier.fiatShamir, OptionT.run_bind, OptionT.run_monadLift,
    monadLift_self, Option.elimM, OptionT.run_pure, bind_assoc, pure_bind,
    Option.elim_some, OptionT.run_liftM_run, Reduction.optionT_run_getM,
    Reduction.option_elim_pure_pure_some, bind_map_left]
  simp only [← OracleComp.liftComp_def]

/-- **The logged Fiat-Shamir verifier run has a challenge entry**: the re-derivation of
the transcript queries the challenge oracle at every challenge round, and a challenge
round exists. -/
theorem fiatShamir_verifier_logged_right_entry
    (hne : Nonempty pSpec.ChallengeIdx)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (messages : pSpec.Messages)
    {z : Option StmtOut × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)}
    (hz : z ∈ support ((simulateQ loggingOracle
      ((V.fiatShamir.run stmtIn
        (fun i => match i with | ⟨0, _⟩ => messages)).run)).run)) :
    ∃ e ∈ z.2, e.1.isRight = true := by
  rw [fiatShamir_verifier_run_peeled] at hz
  obtain ⟨y, log⟩ := z
  obtain ⟨T, la, lb, hla, -, hsplit⟩ := mem_support_loggingOracle_bind_split hz
  subst hsplit
  obtain ⟨e, he, hright⟩ := deriveTranscriptFS_logged_right_entry hne stmtIn messages hla
  exact ⟨e, List.mem_append_left _ he, hright⟩

end VerifierRun

/-! ## R3 discharged -/

section R3Discharge

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- **R3 holds**: with a challenge round present, every `some`-output of the eager-rand
basic Fiat-Shamir game has a verifier log with at least one `fsChallengeOracle` entry —
the verifier's transcript re-derivation queries the challenge oracle. -/
theorem hyb4ChallengeEntryResidual_holds :
    Hyb4ChallengeEntryResidual (pSpec := pSpec) (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) := by
  intro hne _ oImpl V P' out hout
  simp only [KeyLemmaFoundations.basicFiatShamirGameEagerRand,
    mem_support_bind_iff] at hout
  obtain ⟨c, -, ⟨⟨stmtIn, messages⟩, pLogAll⟩, -, hout⟩ := hout
  simp only [mem_support_bind_iff] at hout
  obtain ⟨⟨stmtOut?, vLog⟩, hv, hout⟩ := hout
  have hv' : (stmtOut?, vLog) ∈ support ((simulateQ loggingOracle
      ((V.fiatShamir.run stmtIn
        (fun i => match i with | ⟨0, _⟩ => messages)).run)).run) :=
    VerifierReplay.support_simulateQ_subset _ _ hv
  rcases stmtOut? with _ | stmtOut
  · simp at hout
  · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hout
    subst hout
    exact projectRightQueryLog_ne_nil_of_exists_isRight
      (fiatShamir_verifier_logged_right_entry hne V stmtIn messages hv')

end R3Discharge

end DuplexSpongeFS.Hyb34LogShapeFalse

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.mem_support_loggingOracle_bind_split
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.mem_support_loggingOracle_query_right_bind
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.deriveTranscriptSRAux_logged_right_entry
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.fiatShamir_verifier_run_peeled
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.fiatShamir_verifier_logged_right_entry
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.hyb4ChallengeEntryResidual_holds
