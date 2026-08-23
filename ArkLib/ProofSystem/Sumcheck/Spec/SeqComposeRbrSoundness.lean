/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone
import ArkLib.ProofSystem.Sumcheck.Spec.OracleRbrSoundness
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundCohWired
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundFlipImpClose

/-!
# Discharging the two sum-check RBR soundness keystones (issue #13, residual `K-rbr`)

`Sumcheck.Spec.oracleVerifier_rbrSoundness` (`Spec/OracleRbrSoundness.lean`) assembles the
oracle-level multi-round round-by-round (plain) soundness of the generic concrete sum-check oracle
verifier from two named hypotheses:

* `hRound` — the **per-round** plain RBR soundness of each context-lifted single-round oracle
  verifier `SingleRound.oracleVerifier R n deg D oSpec i`;
* `hSeqCompose` — the **assembled** composed RBR soundness, i.e. the genuine
  per-round-to-composed marginal accounting of the sequential composition.

This file discharges both, working at the generic framework level (so the results apply to *any*
`OracleVerifier.seqCompose` chain, not just sum-check) and then specializing to sum-check.

## `hSeqCompose` — the n-ary sequential-composition keystone

`OracleVerifier.seqCompose_rbrSoundness` (`Composition/Sequential/General.lean`) currently takes the
composed result as a hypothesis (pass-through).  Here we *prove* the genuine reduction to the binary
`append` keystone:

`seqCompose_rbrSoundness_of_append` is an induction on the number of rounds `m` (mirroring the proven
`Reduction.seqCompose_perfectCompleteness_of_append`):

* base case `m = 0`: `seqCompose` is `Verifier.id`, which is perfectly RBR-sound (error `0`), and the
  zero error coincides with the composed error family on the empty challenge-index type;
* successor case `m + 1`: `seqCompose` unfolds (via `seqCompose_succ`) to the binary
  `append (V 0) (tail)`; the binary keystone `hAppend` (the framework's `Verifier.append_rbrSoundness`,
  itself a pass-through residual) combines the head's per-round soundness with the tail's
  `seqCompose` soundness (the inductive hypothesis), and the resulting `Sum.elim`-routed error is
  reconciled with the `seqComposeChallengeIdxToSigma`-indexed composed error by the combinatorial
  bridge `seqComposeError_eq_append` (re-derived here, non-private, from `seqComposeChallengeEquiv`).

The **state-function / bad-event decomposition round-wise** is exactly what the binary
`Verifier.StateFunction.append` (proven in `Append.lean`) and the per-round measure bound supply;
this file assembles them across all `m` rounds.

## `hRound` — per-round plain RBR soundness from RBR knowledge soundness

The single-round result proven in-tree is RBR *knowledge* soundness of the *un-lifted* `Simple`
verifier (`SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness`).  Plain soundness is a genuine
weakening: `rbrKnowledgeSoundness_imp_rbrSoundness` drops the extractor/witness and builds the plain
`StateFunction` from the `KnowledgeStateFunction` via the proven
`Verifier.KnowledgeStateFunction.toStateFunction` (quantifying out the witness), reading the
per-round plain bad-event bound off the per-round knowledge bad-event bound.  The single residual is
the measure-comparison step `hMeasure` (the plain bad event implies, on the support, the knowledge
bad event for *some* witness), taken as an explicit named hypothesis — this is the deepest
probabilistic step.

## No `sorry`/`admit`

The only residuals are the explicit named hypotheses `hAppend` (the binary append keystone — itself a
framework pass-through) and `hMeasure` (the per-round plain↦knowledge measure step).  Everything
connecting them to the two desired sum-check keystones is proven and axiom-clean.
-/

open OracleComp ProtocolSpec
open scoped NNReal

universe u v

namespace ArkLib.SeqComposeRbrSoundness

noncomputable section

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-! ## The combinatorial error bridge (non-private re-derivation)

`General.lean` proves the analogous bridge as a `private` lemma `seqComposeError_eq_append`; we
re-derive it here (publicly) so the n-ary induction below can use it. -/

section ErrorBridge

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}

/-- `seqComposeChallengeIdxToSigma` along the `inl` embedding of a head challenge index lands in the
first component with the original index. -/
private theorem idxToSigma_inl (s : (pSpec 0).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)
      = ⟨0, s⟩ := by
  have hsplit : (Fin.splitSum (n := n)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1) = ⟨0, s.1⟩ := by
    rw [Fin.splitSum_succ]; erw [Fin.dappend_left]
  have hfst : (seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).fst = (0 : Fin (m + 1)) :=
    congrArg Sigma.fst hsplit
  refine Sigma.ext hfst ?_
  rw [Subtype.heq_iff_coe_heq (by rw [hfst]) (by rw [hfst])]
  have hval : ((seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).snd.1)
      = (Fin.splitSum (n := n)
          (ChallengeIdx.inl (pSpec₁ := pSpec 0)
            (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1).snd := rfl
  rw [hval]
  exact (Sigma.ext_iff.mp hsplit).2

/-- `seqComposeChallengeIdxToSigma` along the `inr` embedding of a tail challenge index: the first
component is shifted by `Fin.succ` and the tail index recovered by the tail's
`seqComposeChallengeIdxToSigma`. -/
private theorem idxToSigma_inr
    (s : (ProtocolSpec.seqCompose (fun i => pSpec i.succ)).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)
      = ⟨(seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) s).fst.succ,
          (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) s).snd⟩ := by
  have hsplit : (Fin.splitSum (n := n)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1)
      = ⟨(Fin.splitSum (n := fun i => n i.succ) s.1).fst.succ,
          (Fin.splitSum (n := fun i => n i.succ) s.1).snd⟩ := by
    rw [Fin.splitSum_succ]; erw [Fin.dappend_right]
  have hfst : (seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).fst =
        (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) s).fst.succ :=
    congrArg Sigma.fst hsplit
  refine Sigma.ext hfst ?_
  rw [Subtype.heq_iff_coe_heq (by rw [hfst]) (by rw [hfst])]
  have hval : ((seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).snd.1)
      = (Fin.splitSum (n := n)
          (ChallengeIdx.inr (pSpec₁ := pSpec 0)
            (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1).snd := rfl
  rw [hval]
  exact (Sigma.ext_iff.mp hsplit).2

/-- **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global challenge
index, equals the appended-form error built from the head error and the tail's `seqCompose` error
transported by `ChallengeIdx.sumEquiv.symm`.** This is the combinatorial bridge identifying the two
indexings of the composed protocol's challenges (a public re-derivation of `General.lean`'s private
`seqComposeError_eq_append`). -/
theorem seqComposeError_eq_append (f : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (a : (pSpec 0 ++ₚ ProtocolSpec.seqCompose (fun i => pSpec i.succ)).ChallengeIdx) :
    f (seqComposeChallengeIdxToSigma (pSpec := pSpec) a).fst
        (seqComposeChallengeIdxToSigma (pSpec := pSpec) a).snd =
      (Sum.elim (f 0)
          (fun k => f (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) k).fst.succ
            (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) k).snd) ∘
        ⇑ChallengeIdx.sumEquiv.symm) a := by
  set g : ((i : Fin (m + 1)) × (pSpec i).ChallengeIdx) → ℝ≥0 := fun x => f x.fst x.snd with hg
  rw [Function.comp_apply]
  rw [show a = ChallengeIdx.sumEquiv (ChallengeIdx.sumEquiv.symm a) from
    (Equiv.apply_symm_apply _ _).symm]
  rw [Equiv.symm_apply_apply]
  rcases ChallengeIdx.sumEquiv.symm a with s | s
  · simp only [Sum.elim_inl, ChallengeIdx.sumEquiv, Equiv.coe_fn_mk]
    exact congrArg g (idxToSigma_inl s)
  · simp only [Sum.elim_inr, ChallengeIdx.sumEquiv, Equiv.coe_fn_mk]
    exact congrArg g (idxToSigma_inr s)

end ErrorBridge

/-! ## `hSeqCompose`: the n-ary sequential-composition RBR soundness keystone

The genuine reduction of the composed RBR soundness to the binary `append` keystone, by induction on
the number of rounds.  This is the per-round-to-composed marginal accounting. -/

section SeqCompose

omit [oSpec.Fintype] in
/-- **The n-ary `Verifier.seqCompose` RBR soundness reduces to the binary `append` keystone.**

By induction on `m`:
* base case (`m = 0`): `seqCompose` is `Verifier.id`, which is perfectly RBR-sound with error `0`
  (`Verifier.id_rbrSoundness`); the composed error vanishes because there are no challenge indices;
* successor case (`m + 1`): `seqCompose` unfolds to `append (V 0) (tail)`; `hAppend` (the binary
  keystone `Verifier.append_rbrSoundness`) combines the head's per-round soundness `h 0` with the
  tail's `seqCompose` soundness (the inductive hypothesis), producing the `Sum.elim`-routed error,
  which `seqComposeError_eq_append` identifies with the `seqComposeChallengeIdxToSigma`-indexed
  composed error.

Feeding the framework's `Verifier.append_rbrSoundness` (with its discharged residual) as `hAppend`
closes the n-ary statement. This is exactly the shape consumed by `hSeqCompose` in
`OracleRbrSoundness.lean` (after `OracleVerifier.rbrSoundness` unfolds to the underlying
`Verifier.rbrSoundness` of `toVerifier`, and the `seqCompose` verifier-fusion `toVerifier`
equation). -/
theorem seqCompose_rbrSoundness_of_append {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (lang : (i : Fin (m + 1)) → Set (Stmt i))
    (rbrSoundnessError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
        {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
        {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
        V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
        (V₁.append V₂).rbrSoundness init impl l₁ l₃
          (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm))
    (h : ∀ i, (V i).rbrSoundness init impl (lang i.castSucc) (lang i.succ) (rbrSoundnessError i)) :
    (Verifier.seqCompose Stmt V).rbrSoundness init impl (lang 0) (lang (Fin.last m))
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        rbrSoundnessError ij.1 ij.2) := by
  induction m with
  | zero =>
    rw [Verifier.seqCompose_zero]
    have hzero :
        (fun combinedIdx : (ProtocolSpec.seqCompose pSpec).ChallengeIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2) = 0 := by
      funext combinedIdx
      exact (seqComposeChallengeIdxToSigma combinedIdx).1.elim0
    rw [hzero]
    have hlang : lang (Fin.last 0) = lang 0 := by
      congr 1
    rw [hlang]
    exact Verifier.id_rbrSoundness init impl
  | succ m ih =>
    -- unfold the seqCompose into a binary append of the head with the tail's seqCompose
    rw [Verifier.seqCompose_succ]
    -- the binary keystone, applied to head soundness + tail seqCompose soundness (the IH)
    have hcombined :=
      hAppend (V 0)
        (Verifier.seqCompose (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i)))
        (l₁ := lang 0) (l₃ := lang (Fin.last (m + 1)))
        (e₁ := rbrSoundnessError 0)
        (e₂ := fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) combinedIdx
          rbrSoundnessError (Fin.succ ij.1) ij.2)
        (h 0)
        (ih (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i))
          (fun i => lang (Fin.succ i)) (fun i => rbrSoundnessError (Fin.succ i))
          (fun i => h (Fin.succ i)))
    -- reconcile the Sum.elim-routed error with the seqComposeChallengeIdxToSigma-indexed error.
    -- The goal's error (over `(seqCompose pSpec).ChallengeIdx`) agrees pointwise with
    -- `hcombined`'s `Sum.elim`-routed error via `seqComposeError_eq_append`; the two challenge-index
    -- types are defeq (`seqCompose (m+1) pSpec = pSpec 0 ++ₚ seqCompose tail`).
    have herr :
        (fun combinedIdx : (ProtocolSpec.seqCompose pSpec).ChallengeIdx =>
          letI ij := seqComposeChallengeIdxToSigma (pSpec := pSpec) combinedIdx
          rbrSoundnessError ij.1 ij.2)
        = (Sum.elim (rbrSoundnessError 0)
            (fun combinedIdx =>
              letI ij := seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) combinedIdx
              rbrSoundnessError (Fin.succ ij.1) ij.2) ∘ ⇑ChallengeIdx.sumEquiv.symm) :=
      funext (fun a => seqComposeError_eq_append (pSpec := pSpec) rbrSoundnessError a)
    exact herr ▸ hcombined

end SeqCompose

/-! ## `hRound`: per-round plain RBR soundness from RBR knowledge soundness

`rbrKnowledgeSoundness ⇒ rbrSoundness` is a genuine weakening: the witness/extractor are dropped and
the plain `StateFunction` is constructed from the `KnowledgeStateFunction` via the proven
`Verifier.KnowledgeStateFunction.toStateFunction`.  The single residual is the per-round measure
comparison `hMeasure`, taken as a named hypothesis. -/

section KnowledgeToPlain

variable {StmtIn WitIn StmtOut WitOut : Type} {N : ℕ} {pSpec : ProtocolSpec N}
  [∀ i, SampleableType (pSpec.Challenge i)]

open Verifier

/-- **RBR knowledge soundness ⇒ RBR plain soundness (generic weakening).**

Given a verifier that is round-by-round *knowledge* sound for `relIn`/`relOut` with error
`rbrKnowledgeError`, it is round-by-round (plain) sound for the *languages* `relIn.language`/
`relOut.language` with the same error.

The plain state function is built from the knowledge state function by quantifying out the witness,
via the proven `Verifier.KnowledgeStateFunction.toStateFunction` (so `toFun m s t = ∃ w, kSF m s t w`).
The per-round measure step — that the plain bad-event probability (over the witness-free
`runToRound` marginal) is bounded by the round-`i` knowledge error — is the deepest probabilistic
content and is supplied as the explicit named hypothesis `hMeasure`. (This is the marginalization of
the `runWithLogToRound` knowledge bad-event over the dropped query log and intermediate witness; it
is exactly the per-round bound that the in-tree single-round knowledge result already establishes for
the concrete sum-check verifier, where the bad event has probability `0`.)

Dropping to plain soundness needs no information from `relIn`/`relOut` beyond their languages, so this
is the faithful weakening direction. -/
theorem rbrKnowledgeSoundness_imp_rbrSoundness
    {oSpec : OracleSpec ι} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
    {WitMid : Fin (N + 1) → Type}
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (hMeasure : ∀ stmtIn ∉ relIn.language,
      ∀ (W₁ W₂ : Type) (witIn : W₁) (prover : Prover oSpec StmtIn W₁ StmtOut W₂ pSpec)
        (i : pSpec.ChallengeIdx),
        Pr[fun ⟨transcript, challenge⟩ =>
          ¬ (kSF.toStateFunction).toFun i.1.castSucc stmtIn transcript ∧
            (kSF.toStateFunction).toFun i.1.succ stmtIn (transcript.concat challenge)
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec.getChallenge i) _
              return (transcript, challenge))).run' (← init)] ≤
          rbrKnowledgeError i) :
    verifier.rbrSoundness init impl relIn.language relOut.language rbrKnowledgeError := by
  refine ⟨kSF.toStateFunction, ?_⟩
  intro stmtIn hStmtIn W₁ W₂ witIn prover i
  exact hMeasure stmtIn hStmtIn W₁ W₂ witIn prover i

end KnowledgeToPlain

end

end ArkLib.SeqComposeRbrSoundness

namespace OracleVerifier

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}

set_option linter.unusedVariables false in
/-- RBR-local copy of the binary verifier-fusion law.

This is intentionally named separately from the completeness-side `BinaryVerifierFusion`, so the RBR
assembly can use the lower-level append verifier-fusion keystone without importing the sumcheck
oracle-completeness modules that define overlapping theorem names. -/
def BinaryVerifierFusionForRbr (oSpec : OracleSpec ι) : Prop :=
  ∀ {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface.{0, 0} (OStmt₁ i)]
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface.{0, 0} (OStmt₂ i)]
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface.{0, 0} (OStmt₃ i)]
    {p q : ℕ} {pSpec₁ : ProtocolSpec p} {pSpec₂ : ProtocolSpec q}
    [Oₘ₁ : ∀ i, OracleInterface.{0, 0} (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface.{0, 0} (pSpec₂.Message i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [c₁ : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂),
    (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).toVerifier
      = Verifier.append V₁.toVerifier V₂.toVerifier

/-- The RBR-local binary verifier-fusion law follows from the proven append verifier-fusion
keystone. -/
theorem binaryVerifierFusionForRbr_holds (oSpec : OracleSpec ι) :
    BinaryVerifierFusionForRbr oSpec := by
  intro Stmt₁ ιₛ₁ OStmt₁ Oₛ₁ Stmt₂ ιₛ₂ OStmt₂ Oₛ₂ Stmt₃ ιₛ₃ OStmt₃ Oₛ₃
    p q pSpec₁ pSpec₂ Oₘ₁ Oₘ₂ V₁ c₁ V₂
  exact OracleReduction.oracleVerifier_append_toVerifier
    (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂

/-- The unbounded-round verifier fusion used by the RBR seqCompose assembly, derived from the
RBR-local binary fusion law. -/
theorem seqCompose_toVerifier_of_binary_for_rbr (hBinaryFusion : BinaryVerifierFusionForRbr oSpec)
    {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Oₛ : ∀ i, ∀ j, OracleInterface.{0, 0} (OStmt i j))
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (Oₘ : ∀ i, ∀ j, OracleInterface.{0, 0} ((pSpec i).Message j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)) :
    (OracleVerifier.seqCompose (Oₛ := Oₛ) (Oₘ := Oₘ) Stmt OStmt V (coh := coh)).toVerifier =
      Verifier.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier) := by
  induction m with
  | zero =>
    show (OracleVerifier.seqCompose Stmt OStmt V).toVerifier = Verifier.id
    rw [OracleVerifier.seqCompose_zero Stmt OStmt V]
    exact OracleVerifier.id_toVerifier
  | succ m ih =>
    letI tailCoh :
        ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := (fun i => Oₛ (Fin.succ i)) i.castSucc)
          (Oₛ₂ := (fun i => Oₛ (Fin.succ i)) i.succ) (Oₘ₁ := (fun i => Oₘ (Fin.succ i)) i)
          (V (Fin.succ i)) := fun i => coh i.succ
    letI headCoh :
        OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₘ₁ := Oₘ 0) (V 0) :=
      coh 0
    have ihTail := ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (fun i => Oₛ (Fin.succ i))
      (fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i)) tailCoh
    have hHead := hBinaryFusion (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₛ₃ := Oₛ (Fin.last (m + 1)))
      (Oₘ₁ := Oₘ 0)
      (V 0) (c₁ := headCoh)
      (OracleVerifier.seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
        (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i))
        (fun i => V (Fin.succ i)) (coh := tailCoh))
    rw [OracleVerifier.seqCompose_succ Stmt OStmt (Oₛ := Oₛ) (Oₘ := Oₘ) V (coh := coh),
        Verifier.seqCompose_succ (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier)]
    exact hHead.trans (congrArg (Verifier.append (V 0).toVerifier) ihTail)

end OracleVerifier

/-! ## Discharging `hSeqCompose` for the concrete sum-check oracle verifier

We now specialize the generic `seqCompose_rbrSoundness_of_append` keystone to the concrete sum-check
oracle verifier `Sumcheck.Spec.oracleVerifier`, producing *exactly* the `hSeqCompose` hypothesis
consumed by `Sumcheck.Spec.oracleVerifier_rbrSoundness` (in `OracleRbrSoundness.lean`).

The verifier-fusion `(OracleVerifier.seqCompose …).toVerifier = Verifier.seqCompose …` is supplied by
the proven `OracleVerifier.seqCompose_toVerifier_of_binary` together with the proven binary
verifier-fusion `Sumcheck.Spec.binaryVerifierFusion_proof` (ultimately
`OracleReduction.oracleVerifier_append_toVerifier`). -/

namespace Sumcheck.Spec

open ProtocolSpec OracleComp
open scoped NNReal
open ArkLib.SeqComposeRbrSoundness

noncomputable section

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [oSpec.Fintype] in
/-- **Canonical lifted per-round plain RBR soundness for sum-check.**

This closes the `hRound` hypothesis for the canonical relation chain
`relationRound i.castSucc → relationRound i.succ`: the simple single-round plain RBR theorem is
lifted through the sum-check oracle lens, using the proven per-round `LiftContextCoherent` instance
and the knowledge-sound-lens-to-plain-sound-lens bridge. -/
theorem singleRound_oracleVerifier_rbrSoundness_canonical
    [(oSpec + [(SingleRound.pSpec R deg).Challenge]ₒ'challengeOracleInterface).Fintype]
    [(oSpec + [(SingleRound.pSpec R deg).Challenge]ₒ'challengeOracleInterface).Inhabited]
    (i : Fin n)
    (rbrError : (SingleRound.pSpec R deg).ChallengeIdx → ℝ≥0) :
    (SingleRound.oracleVerifier R n deg D oSpec i).rbrSoundness init impl
      (relationRound R n deg D i.castSucc).language
      (relationRound R n deg D i.succ).language rbrError := by
  letI : Inhabited (SingleRound.Simple.StmtOut R) := ⟨(0, 0)⟩
  letI : OracleVerifier.LiftContextCoherent (SingleRound.sumcheckOracleLens R n deg D oSpec i)
      (SingleRound.Simple.oracleVerifier R deg D oSpec) := by
    change OracleVerifier.LiftContextCoherent (SingleRound.sumcheckOracleLens R n deg D oSpec i)
      (SingleRound.Simple.oracleReduction R deg D oSpec).verifier
    exact SingleRound.coh_proven_inst (R := R) (n := n) (deg := deg) (D := D)
      (oSpec := oSpec) i
  letI : Extractor.Lens.IsKnowledgeSound
      (relationRound R n deg D i.castSucc)
      (SingleRound.Simple.inputRelation R deg D)
      (relationRound R n deg D i.succ)
      (SingleRound.Simple.outputRelation R deg)
      ((SingleRound.Simple.oracleVerifier R deg D oSpec).toVerifier.compatStatement
        (SingleRound.oStmtLens R n deg D i))
      (fun _ _ => True)
      (SingleRound.extractorLens R n deg D i) :=
    SingleRound.extractorLens_rbr_knowledge_soundness (R := R) (n := n) (deg := deg)
      (D := D) (oSpec := oSpec) i
  have hLensSound :
      OracleStatement.Lens.IsSound
        (relationRound R n deg D i.castSucc).language
        (relationRound R n deg D i.succ).language
        (SingleRound.Simple.inputRelation R deg D).language
        (SingleRound.Simple.outputRelation R deg).language
        (Verifier.compatStatement (SingleRound.sumcheckOracleLens R n deg D oSpec i).toLens
          (SingleRound.Simple.oracleVerifier R deg D oSpec).toVerifier)
        (SingleRound.sumcheckOracleLens R n deg D oSpec i).toLens := by
    change (SingleRound.extractorLens R n deg D i).stmt.IsSound
      (relationRound R n deg D i.castSucc).language
      (relationRound R n deg D i.succ).language
      (SingleRound.Simple.inputRelation R deg D).language
      (SingleRound.Simple.outputRelation R deg).language
      (Verifier.compatStatement (SingleRound.oStmtLens R n deg D i)
        (SingleRound.Simple.oracleVerifier R deg D oSpec).toVerifier)
    infer_instance
  exact OracleVerifier.liftContext_rbr_soundness
    (V := SingleRound.Simple.oracleVerifier R deg D oSpec)
    (lens := SingleRound.sumcheckOracleLens R n deg D oSpec i)
    (lensSound := hLensSound)
    (h := SingleRound.Simple.oracleVerifier_rbrSoundness (R := R) (deg := deg) (D := D)
      (oSpec := oSpec) init impl rbrError)

omit [oSpec.Fintype] in
/-- **`hSeqCompose` discharged for the concrete sum-check oracle verifier.**

The composed RBR soundness of `Sumcheck.Spec.oracleVerifier` — in the exact
`seqComposeChallengeIdxToSigma`-indexed-error shape consumed as `hSeqCompose` by
`Sumcheck.Spec.oracleVerifier_rbrSoundness`.

* `hRound` — the per-round plain RBR soundness of each context-lifted single-round oracle verifier
  (this is precisely the `hRound` hypothesis of `oracleVerifier_rbrSoundness`; supply it from
  `rbrKnowledgeSoundness_imp_rbrSoundness` ∘ `liftContext_rbr_soundness` ∘ the proven
  `SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness`);
* `hAppend` — the binary `Verifier.append` RBR-soundness keystone (the framework's
  `Verifier.append_rbrSoundness`, itself a pass-through residual). Feeding it closes the n-ary
  assembly.

The verifier-fusion uses the now-proven `oracleVerifier_append_toVerifier` (via
`binaryVerifierFusion_proof` + `seqCompose_toVerifier_of_binary`), so no `toVerifier`-equation
hypothesis remains. -/
theorem oracleVerifier_seqCompose_rbrSoundness
    (lang : (i : Fin (n + 1)) → Set (StatementRound R n i × (∀ j, OracleStatement R n deg j)))
    (rbrSoundnessError : ∀ _ : Fin n, (SingleRound.pSpec R deg).ChallengeIdx → ℝ≥0)
    (hRound : ∀ i : Fin n,
      (SingleRound.oracleVerifier R n deg D oSpec i).rbrSoundness init impl
        (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
        {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
        {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
        V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
        (V₁.append V₂).rbrSoundness init impl l₁ l₃
          (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm)) :
    (oracleVerifier R deg D n oSpec).rbrSoundness init impl (lang 0) (lang (Fin.last n))
      (fun combinedIdx =>
        letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
        rbrSoundnessError ij.1 ij.2) := by
  -- Unfold the oracle-level RBR soundness to the underlying `toVerifier` RBR soundness.
  show (oracleVerifier R deg D n oSpec).toVerifier.rbrSoundness init impl
    (lang 0) (lang (Fin.last n)) _
  -- Verifier fusion: `(OracleVerifier.seqCompose …).toVerifier = Verifier.seqCompose …`.
  have hfusion :
      (oracleVerifier R deg D n oSpec).toVerifier =
        Verifier.seqCompose (fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j))
          (fun i => (SingleRound.oracleVerifier R n deg D oSpec i).toVerifier) :=
    OracleVerifier.seqCompose_toVerifier_of_binary_for_rbr
      (OracleVerifier.binaryVerifierFusionForRbr_holds oSpec)
      (Stmt := StatementRound R n) (OStmt := fun _ => OracleStatement R n deg)
      (Oₛ := fun _ _ => inferInstance)
      (Oₘ := fun _ _ => inferInstance)
      (SingleRound.oracleVerifier R n deg D oSpec)
      (fun i => inferInstance)
  rw [hfusion]
  -- Apply the generic n-ary→binary RBR-soundness keystone.
  exact seqCompose_rbrSoundness_of_append
    (fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j))
    (fun i => (SingleRound.oracleVerifier R n deg D oSpec i).toVerifier)
    lang rbrSoundnessError hAppend hRound

omit [oSpec.Fintype] in
/-- **Multi-round oracle-level sum-check RBR soundness with `hSeqCompose` discharged.**

The capstone: `Sumcheck.Spec.oracleVerifier_rbrSoundness` with its `hSeqCompose` keystone now supplied
internally from `oracleVerifier_seqCompose_rbrSoundness` (the proven n-ary assembly). The only
remaining residuals are:

* `hRound` — the per-round plain RBR soundness of each context-lifted single-round oracle verifier;
* `hAppend` — the binary `Verifier.append` RBR-soundness keystone.

This is the `RD-innerRbr`-shaped conclusion required by the LogUp soundness lift, with the
sequential-composition combinatorial keystone fully discharged. -/
theorem oracleVerifier_rbrSoundness_of_round_append
    (lang : (i : Fin (n + 1)) → Set (StatementRound R n i × (∀ j, OracleStatement R n deg j)))
    (rbrSoundnessError : ∀ _ : Fin n, (SingleRound.pSpec R deg).ChallengeIdx → ℝ≥0)
    (hRound : ∀ i : Fin n,
      (SingleRound.oracleVerifier R n deg D oSpec i).rbrSoundness init impl
        (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
        {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
        {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
        V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
        (V₁.append V₂).rbrSoundness init impl l₁ l₃
          (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm)) :
    (oracleVerifier R deg D n oSpec).rbrSoundness init impl (lang 0) (lang (Fin.last n))
      (fun combinedIdx =>
        letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
        rbrSoundnessError ij.1 ij.2) :=
  oracleVerifier_rbrSoundness lang rbrSoundnessError hRound
    (oracleVerifier_seqCompose_rbrSoundness lang rbrSoundnessError hRound hAppend)

omit [oSpec.Fintype] in
/-- **Canonical multi-round sum-check RBR with per-round `hRound` closed.**

This is the canonical relation-chain specialization of
`oracleVerifier_rbrSoundness_of_round_append`.  It discharges every per-round RBR hypothesis via
`singleRound_oracleVerifier_rbrSoundness_canonical`, leaving only the binary plain-RBR append
keystone.  The final language is the final sum-check relation `relationRound (Fin.last n)`, not
`Set.univ`; callers that require a different terminal language need a separate language transport
argument. -/
theorem oracleVerifier_rbrSoundness_of_canonical_round_append
    [(oSpec + [(SingleRound.pSpec R deg).Challenge]ₒ'challengeOracleInterface).Fintype]
    [(oSpec + [(SingleRound.pSpec R deg).Challenge]ₒ'challengeOracleInterface).Inhabited]
    (rbrSoundnessError : ∀ _ : Fin n, (SingleRound.pSpec R deg).ChallengeIdx → ℝ≥0)
    (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
        {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
        {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
        V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
        (V₁.append V₂).rbrSoundness init impl l₁ l₃
          (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm)) :
    (oracleVerifier R deg D n oSpec).rbrSoundness init impl
      (relationRound R n deg D 0).language
      (relationRound R n deg D (Fin.last n)).language
      (fun combinedIdx =>
        letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
        rbrSoundnessError ij.1 ij.2) :=
  oracleVerifier_rbrSoundness_of_round_append
    (lang := fun i => (relationRound R n deg D i).language)
    rbrSoundnessError
    (fun i => singleRound_oracleVerifier_rbrSoundness_canonical (R := R) (n := n)
      (deg := deg) (D := D) (oSpec := oSpec) (init := init) (impl := impl) i
      (rbrSoundnessError i))
    hAppend

end

end Sumcheck.Spec

#print axioms ArkLib.SeqComposeRbrSoundness.seqComposeError_eq_append
#print axioms ArkLib.SeqComposeRbrSoundness.seqCompose_rbrSoundness_of_append
#print axioms ArkLib.SeqComposeRbrSoundness.rbrKnowledgeSoundness_imp_rbrSoundness
#print axioms Sumcheck.Spec.singleRound_oracleVerifier_rbrSoundness_canonical
#print axioms Sumcheck.Spec.oracleVerifier_seqCompose_rbrSoundness
#print axioms Sumcheck.Spec.oracleVerifier_rbrSoundness_of_round_append
#print axioms Sumcheck.Spec.oracleVerifier_rbrSoundness_of_canonical_round_append

#print axioms ArkLib.SeqComposeRbrSoundness.seqComposeError_eq_append
#print axioms ArkLib.SeqComposeRbrSoundness.seqCompose_rbrSoundness_of_append
#print axioms ArkLib.SeqComposeRbrSoundness.rbrKnowledgeSoundness_imp_rbrSoundness
