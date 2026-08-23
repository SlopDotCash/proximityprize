/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations
import ArkLib.ProofSystem.Binius.BinaryBasefold.BitsOfIndex
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.ProjectToMidLastEval
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.ProjectToMidSucc
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.ProjectToNextSumEq
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.FinalOracleBridge
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.IteratedFoldToLevel
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.FinalConstantWeld
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.SimulationInfrastructure
import ArkLib.OracleReduction.Completeness
import ArkLib.Data.Misc.Basic

/-!
## Binary Basefold single steps
- **Fold step** :
  P sends V the polynomial `h_i(X) := Σ_{w ∈ B_{ℓ-i-1}} h(r'_0, ..., r'_{i-1}, X, w_0, ...
  w_{ℓ-i-2})`.
  V requires `s_i ?= h_i(0) + h_i(1)`. V samples `r'_i ← L`, sets `s_{i+1} := h_i(r'_i)`,
  and sends P `r'_i`.
- **Relay step** : transform relOut of fold step in case of non-commitment round to match
  roundRelation
- **Commit step** :
    P defines `f^(i+1): S^(i+1) → L` as the function `fold(f^(i), r'_i)` of Definition 4.6.
    if `i+1 < ℓ` and `ϑ | i+1` then
    P submits (submit, ℓ+R-i-1, f^(i+1)) to the oracle `F_Vec^L`
- **Final sum-check step** :
  - P sends V the final constant `c := f^(ℓ)(0, ..., 0)`
  - V verifies : `s_ℓ = eqTilde(r, r') * c`
  => `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})`
-/

set_option maxHeartbeats 400000
set_option linter.style.longFile 2000
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Sumcheck.Structured
open Binius.BinaryBasefold
open scoped NNReal

/-- Taking the rightmost `n` entries after consing one value drops the cons head. -/
theorem fin_rtake_cons_const {n : ℕ} {α : Type*} (x : α) (v : Fin n → α) :
    Fin.rtake (n := n + 1) (α := fun _ : Fin (n + 1) => α)
      (m := n) (v := Fin.cons x v) (h := Nat.le_succ n) = v := by
  funext i
  simp [Fin.rtake, Fin.natAdd]
  rw [show (⟨1 + i.val, by omega⟩ : Fin (n + 1)) = i.succ by
    ext
    simp only [Fin.val_succ]
    omega
  ]
  exact Fin.cons_succ (α := fun _ => α) x v i

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

omit [Field L] [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L]
  [NeZero r] [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
/-- Successor-index form of `getFoldingChallenges_rtake_self`, matching commit-step goals. -/
lemma getFoldingChallenges_rtake_self_succ (i : Fin ℓ)
    (challenges : Fin i.succ → L) (k : ℕ)
    (h h' : k + ϑ ≤ i.succ)
    (hr : i.val + 1 ≤ i.val + 1) :
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.succ
      (Fin.rtake (n := i.val + 1) (α := fun _ : Fin (i.val + 1) => L)
        (m := i.val + 1) (v := challenges) (h := hr)) k h =
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.succ challenges k h' := by
  have hrtake :
      Fin.rtake (n := i.val + 1) (α := fun _ : Fin (i.val + 1) => L)
        (m := i.val + 1) (v := challenges) (h := hr) =
      challenges := by
    have hhr : hr = (by omega : i.val + 1 ≤ i.val + 1) := Subsingleton.elim _ _
    rw [hhr]
    exact Fin.rtake_self' challenges
  rw [hrtake]

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- `iterated_fold` is proof-irrelevant in its destination equality and bound proofs. -/
lemma iterated_fold_proof_irrel {i : Fin r} {steps : ℕ} {destIdx : Fin r}
    (h_destIdx h_destIdx' : destIdx.val = i.val + steps)
    (h_destIdx_le h_destIdx_le' : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (destIdx := destIdx)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f) (r_challenges := r_challenges) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (destIdx := destIdx)
      (h_destIdx := h_destIdx') (h_destIdx_le := h_destIdx_le')
      (f := f) (r_challenges := r_challenges) := by
  have h_eq : h_destIdx = h_destIdx' := Subsingleton.elim _ _
  have h_le_eq : h_destIdx_le = h_destIdx_le' := Subsingleton.elim _ _
  subst h_eq
  subst h_le_eq
  rfl

section GenericLogic

def hEq {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type}
    {OracleOut : ιₒₒ → Type} {n : ℕ} {pSpec : ProtocolSpec n}
  (embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx) :=
  ∀ i, OracleOut i =
    match embed i with
    | Sum.inl j => OracleIn j
    | Sum.inr j => pSpec.Message j

/-- The Pure Logic of an interactive reduction step.
Parametrized by a 'Challenges' type that aggregates all verifier randomness. -/
structure ReductionLogicStep
    (StmtIn WitIn : Type)
    {ιₒᵢ ιₒₒ : Type}
    (OracleIn : ιₒᵢ → Type) (OracleOut : ιₒₒ → Type)
    (StmtOut WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) where

  -- 1. The Specification (Relations) - now with indexed oracles
  completeness_relIn    : (StmtIn × (∀ i, OracleIn i)) × WitIn → Prop
  completeness_relOut   : (StmtOut × (∀ i, OracleOut i)) × WitOut → Prop

  -- 2. The Verifier (Pure Logic)
  verifierCheck : StmtIn → FullTranscript pSpec → Prop
  verifierOut   : StmtIn → FullTranscript pSpec → StmtOut

  -- 2b. Oracle Embedding (like OracleVerifier)
  embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx
  hEq : hEq (OracleIn := OracleIn) (OracleOut := OracleOut) (ιₒᵢ := ιₒᵢ) (ιₒₒ := ιₒₒ)
    (pSpec := pSpec) (embed := embed)

  -- 3. The Honest Prover (Pure Logic)
  honestProverTranscript : StmtIn → WitIn → (∀ i, OracleIn i) → pSpec.Challenges → FullTranscript pSpec

  -- 4. The Prover's Output State
  proverOut : StmtIn → WitIn → (∀ i, OracleIn i) → FullTranscript pSpec →
    ((StmtOut × (∀ i, OracleOut i)) × WitOut)

/-- Strong Completeness:
  "For ANY set of challenges, the honest transcript passes the check
   and leads to a valid next state." -/
@[reducible]
def ReductionLogicStep.IsStronglyComplete
    {StmtIn WitIn : Type}
    {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type} {OracleOut : ιₒₒ → Type}
    {StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (step : ReductionLogicStep StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec) : Prop :=
  ∀ (stmtIn : StmtIn) (witIn : WitIn) (oStmtIn : ∀ i, OracleIn i) (challenges : pSpec.Challenges),

    -- Assumption: The input relation holds (valid start state)
    (h_relIn : step.completeness_relIn ((stmtIn, oStmtIn), witIn)) →

    -- 1. Generate the Honest Transcript (Deterministic given challenges)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges

    -- 2. The Verifier MUST accept this transcript
    step.verifierCheck stmtIn transcript ∧

    -- 3. The output MUST be valid and consistent
    let verifierStmtOut := step.verifierOut stmtIn transcript

    -- Compute verifier oracle output via embedding (like OracleVerifier.toVerifier)
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
      oStmtIn transcript
      -- fun i => match h : step.embed i with
      -- | Sum.inl j => by simpa only [step.hEq, h] using (oStmtIn j)
      -- | Sum.inr j => by simpa only [step.hEq, h] using (transcript.messages j)

    let ((proverStmtOut, proverOStmtOut), proverWitOut) :=
      step.proverOut stmtIn witIn oStmtIn transcript

    -- Conclusion A: The Prover's output satisfies the next relation (Soundness/Completeness)
    step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) ∧

    -- Conclusion B: The Prover and Verifier agree on the next statement
    proverStmtOut = verifierStmtOut ∧

    -- Conclusion C: The Prover and Verifier agree on the oracle statements
    proverOStmtOut = verifierOStmtOut

/-- Oracle-aware reduction logic step for protocols where the verifier queries oracles
during verification (e.g., QueryPhase in Binary Basefold).

Unlike `ReductionLogicStep` where `verifierCheck` is a pure `Prop`, here it returns
`OracleComp (oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)) StmtOut` to support oracle
queries during verification. This matches the signature of `OracleVerifier.verify`.

All other components (embed, hEq, relations, proverOut, verifierOut) remain pure,
giving definitional equality when accessed via dot notation. -/
structure OracleAwareReductionLogicStep
    {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn : Type)
    {ιₒᵢ ιₒₒ : Type}
    (OracleIn : ιₒᵢ → Type) (OracleOut : ιₒₒ → Type)
    (StmtOut WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OracleIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] where

  -- 1. The Specification (wRelations) - same as ReductionLogicStep
  completeness_relIn : (StmtIn × (∀ i, OracleIn i)) × WitIn → Prop
  completeness_relOut : (StmtOut × (∀ i, OracleOut i)) × WitOut → Prop

  -- 2. The Verifier (Oracle-Aware)
  -- Key difference: verifierCheck is monadic, can query oracles
  -- Uses the extended spec: oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)
  -- Same signature as OracleVerifier.verify
  verifierCheck : StmtIn → FullTranscript pSpec →
    OracleComp (oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)) StmtOut
  -- Output computation remains pure/deterministic
  verifierOut   : StmtIn → FullTranscript pSpec → StmtOut

  -- 2b. Oracle Embedding (same as ReductionLogicStep)
  embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx
  hEq : hEq (OracleIn := OracleIn) (OracleOut := OracleOut) (ιₒᵢ := ιₒᵢ) (ιₒₒ := ιₒₒ)
    (pSpec := pSpec) (embed := embed)

  -- 3. The Honest Prover (Pure Logic) - same as ReductionLogicStep
  honestProverTranscript : StmtIn → WitIn → (∀ i, OracleIn i)
    → pSpec.Challenges → FullTranscript pSpec

  -- 4. The Prover's Output State - same as ReductionLogicStep
  proverOut : StmtIn → WitIn → (∀ i, OracleIn i) → FullTranscript pSpec →
    ((StmtOut × (∀ i, OracleOut i)) × WitOut)

/-- Strong Completeness Under Simulation for Oracle-Aware Reduction Logic:
  \"For ANY set of challenges, when the verifier check is run under honest oracle simulation,
   it succeeds with probability 1, and the output satisfies the relation.\"

  This is the appropriate notion of completeness for verifiers that query oracles during
  verification (e.g., the query phase in Binary Basefold). Unlike `IsStronglyComplete`,
  which checks the raw `OracleComp`, this checks the simulated execution where oracle
  queries are answered by the honest oracle statements.

  The key difference: In raw execution, oracle queries return arbitrary values, so guards
  checking oracle responses will fail. Under simulation with `simOracle2`, queries are
  answered by `oStmtIn`, making the guards pass.

  **Type Constraint**: The step's `querySpec` must be `oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)`
  for the simulation to type-check. This is the natural structure where:
  - `oSpec` is the shared/base oracle (e.g., random oracle, hash function)
  - `[OracleIn]ₒ` are the oracle statements the verifier can query
  - `[pSpec.Message]ₒ` are the prover messages the verifier can query -/
@[reducible]
def OracleAwareReductionLogicStep.IsStronglyCompleteUnderSimulation
    {ι : Type} {oSpec : OracleSpec ι} [OracleSpec.Fintype oSpec] [OracleSpec.Inhabited oSpec]
    {StmtIn WitIn : Type}
    {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type} {OracleOut : ιₒₒ → Type}
    {StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₛᵢ : ∀ i, OracleInterface (OracleIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    -- The step uses oSpec as its base oracle; internally it accesses
    -- oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)
    (step : OracleAwareReductionLogicStep oSpec
      StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec) : Prop :=
  ∀ (stmtIn : StmtIn) (witIn : WitIn) (oStmtIn : ∀ i, OracleIn i) (challenges : pSpec.Challenges),

    -- Assumption: The input relation holds (valid start state)
    (h_relIn : step.completeness_relIn ((stmtIn, oStmtIn), witIn)) →

    -- 1. Generate the Honest Transcript (Deterministic given challenges)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges

    -- 2. Define the honest oracle simulator
    -- simOracle2 oSpec t₁ t₂ : SimOracle.Stateless (oSpec + ([T₁]ₒ + [T₂]ₒ)) oSpec
    -- This answers queries to OracleIn using oStmtIn and queries to Messages using transcript
    let so := OracleInterface.simOracle2 oSpec oStmtIn transcript.messages

    -- 3. The Verifier check under simulation MUST succeed with probability 1
    Pr[⊥ | simulateQ so (step.verifierCheck stmtIn transcript)] = 0 ∧

    -- 4. The output MUST be valid and consistent
    let verifierStmtOut := step.verifierOut stmtIn transcript

    -- Compute verifier oracle output via embedding (like OracleVerifier.toVerifier)
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
      oStmtIn transcript

    let ((proverStmtOut, proverOStmtOut), proverWitOut) :=
      step.proverOut stmtIn witIn oStmtIn transcript

    -- Conclusion A: The Prover's output satisfies the next relation
    step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) ∧

    -- Conclusion B: The Prover and Verifier agree on the next statement
    proverStmtOut = verifierStmtOut ∧

    -- Conclusion C: The Prover and Verifier agree on the oracle statements
    proverOStmtOut = verifierOStmtOut

/-- **RBR Extraction Failure Event**: Generic predicate for round-by-round knowledge soundness.

This captures when the RBR extractor fails to produce a valid witness at round `i.1.castSucc`,
but a valid witness exists at round `i.1.succ`. This is the fundamental "bad event" that must
be bounded in all RBR knowledge soundness proofs.

**Usage:** Instantiate with protocol-specific `kSF`, `extractor`, and transcript to get the
phase-specific doom-escape event. The `kSF` argument may be a bare state-function or a
`Verifier.KnowledgeStateFunction` (coerced to its `toFun` via the `CoeFun` instance). -/
@[reducible]
def rbrExtractionFailureEvent {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn WitOut : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} {WitMid : Fin (n + 1) → Type}
    (kSF : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (i : pSpec.ChallengeIdx) (stmtIn : StmtIn)
    (transcript : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i) : Prop :=
  ∃ witMid : WitMid i.1.succ,
    ¬ kSF i.1.castSucc stmtIn transcript
      (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
    kSF i.1.succ stmtIn (transcript.concat challenge) witMid

end GenericLogic

section SingleIteratedSteps
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context
section FoldStep

/-- The Logic Instance for the i-th round of Binary Folding. -/
def foldStepLogic (i : Fin ℓ) :
    ReductionLogicStep
      -- In/Out Types
      (Statement (L := L) Context i.castSucc)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      -- Protocol Spec
      (pSpecFold (L := L))
      where

  -- 1. Relations (using strict relations for completeness)
  completeness_relIn := fun ((s, o), w) =>
    ((s, o), w) ∈ strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i.castSucc (mp := mp)
  completeness_relOut := fun ((s, o), w) =>
    ((s, o), w) ∈ strictFoldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i (mp := mp)

  -- 2. Verifier Logic (Using extracted kernels)
  verifierCheck := fun s t =>
    foldVerifierCheck i s (𝓑 := 𝓑) (t.messages ⟨0, rfl⟩)

  verifierOut := fun s t =>
    foldVerifierStmtOut i s (t.messages ⟨0, rfl⟩) (t.challenges ⟨1, rfl⟩)

  -- 2b. Oracle Embedding (must match foldOracleVerifier)
  embed := ⟨fun j => by
    if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
      exact Sum.inl ⟨j.val, by omega⟩
    else omega -- never happens
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Sum.inl.injEq] at h_ab_eq
    exact h_ab_eq
  ⟩
  hEq := fun oracleIdx => by
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Function.Embedding.coeFn_mk]

  -- 3. Honest Prover Logic (Constructing the transcript)
  --    "Given input and the future challenge, what would the transcript look like?"
  honestProverTranscript := fun _stmtIn witIn _oStmtIn chal =>
    let msg : ↥L⦃≤ 2⦄[X] := foldProverComputeMsg (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i witIn
    FullTranscript.mk2 msg (chal ⟨1, rfl⟩)

  -- 4. Prover Output (State Update)
  proverOut := fun s w o t =>
    let h_i : (pSpecFold (L := L)).«Type» 0 := t ⟨0, by omega⟩
    let r_i' : (pSpecFold (L := L)).«Type» 1 := t ⟨1, by omega⟩
    getFoldProverFinalOutput 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
      (s, o, w, h_i, r_i')

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [SampleableType L] in
/-- The Main Lemma: Binary Folding satisfies Strong Completeness.

This proves that for any valid input satisfying `roundRelation`, the honest prover-verifier
interaction correctly computes the sumcheck polynomial and updates the witness through folding.

**Proof Structure:**
- Verifier check: Uses `projectToNextSumcheckPoly_sum_eq`.
- Output relation: Uses `badEventExistsProp_succ_preserved` for bad events, and preservation lemmas
  (e.g., `witnessStructuralInvariant_succ_preserved`) otherwise.
- Agreement: Prover and verifier agree on output statements and oracles. -/
lemma foldStep_is_logic_complete (i : Fin ℓ) :
    (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  -- Extract properties from h_relIn (strictRoundRelation)
  simp only [foldStepLogic, strictRoundRelation, strictRoundRelationProp,
    Set.mem_setOf_eq] at h_relIn

  -- We'll need sumcheck consistency for Fact 1, so extract it from either branch
  have h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H
    := h_relIn.1

  let h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    -- Fact 1: Verifier check passes (sumcheck condition)
    simp only [step, foldStepLogic, foldVerifierCheck, foldProverComputeMsg]
    rw [h_sumcheck_cons]
    apply Sumcheck.Structured.getSumcheckRoundPoly_sum_eq

  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    -- Fact 3: Prover and verifier statements agree
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, foldStepLogic]; simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Fin.val_succ]
    rfl

  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
    simp only [step, foldStepLogic]
    -- Fact 4: Prover and verifier oracle statements agree
    funext j
    simp only [Prod.mk.eta, Fin.isValue, MessageIdx, Fin.is_lt, ↓reduceDIte,
      Fin.eta, Fin.zero_eta, Fin.mk_one, Function.Embedding.coeFn_mk, Sum.inl.injEq,
      OracleVerifier.mkVerifierOStmtOut_inl, cast_eq]

  -- Key fact: Oracle statements are unchanged in the fold step
  -- (all oracle indices map via Sum.inl in the embedding)
  have h_verifierOStmtOut_eq : verifierOStmtOut = oStmtIn := by
    rw [← hOStmtOut_eq]
    simp only [proverOStmtOut, proverOutput, step, foldStepLogic]

  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- Fact 2: Output relation holds (strictFoldStepRelOut)
    simp only [step, foldStepLogic, strictFoldStepRelOut, strictFoldStepRelOutProp, Set.mem_setOf_eq]
    let r_i' : L := by
      simpa [ProtocolSpec.Challenge, pSpecFold] using challenges ⟨⟨1, by omega⟩, by rfl⟩
    simp only [Fin.val_succ]
    constructor
    · -- Part 2.1: sumcheck consistency
      unfold sumcheckConsistencyProp
      dsimp only [verifierStmtOut, proverWitOut, proverOutput]
      simp only [step, foldStepLogic, foldVerifierStmtOut, getFoldProverFinalOutput, transcript]
      apply Sumcheck.Structured.projectToNextSumcheckPoly_sum_eq
    · -- Part 2.2: strictOracleWitnessConsistency
      simp only [Fin.coe_castSucc] at h_relIn
      have h_oracleWitConsistency_In := h_relIn.2
      rw [h_verifierOStmtOut_eq];
      dsimp only [strictOracleWitnessConsistency] at h_oracleWitConsistency_In ⊢
      -- Extract the three components from the input
      obtain ⟨h_wit_struct_In, h_oracle_folding_In⟩ :=
        h_oracleWitConsistency_In
      -- Now prove each component for the output
      refine ⟨?_, ?_⟩
      · -- Component 1: witnessStructuralInvariant
        unfold witnessStructuralInvariant
        obtain ⟨h_H_In, h_f_In⟩ := h_wit_struct_In
        dsimp only [Fin.val_succ, proverWitOut, proverOutput, step,
          foldStepLogic, verifierStmtOut]
        constructor
        · rw [h_H_In]
          exact Sumcheck.Structured.projectToNextSumcheckPoly_eq_projectToMidSumcheckPoly_succ
            (L := L) (ℓ := ℓ) (t := witIn.t) (m := mp.multpoly stmtIn.ctx) (i := i)
            (challenges := stmtIn.challenges) (r_i' := r_i')
        · conv_lhs =>
            rw [h_f_In]
            rw [←getMidCodewords_succ]
          rfl
      · -- Component 2: strictOracleFoldingConsistencyProp
        have h_oracleIdx_eq : (OracleFrontierIndex.mkFromStmtIdx i.castSucc).val
          = (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i).val := by rfl
        have h_challenges_eq :
            Fin.tail verifierStmtOut.challenges = stmtIn.challenges := by
          dsimp only [foldStepLogic, verifierStmtOut, step]
          rfl
        rw! (castMode := .all) [h_oracleIdx_eq] at h_oracle_folding_In
        simp at h_oracle_folding_In ⊢
        rw! (castMode := .all) [h_challenges_eq]
        exact h_oracle_folding_In

  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end FoldStep

section CommitStep

def commitStepLogic_embedFn (i : Fin ℓ) :
    (Fin (toOutCodewordsCount ℓ ϑ i.succ)) → Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕ (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).MessageIdx :=
  fun j => by
  if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
    exact Sum.inl ⟨j.val, hj⟩
  else
    exact Sum.inr ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩

def commitStepLogic_embed_inj (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    Function.Injective (commitStepLogic_embedFn  𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i) := by
  intro a b h_ab_eq
  simp only [MessageIdx, commitStepLogic_embedFn, Fin.isValue] at h_ab_eq
  split_ifs at h_ab_eq with h_ab_eq_l h_ab_eq_r
  · simp at h_ab_eq; apply Fin.eq_of_val_eq; exact h_ab_eq
  · have ha_lt : a < toOutCodewordsCount ℓ ϑ i.succ := by omega
    have hb_lt : b < toOutCodewordsCount ℓ ϑ i.succ := by omega
    conv_rhs at ha_lt => rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    conv_rhs at hb_lt => rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    simp only [hCR, ↓reduceIte] at ha_lt hb_lt
    have h_a : a = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
    have h_b : b = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
    omega

/- the CommitStep is a 1-message oracle reduction to place the conditional oracle message -/
def commitStepLogic_embed (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    Fin (toOutCodewordsCount ℓ ϑ i.succ) ↪ Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕ (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).MessageIdx := ⟨
  commitStepLogic_embedFn  𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i
  , commitStepLogic_embed_inj 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i hCR
  ⟩

-- ⊢ ∀ (i_1 : Fin (toOutCodewordsCount ℓ ϑ i.succ)),
--   OracleStatement 𝔽q β ϑ i.succ i_1 =
--     match (commitStepLogic_embed 𝔽q β i hCR) i_1 with
--     match (commitStepLogic_embed 𝔽q β ϑ i hCR) i_1 with
--     | Sum.inl j => OracleStatement 𝔽q β ϑ i.castSucc j
--     | Sum.inr j => (pSpecCommit 𝔽q β i).Message j

def commitStepHEq (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    hEq (OracleIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (OracleOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (ιₒᵢ := Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) (ιₒₒ := Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (pSpec := pSpecCommit 𝔽q β i) (embed := commitStepLogic_embed 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i hCR)
  := fun oracleIdx => by
    unfold OracleStatement pSpecCommit commitStepLogic_embed commitStepLogic_embedFn
    simp only [MessageIdx, Fin.isValue, Function.Embedding.coeFn_mk, Message,
      Matrix.cons_val_fin_one]
    by_cases hlt : oracleIdx.val < toOutCodewordsCount ℓ ϑ i.castSucc
    · simp only [hlt, ↓reduceDIte]
    · simp only [hlt, ↓reduceDIte, Fin.isValue]
      have hOracleIdx_lt : oracleIdx.val < toOutCodewordsCount ℓ ϑ i.succ := by omega
      simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hCR, ↓reduceIte] at hOracleIdx_lt
      have hOracleIdx : oracleIdx = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
      simp_rw [hOracleIdx]
      have h := toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ (i := i) (hCR := hCR)
      unfold OracleFunction
      congr 1; congr 1
      funext x
      congr 1; congr 1
      simp only [Fin.mk.injEq]; rw [h]

/-- The Logic Instance for the commit step.
This is a trivial 1-message protocol where the prover just sends an oracle and the verifier
accepts it. -/
def commitStepLogic (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    ReductionLogicStep
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where

  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictFoldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i

  completeness_relOut := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ

  -- No verification needed - just accept
  verifierCheck := fun _ _ => True

  -- Statement doesn't change
  verifierOut := fun stmt _ => stmt

  -- Oracle embedding: new oracle index maps to the message
  embed := commitStepLogic_embed 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR

  hEq := (commitStepHEq 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)

  -- No challenges in 1-message protocol, so transcript is just the message
  honestProverTranscript := fun _stmt wit _oStmt _challenges =>
    fun ⟨0, _⟩ => wit.f

  -- Prover output: statement unchanged, oracle extended with new function
  proverOut := fun stmt wit oStmtIn transcript =>
    let oStmtOut :=
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn (newOracleFn := wit.f)
      -- OracleVerifier.mkVerifierOStmtOut
      -- (embed := (commitStepLogic_embed 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR))
      -- (hEq := (commitStepHEq 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR))
      -- oStmtIn transcript
    ((stmt, oStmtOut), wit)

universe u v
/-- Applying a casted nondependent function is the same as casting the argument backward first. -/
theorem cast_fun_eq_fun_cast_arg {α β : Type u} {γ : Type v} {hαβ : α = β}
    {hfun : (α → γ) = (β → γ)} (f : α → γ) (x : β) :
    cast hfun f x = f (cast hαβ.symm x) := by
  subst hαβ
  cases hfun
  rfl

theorem cast_fun_eq_fun_cast_arg_rev {α β : Type u} {γ : Type v} {hαβ : α = β}
    {hfun : (β → γ) = (α → γ)} (f : β → γ) (x : α) :
    cast hfun f x = f (cast hαβ x) := by
  subst hαβ
  cases hfun
  rfl

theorem fun_heq_cast_arg {α β : Type u} {γ : Type v} (hαβ : α = β)
    (f : β → γ) :
    HEq (fun x : α => f (cast hαβ x)) f := by
  subst hαβ
  rfl

theorem verifier_inr_transport_heq {n : ℕ} {pSpec : ProtocolSpec n}
    {ιₛᵢ ιₛₒ : Type}
    {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
    (embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx)
    (hTypes : hEq (OracleIn := OStmtIn) (OracleOut := OStmtOut)
      (pSpec := pSpec) (embed := embed))
    {idx : ιₛₒ} {msgIdx : pSpec.MessageIdx}
    (h : embed idx = Sum.inr msgIdx) (x : pSpec.Message msgIdx) :
    HEq ((hTypes idx ▸ h ▸ x : OStmtOut idx)) x := by
  refine (eqRec_heq (φ := fun T : Type => T) (hTypes idx).symm (h ▸ x)).trans ?_
  rw [eqRec_eq_cast]
  exact cast_heq _ x

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Old-oracle branch of the commit-step `snoc_oracle`/verifier-output agreement.
For old frontier indices, both constructions route to the same input oracle. -/
lemma snoc_oracle_eq_mkVerifierOStmtOut_commitStep_old
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩))
    (transcript : FullTranscript (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc) :
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn newOracle j =
      OracleVerifier.mkVerifierOStmtOut (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed
        (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑) i hCR).hEq oStmtIn transcript j := by
  dsimp only [snoc_oracle]
  simp only [hCR, ↓reduceDIte]
  have h_embed : (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed j =
      Sum.inl ⟨j.val, hj⟩ := by
    simp only [commitStepLogic, commitStepLogic_embed, Function.Embedding.coeFn_mk,
      commitStepLogic_embedFn, hj, dif_pos]
  rw [OracleVerifier.mkVerifierOStmtOut_inl _ _ _ _ _ _ h_embed]
  simp only [hj, dif_pos, eqRec_eq_cast, cast_cast]
  apply eq_of_heq
  refine HEq.trans ?_ (cast_heq _ (oStmtIn ⟨j.val, hj⟩)).symm
  have hidx : (⟨j.val, by omega⟩ :
      Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) = ⟨j.val, hj⟩ := by
    ext
    rfl
  cases hidx
  rfl

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- New-oracle branch of the commit-step `snoc_oracle`/verifier-output agreement.
The `snoc_oracle` side is now a direct cast of the transcript message oracle. -/
lemma snoc_oracle_eq_mkVerifierOStmtOut_commitStep_new
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩))
    (transcript : FullTranscript (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (h_transcript_eq : transcript.messages ⟨0, rfl⟩ = newOracle)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : ¬ j.val < toOutCodewordsCount ℓ ϑ i.castSucc) :
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn newOracle j =
      OracleVerifier.mkVerifierOStmtOut (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed
        (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑) i hCR).hEq oStmtIn transcript j := by
  have h_embed : (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed j =
      Sum.inr ⟨0, rfl⟩ := by
    simp only [commitStepLogic, commitStepLogic_embed, Function.Embedding.coeFn_mk,
      commitStepLogic_embedFn, hj, dif_neg, not_false_eq_true]
    rfl
  rw [OracleVerifier.mkVerifierOStmtOut_inr _ _ _ _ _ _ h_embed]
  apply eq_of_heq
  have h_snoc :
      HEq (snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn newOracle j)
        newOracle := by
    exact snoc_oracle_new_heq_of_commit 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by rfl)
      (i := i) hCR oStmtIn newOracle j hj
  have h_msg : HEq newOracle (transcript.messages ⟨0, rfl⟩) :=
    heq_of_eq h_transcript_eq.symm
  have h_transport :
      HEq ((((commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).hEq j) ▸
          h_embed ▸ transcript.messages ⟨0, rfl⟩ :
            OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j))
        (transcript.messages ⟨0, rfl⟩) := by
    exact verifier_inr_transport_heq
      (embed := (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed)
      (hTypes := (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).hEq)
      h_embed (transcript.messages ⟨0, rfl⟩)
  exact h_snoc.trans (h_msg.trans h_transport.symm)

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Helper lemma: snoc_oracle matches mkVerifierOStmtOut for commit steps.

This proves that when we add a new oracle via `snoc_oracle`, the result matches what the verifier
computes using `OracleVerifier.mkVerifierOStmtOut` with the commit step's embedding.

The key insight:
- For indices `j < toOutCodewordsCount ℓ ϑ i.castSucc`: embed maps to `Sum.inl j` (old oracle)
- For index `j = toOutCodewordsCount ℓ ϑ i.castSucc`: embed maps to `Sum.inr 0`
  (new oracle from message)
-/
lemma snoc_oracle_eq_mkVerifierOStmtOut_commitStep
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩))
    (transcript : FullTranscript (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (h_transcript_eq : transcript.messages ⟨0, rfl⟩ = newOracle) :
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn newOracle =
    OracleVerifier.mkVerifierOStmtOut (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed
      (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i hCR).hEq oStmtIn transcript := by
  funext j
  by_cases hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · exact snoc_oracle_eq_mkVerifierOStmtOut_commitStep_old 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      i hCR oStmtIn newOracle transcript j hj
  · exact snoc_oracle_eq_mkVerifierOStmtOut_commitStep_new 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      i hCR oStmtIn newOracle transcript h_transcript_eq j hj

/-- Oracle folding consistency is preserved when adding a new oracle in a commit step.

This lemma shows that if `oStmtIn` satisfies `oracleFoldingConsistencyProp` at round `i.castSucc`,
then `oStmtOut` (constructed via `mkVerifierOStmtOut` with commit step's embed/hEq) satisfies it
at `i.succ`.

**Key insight**: In a commit step:
- The oracle frontier index values are equal:
  `(mkFromStmtIdxCastSuccOfSucc i).val = (mkFromStmtIdx i.succ).val`
- The challenges don't change (commit step has no verifier challenges)
- Therefore oracle folding consistency trivially carries over
-/
-- Arithmetic bound lemmas
lemma commitStep_j_bound (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i.succ) :
    j.val < toOutCodewordsCount ℓ ϑ i.castSucc := by
  have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  conv_rhs at hj => rw [h_count_succ]
  omega

lemma commitStep_j_is_last (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i.succ)
    (hj_next : ¬ j.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc) :
    j.val + 1 = toOutCodewordsCount ℓ ϑ i.castSucc := by
  have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  conv_rhs at hj => rw [h_count_succ]
  omega

omit [SampleableType L] in
lemma strictOracleFoldingConsistency_commitStep
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (stmtIn : Statement (L := L) Context i.succ)
    (witIn : Witness 𝔽q β i.succ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
    (challenges : (pSpecCommit 𝔽q β i).Challenges)
    (h_wit_struct_In : witnessStructuralInvariant 𝔽q β (mp := mp) stmtIn witIn)
    (h_oracle_folding_In : strictOracleFoldingConsistencyProp 𝔽q β (t := witIn.t) (i := i.castSucc)
      (challenges := Fin.rtake (m := i)
        (v := stmtIn.challenges) (h := by
          simp only [Fin.val_succ, le_add_iff_nonneg_right, zero_le]))
      (oStmt := oStmtIn)) :
    let step := (commitStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i (hCR := hCR))
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    let verifierStmtOut := step.verifierOut stmtIn transcript
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
      oStmtIn transcript
    strictOracleFoldingConsistencyProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i.succ)
      (challenges := Fin.rtake (m := i.val + 1)
        (v := verifierStmtOut.challenges) (h := by simp only [Fin.val_succ, le_refl]))
      (oStmt := verifierOStmtOut) (t := witIn.t)
    := by
  let step := (commitStepLogic 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i (hCR := hCR))
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let P₀ : L⦃< 2 ^ ℓ⦄[X] :=
    polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => witIn.t.val.eval (statementOrderBitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := 0) (P := P₀)

  have h_wit_f_eq : witIn.f = getMidCodewords 𝔽q β witIn.t stmtIn.challenges :=
    h_wit_struct_In.2
  have h_oracle_folding_tail :
      strictOracleFoldingConsistencyProp 𝔽q β (t := witIn.t) (i := i.castSucc)
        (challenges := Fin.tail stmtIn.challenges) (oStmt := oStmtIn) := by
    convert h_oracle_folding_In using 2
    exact (show Fin.rtake (n := i.val + 1) (α := fun _ : Fin (i.val + 1) => L)
        (m := i.val) (v := stmtIn.challenges) (h := by omega) =
        Fin.tail stmtIn.challenges by
      rw [← Fin.cons_self_tail stmtIn.challenges]
      exact fin_rtake_cons_const (stmtIn.challenges ⟨0, Nat.succ_pos i.val⟩)
        (Fin.tail stmtIn.challenges)).symm
  have h_OStmtOut_eq : verifierOStmtOut = snoc_oracle 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl)
      oStmtIn (newOracleFn := witIn.f) := by
    rw [snoc_oracle_eq_mkVerifierOStmtOut_commitStep 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp)
      i hCR oStmtIn witIn.f transcript (by rfl)]
  have h_challenges_eq : stmtIn.challenges = verifierStmtOut.challenges := by rfl
  have h_rtake_full (h : i.val + 1 ≤ i.val + 1) :
      Fin.rtake (n := i.val + 1) (α := fun _ : Fin (i.val + 1) => L)
        (m := i.val + 1) (v := stmtIn.challenges) (h := h) =
      stmtIn.challenges := by
    simpa using (Fin.rtake_self' (v := stmtIn.challenges))

  simp only [strictOracleFoldingConsistencyProp]
  intro j
  have h_count_succ :
      toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  have h_j_bound : j.val < toOutCodewordsCount ℓ ϑ i.succ := j.isLt
  by_cases hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · have h_verifier_eq_old : verifierOStmtOut j = oStmtIn ⟨j.val, hj⟩ := by
      rw [h_OStmtOut_eq]
      dsimp only [snoc_oracle]
      simp only [hj, ↓reduceDIte]
    change verifierOStmtOut j = _
    rw [h_verifier_eq_old]
    have h_old_steps_bound : j.val * ϑ ≤ i.val := by
      have hle := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i.castSucc ⟨j.val, hj⟩
      simpa only [Fin.val_castSucc, i.isLt, ↓reduceIte] using hle
    have h_chal_tail :
        getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := j.val * ϑ) i.castSucc
            (Fin.tail stmtIn.challenges) 0 (h := by
              simpa only [zero_add, Fin.val_castSucc] using h_old_steps_bound) =
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := j.val * ϑ) i.succ
            stmtIn.challenges 0 (h := by
              simp only [zero_add, Fin.val_succ]
              omega) := by
      simpa only [zero_add] using
        (getFoldingChallenges_tail_castSucc_eq_of_le (r := r) (𝓡 := 𝓡)
          (ϑ := j.val * ϑ) i stmtIn.challenges 0
          (by simpa only [zero_add, Fin.val_castSucc] using h_old_steps_bound)
          (by
            simp only [zero_add, Fin.val_succ]
            omega))
    have h_old_eq := h_oracle_folding_tail ⟨j.val, hj⟩
    rw [← h_challenges_eq]
    have h_chal_full :
        getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := j.val * ϑ) i.succ
            (Fin.rtake (n := i.val + 1) (α := fun _ : Fin (i.val + 1) => L)
              (m := i.val + 1) (v := stmtIn.challenges)
              (h := by exact le_rfl)) 0 (h := by
              simp only [zero_add, Fin.val_succ]
              omega) =
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := j.val * ϑ) i.succ
            stmtIn.challenges 0 (h := by
              simp only [zero_add, Fin.val_succ]
              omega) := by
      exact getFoldingChallenges_rtake_self_succ (r := r) (𝓡 := 𝓡)
        (ϑ := j.val * ϑ) (i := i) (challenges := stmtIn.challenges) (k := 0)
        (h := by
          simp only [zero_add, Fin.val_succ]
          omega)
        (h' := by
          simp only [zero_add, Fin.val_succ]
          omega)
        (hr := by exact le_rfl)
    have h_chal_eq :
        getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := j.val * ϑ) i.castSucc
            (Fin.tail stmtIn.challenges) 0 (h := by
              simpa only [zero_add, Fin.val_castSucc] using h_old_steps_bound) =
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := j.val * ϑ) i.succ
            (Fin.rtake (n := i.val + 1) (α := fun _ : Fin (i.val + 1) => L)
              (m := i.val + 1) (v := stmtIn.challenges)
              (h := by exact le_rfl)) 0 (h := by
              simp only [zero_add, Fin.val_succ]
              omega) :=
      h_chal_tail.trans h_chal_full.symm
    exact h_old_eq.trans (by
      rw [h_chal_eq]
      simp only [Fin.val_mk]
      apply iterated_fold_proof_irrel)
  · change verifierOStmtOut j = _
    rw [h_OStmtOut_eq]
    dsimp only [snoc_oracle]
    simp only [hj, ↓reduceDIte, hCR]
    have h_j_eq : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
    have h_domain_idx_eq : (oraclePositionToDomainIndex (positionIdx := j)).val = i.val + 1 := by
      simp only [h_j_eq]
      exact toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ i hCR
    funext x
    dsimp only [Fin.val_last, getMidCodewords] at h_wit_f_eq
    rw [h_wit_f_eq]
    rw [← h_challenges_eq]
    have h_new_steps_eq : j.val * ϑ = i.val + 1 := by
      simpa only [oraclePositionToDomainIndex, Fin.val_mk] using h_domain_idx_eq

    have h_cast_elim := iterated_fold_congr_dest_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := i.succ)
      (destIdx := ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩)
      (destIdx' := ⟨i.succ, by simp only [Fin.val_succ]; omega⟩)
      (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ, zero_add]
        exact h_domain_idx_eq)
      (h_destIdx_le := by simp only [oracle_index_le_ℓ])
      (h_destIdx_eq_destIdx' := by
        simp only [Fin.val_succ, Fin.mk.injEq]
        exact h_domain_idx_eq)
      (f := f₀)
      (r_challenges := foldOrderChallenges stmtIn.challenges)
    dsimp only [f₀, P₀] at h_cast_elim
    unfold polyToOracleFunc at h_cast_elim
    rw [cast_fun_eq_fun_cast_arg (hαβ := by
      apply congrArg (fun idx => (sDomain 𝔽q β h_ℓ_add_R_rate idx : Type))
      exact Fin.eq_of_val_eq h_new_steps_eq.symm)]
    have h_first := (h_cast_elim x).symm
    refine h_first.trans ?_
    unfold getFoldingChallenges

    have h_cast_elim2 := iterated_fold_congr_steps_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := i.succ) (steps' := j.val * ϑ)
      (destIdx := ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩)
      (h_steps_eq_steps' := by exact h_domain_idx_eq.symm)
      (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ, zero_add]
        exact h_domain_idx_eq)
      (h_destIdx_le := by simp only [oracle_index_le_ℓ])
      (f := f₀) (r_challenges := foldOrderChallenges stmtIn.challenges)
    dsimp only [f₀, P₀] at h_cast_elim2
    unfold polyToOracleFunc at h_cast_elim2
    rw [h_cast_elim2]
    dsimp only [Fin.val_succ, Fin.take_apply, Fin.castLE_refl]
    congr 1
    dsimp only [oraclePositionToDomainIndex] at h_domain_idx_eq
    have h_challenges_eq_take :
        (fun cIdx : Fin (j.val * ϑ) =>
          foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.succ)
            stmtIn.challenges ⟨cIdx.val, by
          simpa only [Fin.val_succ, h_domain_idx_eq] using cIdx.isLt⟩) =
        (fun cIdx : Fin (j.val * ϑ) =>
          foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.succ)
          (Fin.rtake (n := i.val + 1) (α := fun _ : Fin (i.val + 1) => L)
            (m := i.val + 1) (v := stmtIn.challenges)
            (h := by exact le_rfl)) ⟨0 + cIdx.val, by
          simpa only [zero_add, Fin.val_succ, h_domain_idx_eq] using cIdx.isLt⟩) := by
      rw [h_rtake_full]
      funext cId
      simp only [Fin.val_succ, zero_add]
    simpa using h_challenges_eq_take

omit [SampleableType L] in
/-- Commit step logic is strongly complete.
The key insight is that the commit step just extends the oracle without changing the statement,
and the verifier always accepts (no verification check). -/
lemma commitStep_is_logic_complete (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i (hCR := hCR)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (commitStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i (hCR := hCR))
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2

  -- Extract properties from h_relIn (strictFoldStepRelOut)
  dsimp only [commitStepLogic, strictFoldStepRelOut, strictFoldStepRelOutProp,
    strictRoundRelation, strictRoundRelationProp, Set.mem_setOf_eq] at h_relIn
  dsimp only [strictFoldStepRelOutProp, strictRoundRelationProp, Fin.val_succ] at h_relIn

  -- We'll need sumcheck consistency for Fact 1, so extract it from either branch
  have h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H
    := h_relIn.1
  let h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    dsimp only [commitStepLogic, Prod.mk.eta, step]

  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    dsimp only [step, commitStepLogic]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    -- clear_value h_VCheck_passed
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
    conv_lhs => dsimp only [step, commitStepLogic]
    dsimp only [transcript, step]
    rw [snoc_oracle_eq_mkVerifierOStmtOut_commitStep 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp)
      i hCR oStmtIn witIn.f transcript (by rfl)]

  have h_first_oracle_eq : (getFirstOracle 𝔽q β verifierOStmtOut)
    = (getFirstOracle 𝔽q β oStmtIn) := by
    rw [← hOStmtOut_eq]
    dsimp only [proverOStmtOut, proverOutput, step, commitStepLogic]
    exact getFirstOracle_snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (by rfl) oStmtIn _

  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- Fact 2: Output relation holds (strictRoundRelation)
    dsimp only [step, commitStepLogic, strictRoundRelation, strictRoundRelationProp,
      Set.mem_setOf_eq]
    simp only [Fin.val_succ]
    constructor
    · -- Part 2.1: sumcheck consistency
      exact h_sumcheck_cons
    · -- Part 2.2: strictOracleWitnessConsistency
      have h_strictOracleWitConsistency_In := h_relIn.2
      dsimp only [strictOracleWitnessConsistency] at h_strictOracleWitConsistency_In ⊢
      -- Extract the two components from the input
      obtain ⟨h_wit_struct_In, h_strict_oracle_folding_In⟩ := h_strictOracleWitConsistency_In
      -- Now prove each component for the output
      refine ⟨?_, ?_⟩
      · -- Component 1: witnessStructuralInvariant
        exact h_wit_struct_In
      · -- Component 2: strictOracleFoldingConsistencyProp
        exact strictOracleFoldingConsistency_commitStep 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (witIn := witIn)
          (stmtIn := stmtIn) (hCR := hCR) (h_wit_struct_In := h_wit_struct_In)
          (h_oracle_folding_In := h_strict_oracle_folding_In) (challenges := challenges)

  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end CommitStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step

This section implements the final sumcheck step that sends the constant `c := f^(ℓ)(0, ..., 0)`
from the prover to the verifier. This step completes the sumcheck verification by ensuring
the final constant is consistent with the folding chain.

The step consists of :
- P → V : constant `c := f^(ℓ)(0, ..., 0)`
- V verifies : `s_ℓ = eqTilde(r, r') * c`
=> `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})` and `f^(ℓ)(0, ..., 0)`

**Key Mathematical Insight** : At round ℓ, we have :
- `P^(ℓ)(X) = Σ_{w ∈ B_0} H_ℓ(w) · X_w^(ℓ)(X) = H_ℓ(0) · X_0^(ℓ)(X) = H_ℓ(0)`
- Since `H_ℓ(X)` is constant (zero-variate): `H_ℓ(X) = t(r'_0, ..., r'_{ℓ-1})`
- Therefore : `P^(ℓ)(X) = t(r'_0, ..., r'_{ℓ-1})` (constant polynomial)
- And `s_ℓ = ∑_{w ∈ B_0} t(r'_0, ..., r'_{ℓ-1}) = t(r'_0, ..., r'_{ℓ-1})`
-/

/-- Oracle interface instance for the final sumcheck step message -/
instance : ∀ j, OracleInterface ((pSpecFinalSumcheckStep (L := L)).Message j) := fun j =>
  match j with
  | ⟨0, _⟩ => OracleInterface.instDefault

/-- The Logic Instance for the final sumcheck step.
This is a 1-message protocol where the prover sends the final constant c. -/
def finalSumcheckStepLogic :
    ReductionLogicStep
      -- In/Out Types
      (Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
      (Unit)
      -- Protocol Spec
      (pSpecFinalSumcheckStep (L := L))
      where

  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ)

  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    -- For strict relations, we need t from the input witness
    -- In completeness proofs, this will be extracted from h_relIn via
    -- strictOracleWitnessConsistency
      ((stmtOut, oStmtOut), witOut) ∈ strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

  verifierCheck := fun stmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let eq_tilde_eval := eqTilde (r := stmtIn.ctx.t_eval_point) (r' := stmtIn.challenges)
    stmtIn.sumcheck_target = eq_tilde_eval * c

  verifierOut := fun stmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }

  honestProverTranscript := fun _stmtIn witIn _oStmtIn _chal =>
    -- The honest prover sends c = f^(ℓ)(0, ..., 0)
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩
    FullTranscript.mk1 c

  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
    ((stmtOut, oStmtIn), ())

  embed := ⟨fun j => by
    have h_lt : j.val < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) := j.isLt
    exact Sum.inl ⟨j.val, by omega⟩
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Fin.eta, Sum.inl.injEq] at h_ab_eq
    exact h_ab_eq
  ⟩
  hEq := fun oracleIdx => by simp only [Fin.eta]

omit [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L] [NeZero ℓ] in
/-- At `Fin.last ℓ`, sumcheck consistency is the single empty-variable evaluation. -/
lemma sumcheckConsistency_at_last_simplifies
    (target : L) (H : L⦃≤ 2⦄[X Fin (ℓ - Fin.last ℓ)])
    (h_cons : sumcheckConsistencyProp (𝓑 := 𝓑) target H) :
    target = H.val.eval (fun _ => (0 : L)) := by
  simp only [Fin.val_last] at H h_cons ⊢
  simp only [sumcheckConsistencyProp] at h_cons
  haveI : IsEmpty (Fin 0) := Fin.isEmpty
  rw [Finset.sum_eq_single (a := fun _ => 0)
    (h₀ := fun b _ hb_ne => by
      exfalso
      apply hb_ne
      funext i
      simp only [tsub_self] at i
      exact i.elim0)
    (h₁ := fun h_not_mem => by
      exfalso
      apply h_not_mem
      simp only [Fintype.mem_piFinset]
      intro i
      simp only [tsub_self] at i
      exact i.elim0)] at h_cons
  exact h_cons

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- The final sumcheck verifier check follows from sumcheck consistency, witness structure, and the
final codeword evaluation identity. -/
lemma finalSumcheckStep_verifierCheck_passed_of_finalCodeword
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H)
    (h_wit_struct : witnessStructuralInvariant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := BBF_SumcheckMultiplierParam) (stmt := stmtIn) (wit := witIn))
    (h_final_codeword :
      witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges) :
    (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).verifierCheck stmtIn
        ((finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑)).honestProverTranscript stmtIn witIn oStmtIn challenges) := by
  have h_target_eq_H_eval :
      stmtIn.sumcheck_target = witIn.H.val.eval (fun _ => (0 : L)) :=
    sumcheckConsistency_at_last_simplifies (L := L) (ℓ := ℓ) (𝓑 := 𝓑)
      stmtIn.sumcheck_target witIn.H h_sumcheck_cons
  have h_proj_eval :
      (projectToMidSumcheckPoly ℓ witIn.t
        (m := (BBF_SumcheckMultiplierParam (L := L) (ℓ := ℓ)).multpoly stmtIn.ctx)
        (Fin.last ℓ) stmtIn.challenges).val.eval (fun _ => (0 : L)) =
      ((BBF_SumcheckMultiplierParam (L := L) (ℓ := ℓ)).multpoly stmtIn.ctx).val.eval
        stmtIn.challenges * witIn.t.val.eval stmtIn.challenges := by
    apply Sumcheck.Structured.projectToMidSumcheckPoly_at_last_eval
  have h_eq : stmtIn.sumcheck_target =
      eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
        witIn.f ⟨0, by simp only [zero_mem]⟩ := by
    calc
      stmtIn.sumcheck_target
          = witIn.H.val.eval (fun _ => (0 : L)) := h_target_eq_H_eval
      _ = (projectToMidSumcheckPoly ℓ witIn.t
            (m := (BBF_SumcheckMultiplierParam (L := L) (ℓ := ℓ)).multpoly stmtIn.ctx)
            (Fin.last ℓ) stmtIn.challenges).val.eval (fun _ => (0 : L)) := by
            rw [h_wit_struct.1]
      _ = ((BBF_SumcheckMultiplierParam (L := L) (ℓ := ℓ)).multpoly stmtIn.ctx).val.eval
            stmtIn.challenges * witIn.t.val.eval stmtIn.challenges := h_proj_eval
      _ = eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
            witIn.t.val.eval stmtIn.challenges := by
            rfl
      _ = eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
            witIn.f ⟨0, by simp only [zero_mem]⟩ := by
            rw [h_final_codeword]
  dsimp [finalSumcheckStepLogic, FullTranscript.mk1] at h_eq ⊢
  exact h_eq

omit [SampleableType L] in
/-- The final folded codeword value sent by the honest prover is the multilinear polynomial
evaluation at the statement challenges. -/
lemma finalSumcheckStep_final_codeword_eq_eval
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (h_wit_struct : witnessStructuralInvariant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := BBF_SumcheckMultiplierParam) (stmt := stmtIn) (wit := witIn)) :
    witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges := by
  rw [h_wit_struct.2]
  exact getMidCodewords_last_apply_eq_eval 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (t := witIn.t) (challenges := stmtIn.challenges)
    (y := ⟨0, by simp only [Fin.val_last, zero_mem]⟩)

omit [SampleableType L] in
/-- The final sumcheck verifier check follows directly from sumcheck consistency and witness
structure. -/
lemma finalSumcheckStep_verifierCheck_passed
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H)
    (h_wit_struct : witnessStructuralInvariant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := BBF_SumcheckMultiplierParam) (stmt := stmtIn) (wit := witIn)) :
    (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).verifierCheck stmtIn
        ((finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑)).honestProverTranscript stmtIn witIn oStmtIn challenges) := by
  exact finalSumcheckStep_verifierCheck_passed_of_finalCodeword 𝔽q β
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    (stmtIn := stmtIn) (witIn := witIn) (oStmtIn := oStmtIn) (challenges := challenges)
    (h_sumcheck_cons := h_sumcheck_cons) (h_wit_struct := h_wit_struct)
    (h_final_codeword := finalSumcheckStep_final_codeword_eq_eval 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
      (h_wit_struct := h_wit_struct))

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- The oracle-folding part of the final relation output is exactly the synchronized final-round
input consistency. The remaining relation-out obligation is the final constant fold. -/
lemma finalSumcheckStep_strictOracleFoldingConsistency_out
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (h_strictOracleWitConsistency_In : strictOracleWitnessConsistency 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := SumcheckBaseContext L ℓ)
      (mp := BBF_SumcheckMultiplierParam) (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)) (stmt := stmtIn)
      (wit := witIn) (oStmt := oStmtIn)) :
    strictOracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t := witIn.t) (i := Fin.last ℓ) (challenges := stmtIn.challenges)
      (oStmt := oStmtIn) := by
  simpa [strictOracleWitnessConsistency, olderStmtChallenges_self] using
    h_strictOracleWitConsistency_In.2

/-
The two direct final-step helper proofs below are stale after the challenge-order migration and have
no live callers. The public final-step completeness theorem is the explicit
`FinalSumcheckStepLogicCompleteResidual` surface below; keep these helper sketches out of the active
elaboration path until the full direct proof is restored.

omit [SampleableType L] in
/-- **Strict version**: When folding the last oracle to level `ℓ` (final sumcheck),
the iterated fold of the last oracle equals the constant function.

This is the strict version that uses exact equality instead of UDR codewords.
It is used in the final sumcheck step to show that the folding chain correctly
terminates at the constant function. -/
lemma iterated_fold_to_const_strict
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_strictOracleWitConsistency_In : strictOracleWitnessConsistency 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := SumcheckBaseContext L ℓ)
      (mp := BBF_SumcheckMultiplierParam) (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := witIn) (oStmt := oStmtIn)) :
    let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    let verifierStmtOut := step.verifierOut stmtIn transcript
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
    let lastDomainIdx := getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
    -- have h_eq := getLastOracleDomainIndex_last (ℓ := ℓ) (ϑ := ϑ)
    let k := lastDomainIdx.val
    have h_k: k = ℓ - ϑ := by
      dsimp only [k, lastDomainIdx]
      rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    let curDomainIdx : Fin r := ⟨k, by
      rw [h_k]
      omega
    ⟩
    have h_destIdx_eq: curDomainIdx.val = lastDomainIdx.val := rfl
    let f_k : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) curDomainIdx :=
      getLastOracle (h_destIdx := h_destIdx_eq) (oracleFrontierIdx := Fin.last ℓ)
        𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := verifierOStmtOut)
    let finalChallenges : Fin ϑ → L := fun cId => verifierStmtOut.challenges ⟨k + cId, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
      have h_cId : cId.val < ϑ := cId.isLt
      have h_last : (Fin.last ℓ).val = ℓ := rfl
      omega
    ⟩
    let destDomainIdx : Fin r := ⟨k + ϑ, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
      omega
    ⟩
    let folded := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curDomainIdx) (steps := ϑ) (destIdx := destDomainIdx) (h_destIdx := by rfl)
      (h_destIdx_le := by
        dsimp only [destDomainIdx, k, lastDomainIdx];
        rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
          Nat.div_mul_cancel (hdiv.out)]
        rw [Nat.sub_add_cancel (by exact Nat.le_of_dvd (h:=by
          exact Nat.pos_of_neZero ℓ) (hdiv.out))]
      ) (f := f_k)
      (r_challenges := finalChallenges)

    ∀ y, folded y = transcript.messages ⟨0, rfl⟩ := by
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  intro step transcript verifierStmtOut verifierOStmtOut
  intro lastDomainIdx k h_k curDomainIdx h_destIdx_eq f_k finalChallenges destDomainIdx folded
  let P₀: L⦃< 2 ^ ℓ⦄[X] := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => witIn.t.val.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  -- From strictOracleWitnessConsistency, we can construct strictfinalSumcheckStepFoldingStateProp
  -- which contains strictFinalConstantConsistency, giving us the desired equality
  -- Extract components from h_strictOracleWitConsistency_In
  have h_wit_struct := h_strictOracleWitConsistency_In.1
  have h_strict_oracle_folding := h_strictOracleWitConsistency_In.2
  dsimp only [Fin.val_last, OracleFrontierIndex.val_mkFromStmtIdx,
    strictOracleFoldingConsistencyProp] at h_strict_oracle_folding
  -- Construct the input for strictfinalSumcheckStepFoldingStateProp
  let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
    ctx := stmtIn.ctx,
    sumcheck_target := stmtIn.sumcheck_target,
    challenges := stmtIn.challenges,
    final_constant := transcript.messages ⟨0, rfl⟩
  }
  let c : L := transcript.messages ⟨0, rfl⟩
  have h_VOStmtOut_eq : verifierOStmtOut = oStmtIn := by rfl
  have h_challenges_eq : stmtIn.challenges = verifierStmtOut.challenges := by rfl
  have h_eq : folded = fun x => stmtOut.final_constant := by
    change folded = fun x => c
    dsimp only [folded, f_k]
    -- , getLastOracle]
    -- f_last is the iterated_fold of f₀ yielded from P₀
    have h_f_last_consistency := h_strict_oracle_folding
      (j := (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)))
    --   h_f_last_consistency : oStmtIn (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) =
    -- iterated_fold 𝔽q β 0 (↑(getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) * ϑ) ⋯ ⋯
    --   (polyToOracleFunc 𝔽q β ↑(polynomialFromNovelCoeffsF₂ 𝔽q β ℓ ⋯
    --     fun ω ↦ (MvPolynomial.eval ↑↑ω) ↑witIn.t))
    --   (getFoldingChallenges (Fin.last ℓ) (Fin.take ℓ ⋯ stmtIn.challenges) 0 ⋯)

    rw [h_VOStmtOut_eq]
    dsimp only [c, transcript, step, finalSumcheckStepLogic]
    dsimp only [FullTranscript.mk1, FullTranscript.messages]
    simp only [Fin.val_last]
    have h_wit_f_eq : witIn.f = getMidCodewords 𝔽q β witIn.t stmtIn.challenges := h_wit_struct.2
    dsimp only [Fin.val_last, getMidCodewords] at h_wit_f_eq
    conv_rhs => rw [h_wit_f_eq]; simp only
    have h_curDomainIdx_eq : curDomainIdx = ⟨ℓ - ϑ, by omega⟩ := by
      dsimp [curDomainIdx, k, lastDomainIdx]
      simp only [Fin.mk.injEq]
      rw [getLastOraclePositionIndex_last, Nat.sub_mul,
        Nat.div_mul_cancel (hdiv.out)]; simp only [one_mul]

    let res := iterated_fold_congr_source_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curDomainIdx) (i' := ⟨ℓ - ϑ, by omega⟩) (h := h_curDomainIdx_eq) (steps := ϑ)
      (destIdx := destDomainIdx)
      (h_destIdx := by rfl) (h_destIdx' := by simp only [destDomainIdx, h_k])
      (h_destIdx_le := by
        dsimp only [destDomainIdx]; rw [h_k];
        rw [Nat.sub_add_cancel (by exact Nat.le_of_dvd (h:=by
          exact Nat.pos_of_neZero ℓ) (hdiv.out))]
      ) (f := (getLastOracle 𝔽q β h_destIdx_eq oStmtIn)) (r_challenges := finalChallenges)
    rw [res]
    dsimp only [getLastOracle, finalChallenges, verifierStmtOut, step, finalSumcheckStepLogic]
    rw [h_f_last_consistency]
    simp only [Fin.take_eq_self]
    -- Extract the inner iterated_fold function
    let k_pos_idx := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    let k_steps := k_pos_idx.val * ϑ
    have h_k_steps_eq : k_steps = k := by
      dsimp only [k_steps, k_pos_idx, k, lastDomainIdx]
    -- The inner iterated_fold is already a function from domain k to L
    -- We can remove the cast wrapper since the domains match
    have h_cast_elim := iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := k_steps) (destIdx := curDomainIdx) (destIdx' := ⟨k_steps, by omega⟩)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by
        dsimp only [curDomainIdx]; simp only [h_k, tsub_le_iff_right, le_add_iff_nonneg_right,
          zero_le]; )
      (h_destIdx_eq_destIdx' := by rfl)
      (f := f₀) (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
    have h_cast_elim2 := iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := k_steps)
      (destIdx := ⟨ℓ - ϑ, by omega⟩)
      (destIdx' := curDomainIdx)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by
        dsimp only [curDomainIdx]; simp only [h_k_steps_eq, h_k, tsub_le_iff_right,
          le_add_iff_nonneg_right, zero_le]; )
      (h_destIdx_eq_destIdx' := by dsimp only [curDomainIdx]; simp only [Fin.val_last, Fin.mk.injEq]; omega)
      (f := f₀) (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))

    dsimp only [k_steps, k_pos_idx, f₀, P₀] at h_cast_elim
    dsimp only [k_steps, k_pos_idx, f₀, P₀] at h_cast_elim2
    conv_lhs =>
      simp only [←h_cast_elim]
      simp only [←h_cast_elim2]
      simp only [←fun_eta_expansion]

    have h_transitivity := iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (midIdx := ⟨ℓ - ϑ, by omega⟩) (destIdx := destDomainIdx)
      (steps₁ := k_steps) (steps₂ := ϑ)
      (h_midIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, h_k_steps_eq, h_k, zero_add])
      (h_destIdx := by
        dsimp only [destDomainIdx, k_steps, k_pos_idx];
        rw [h_k]; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff]
        rw [getLastOraclePositionIndex_last]; simp only
        rw [Nat.sub_mul]; rw [Nat.div_mul_cancel (hdiv.out)]; simp only [one_mul]
      )
      (h_destIdx_le := by
        dsimp only [destDomainIdx]
        rw [h_k]
        rw [Nat.sub_add_cancel (by exact Nat.le_of_dvd (h:=by exact Nat.pos_of_neZero ℓ) (hdiv.out))])
      (f := f₀)
      (r_challenges₁ := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
      (r_challenges₂ := finalChallenges)
    have h_finalChallenges_eq : finalChallenges = fun cId : Fin ϑ => stmtIn.challenges ⟨k + cId.val, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
      have h_cId : cId.val < ϑ := cId.isLt
      have h_last : (Fin.last ℓ).val = ℓ := rfl
      omega
    ⟩ := by rfl
    rw [h_finalChallenges_eq] at h_transitivity
    rw [h_transitivity]
    have h_steps_eq : k_steps + ϑ = ℓ := by
      dsimp only [k_steps, k_pos_idx, h_k_steps_eq, h_k]
      rw [getLastOraclePositionIndex_last];
      simp only [Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)];
      rw [Nat.sub_add_cancel (by exact Nat.le_of_dvd (h:=by exact Nat.pos_of_neZero ℓ) (hdiv.out))]

    -- Show that the concatenated challenges equal stmtIn.challenges
    have h_concat_challenges_eq : Fin.append (getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := k_steps) (Fin.last ℓ) stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
        finalChallenges = fun (cIdx : Fin (k_steps + ϑ)) => stmtIn.challenges ⟨cIdx, by simp only [Fin.val_last]; omega⟩ := by
      funext cId
      dsimp only [getFoldingChallenges, finalChallenges]
      by_cases h : cId.val < k_steps
      · -- Case 1: cId < k_steps, so it's from the first part
        simp only [Fin.val_last]
        dsimp only [Fin.append, Fin.addCases]
        simp only [h, ↓reduceDIte, getFoldingChallenges, Fin.val_last, Fin.coe_castLT, zero_add]
      · -- Case 2: cId >= k_steps, so it's from the second part
        simp only [Fin.val_last]
        dsimp only [Fin.append, Fin.addCases]
        simp [h, ↓reduceDIte, Fin.coe_subNat, Fin.coe_cast, eq_rec_constant]
        congr 1
        simp only [Fin.val_last, Fin.mk.injEq]
        rw [add_comm]; rw [←h_k_steps_eq]; omega
    dsimp only [finalChallenges] at h_concat_challenges_eq
    rw [h_challenges_eq.symm] at h_concat_challenges_eq
    simp only [h_concat_challenges_eq]
    funext y
    have h_cast_elim3 := iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := k_steps + ϑ)
      (destIdx := destDomainIdx)
      (destIdx' := ⟨Fin.last ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
      (h_destIdx_le := by dsimp only [destDomainIdx]; omega)
      (h_destIdx_eq_destIdx' := by
        dsimp only [destDomainIdx]; simp only [Fin.val_last, Fin.mk.injEq]; omega)
      (f := f₀) (r_challenges := fun (cIdx : Fin (k_steps + ϑ)) => stmtIn.challenges ⟨cIdx, by simp only [Fin.val_last]; omega⟩)
    rw [h_cast_elim3]
    have h_cast_elim4 := iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := ℓ) (steps' := k_steps + ϑ)
      (destIdx := ⟨Fin.last ℓ, by omega⟩)
      (h_steps_eq_steps' := by simp only [h_steps_eq]) (h_destIdx := by
        dsimp only [destDomainIdx]; simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          zero_add];)
      (h_destIdx_le := by simp only [Fin.val_last, le_refl]) -- simp only [h_k_steps_eq, h_k, tsub_le_iff_right,
      (f := f₀) (r_challenges := stmtIn.challenges)
    rw [←h_cast_elim4]
    set f_ℓ := iterated_fold 𝔽q β 0 ℓ (destIdx := ⟨Fin.last ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add];)
      (h_destIdx_le := by simp only [Fin.val_last, le_refl]) (f := f₀) (r_challenges := stmtIn.challenges)
    have h_eval_eq : ∀ x, f_ℓ x = f_ℓ ⟨0, by simp only [zero_mem]⟩ := by
      intro x
      apply iterated_fold_to_level_ℓ_is_constant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := witIn.t) (destIdx := ⟨Fin.last ℓ, by omega⟩) (h_destIdx := by simp only [Fin.val_last]) (challenges := stmtIn.challenges) (x := x) (y := 0)
    rw [h_eval_eq]; rfl
  rw [h_eq]
  intro y
  rfl

/-- The verifier check passes in the final sumcheck step.

**Proof structure:**
1. From `sumcheckConsistencyProp`:
   - `stmtIn.sumcheck_target = ∑ x ∈ 𝓑^ᶠ(0), witIn.H.val.eval x`
   - Since `𝓑^ᶠ(0) = {∅}`, this simplifies to `witIn.H.val.eval (fun _ => 0)`

2. From `witnessStructuralInvariant`:
   - `witIn.H = projectToMidSumcheckPoly ...`
   - Using `projectToMidSumcheckPoly_at_last`:
   - `witIn.H.val.eval (fun _ => 0) = eqTilde(...) * witIn.f ⟨0, ...⟩`

3. Combining these gives the verifier check equation. -/
lemma finalSumcheckStep_verifierCheck_passed
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H)
    (h_strictOracleWitConsistency_In : strictOracleWitnessConsistency 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := SumcheckBaseContext L ℓ)
      (mp := BBF_SumcheckMultiplierParam) (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)) (stmt := stmtIn)
      (wit := witIn) (oStmt := oStmtIn)) :
    let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges

  -- Simplify the verifier check to the equality we need to prove
  change (finalSumcheckStepLogic 𝔽q β).verifierCheck stmtIn transcript
  simp only [finalSumcheckStepLogic]
  dsimp only [sumcheckConsistencyProp] at h_sumcheck_cons

  -- Simplify the sum to a single evaluation since 𝓑^ᶠ(0) = {∅}
  rw [Finset.sum_eq_single (a := fun _ => 0) (h₀ := fun b _ hb_ne => by
    have : b = fun x ↦ 0 := by
      funext i;
      rw [Fin.val_last] at i
      simp only [tsub_self] at i; exact i.elim0
    contradiction
    ) (h₁ := fun h_not_mem => by
      exfalso; apply h_not_mem
      simp only [Fintype.mem_piFinset]; intro x
      rw [Fin.val_last] at x
      simp only [tsub_self] at x; exact x.elim0
    )] at h_sumcheck_cons

  have h_wit_structural_invariant := h_strictOracleWitConsistency_In.1

  have h_f_eq_getMidCodewords_t : witIn.f = getMidCodewords 𝔽q β witIn.t stmtIn.challenges :=
    h_wit_structural_invariant.2

  have h_witIn_f_0_eq_c : witIn.f ⟨0, by simp only [zero_mem]⟩ = transcript.messages ⟨0, rfl⟩ := by
    rfl
  -- NOTE: this is important
  let h_c_eq : (transcript.messages ⟨0, rfl⟩) = witIn.t.val.eval stmtIn.challenges := by
    change witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges
    -- Since `f (f_ℓ)` is `getMidCodewords` of `t`, `f = fold(f₀, r') where f₀ = fun x => t.eval x`
    dsimp only [getMidCodewords, Fin.coe_ofNat_eq_mod] at h_f_eq_getMidCodewords_t
    rw [congr_fun h_f_eq_getMidCodewords_t ⟨0, by simp only [zero_mem]⟩]
    --   ⊢ iterated_fold 𝔽q β 0 ℓ ⋯
    --   (fun x ↦ Polynomial.eval ↑x ↑(polynomialFromNovelCoeffsF₂ 𝔽q β ℓ ⋯
    --     fun ω ↦ (MvPolynomial.eval ↑↑ω) ↑witIn.t))
    --   stmtIn.challenges ⟨↑⟨0, ⋯⟩, ⋯⟩ =
    -- (MvPolynomial.eval stmtIn.challenges) ↑witIn.t
    -- have h_eq : @Fin.mk r (0 % ℓ) (isLt := by exact Nat.pos_of_ne_zero (by omega)) = 0 := by
      -- simp only [Nat.zero_mod, Fin.mk_zero']
    let coeffs := fun (ω : Fin (2 ^ (ℓ - 0))) => witIn.t.val.eval (bitsOfIndex ω)
    let res := iterated_fold_advances_evaluation_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := Fin.last ℓ) (destIdx := ⟨↑(Fin.last ℓ), by omega⟩) (h_destIdx := by
        simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
      (h_destIdx_le := by simp only; omega) (coeffs := coeffs) (r_challenges := stmtIn.challenges)
    unfold polyToOracleFunc at res
    simp only at res
    rw [intermediate_poly_P_base 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_ℓ := by omega) (coeffs := coeffs)] at res
    dsimp only [polynomialFromNovelCoeffsF₂]
    change iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ↑(Fin.last ℓ)
      (destIdx := ⟨↑(Fin.last ℓ), by omega⟩) (by simp only [Fin.val_last, Fin.coe_ofNat_eq_mod,
        Nat.zero_mod, zero_add]) (by simp only; omega)
        (fun x ↦
          Polynomial.eval (↑x) (polynomialFromNovelCoeffs 𝔽q β ℓ (h_ℓ := by omega) coeffs))
        stmtIn.challenges ⟨0, by simp only [Fin.val_last, zero_mem]⟩ =
      (MvPolynomial.eval stmtIn.challenges) (witIn.t.val)
    rw [res]
    --   (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨0 % ℓ + ℓ, ⋯⟩ fun j ↦
    --     ∑ x, multilinearWeight stmtIn.challenges x * coeffs ⟨↑j * 2 ^ ℓ + ↑x, ⋯⟩) =
    -- (MvPolynomial.eval stmtIn.challenges) ↑witIn.t
    dsimp only [intermediateEvaluationPoly]
    -- have h_empty_univ : Fin (ℓ - (Fin.last ℓ)) = Fin 0 := by
      -- simp only [Fin.val_last, tsub_self]

    haveI : IsEmpty (Fin (ℓ - (Fin.last ℓ).val)) := by
      simp only [Fin.val_last, Nat.sub_self]
      infer_instance
    conv_lhs => -- Eliminate the intermediateNovelBasisX terms
      dsimp only [intermediateNovelBasisX]
      simp only [Finset.univ_eq_empty, Finset.prod_empty] -- eliminate the finsum over (Fin 0)
      simp only [map_mul, mul_one]
      rw [←map_sum] -- bring the `C` out of the sum
    have h_Fin_eq : Fin (2 ^ (ℓ - ↑(Fin.last ℓ))) = Fin 1 := by
      simp only [Fin.val_last, tsub_self, pow_zero]
    haveI : Unique (Fin (2 ^ (ℓ - (Fin.last ℓ).val))) := by
      simp only [Fin.val_last, Nat.sub_self, pow_zero]
      exact Fin.instUnique
    have h_default : (@default (Fin (2 ^ (ℓ - ↑(Fin.last ℓ)))) Unique.instInhabited).val = 0 := by
      have hlt := (@default (Fin (2 ^ (ℓ - ↑(Fin.last ℓ)))) Unique.instInhabited).isLt
      simp only [Fin.val_last, Nat.sub_self, pow_zero] at hlt
      exact Nat.lt_one_iff.mp hlt
    simp only [Fintype.sum_unique, Fin.val_zero, h_default]
    simp only [Fin.val_last, Nat.sub_zero, zero_mul, zero_add, Fin.eta, map_sum, map_mul]
    dsimp only [Nat.sub_zero, Fin.isValue, coeffs]
    simp only [←map_mul, ←map_sum]
    letI : NeZero (Fin.last ℓ).val := {
      out := by
        have h_ℓ_pos : ℓ > 0 := by exact Nat.pos_of_neZero ℓ
        rw [Fin.val_last]; omega
    }
    let res := multilinear_eval_eq_sum_bool_hypercube (challenges := stmtIn.challenges)
      (t := witIn.t)
    simp only [Fin.val_last] at res
    rw [res, Polynomial.eval_C];

  -- Apply `projectToMidSumcheckPoly_at_last` to connect H.eval with eqTilde * f(0)
  have h_H_eval_at_zero_eq_mul : witIn.H.val.eval (fun _ => (0 : L)) =
      eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
      (witIn.f ⟨0, by simp only [zero_mem]⟩) := by
    rw [h_wit_structural_invariant.1]
    rw [Sumcheck.Structured.projectToMidSumcheckPoly_at_last_eval]
    -- ↑witIn.t = witIn.f ⟨0, ⋯⟩
    rw [h_witIn_f_0_eq_c, h_c_eq]; rfl

  -- Combine to finish the proof
  change stmtIn.sumcheck_target = eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
    witIn.f ⟨0, by simp only [Fin.val_last, zero_mem]⟩
  rw [←h_H_eval_at_zero_eq_mul]
  exact h_sumcheck_cons
-/

/- Final sumcheck step logic is strongly complete.
**Key Proof Obligations:**
1. **Verifier Check**: Show that `stmtIn.sumcheck_target = eq_tilde_eval * c`
   where `c = wit.f ⟨0, ...⟩`
   - This should follow from `h_relIn` (roundRelation) which includes `oracleWitnessConsistency`
   - The `oracleWitnessConsistency` includes:
     * `witnessStructuralInvariant`: `wit.H = projectToMidSumcheckPoly ...`
       and `wit.f = getMidCodewords ...`
     * `sumcheckConsistencyProp`:
       `stmt.sumcheck_target = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ℓ), wit.H.val.eval x`
       For `i = Fin.last ℓ`, we have `ℓ - ℓ = 0`, so this is a sum over 0 variables
   - Need to connect these properties to show the verifier check passes

2. **Relation Out**: Show that the output satisfies `finalSumcheckRelOut`
  - This involves showing `finalFoldingStateProp` holds for the output
-/
set_option maxHeartbeats 4000000 in
/-- **The final sumcheck step logic is strongly complete** (direct proof; discharges the former
`FinalSumcheckStepLogicCompleteResidual`, issue #327). The four obligations: the verifier check
(`finalSumcheckStep_verifierCheck_passed`), the relation out (oracle-folding consistency via
`finalSumcheckStep_strictOracleFoldingConsistency_out` plus the final-constant weld
`getLastOracle_finalFold_eq_eval'` against `finalSumcheckStep_final_codeword_eq_eval`), and the
two prover/verifier output agreements (definitional). -/
lemma finalSumcheckStep_is_logic_complete :
    (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  simp only [finalSumcheckStepLogic, strictRoundRelation, strictRoundRelationProp,
    Set.mem_setOf_eq] at h_relIn
  obtain ⟨h_sumcheck_cons, h_strictOWC⟩ := h_relIn
  have h_wit_struct := h_strictOWC.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. verifier check
    exact finalSumcheckStep_verifierCheck_passed 𝔽q β (𝓑 := 𝓑) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
      (oStmtIn := oStmtIn) (challenges := challenges)
      (h_sumcheck_cons := h_sumcheck_cons) (h_wit_struct := h_wit_struct)
  · -- 2. relation out
    simp only [finalSumcheckStepLogic, strictFinalSumcheckRelOut,
      strictFinalSumcheckRelOutProp, Set.mem_setOf_eq]
    refine ⟨witIn.t, ?_, ?_⟩
    · -- component 1: oracle-folding consistency at the output
      exact finalSumcheckStep_strictOracleFoldingConsistency_out 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
        (oStmtIn := oStmtIn) h_strictOWC
    · -- component 2: the final-constant consistency
      funext x
      have h_oracle_out := finalSumcheckStep_strictOracleFoldingConsistency_out 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
        (oStmtIn := oStmtIn) h_strictOWC
      have h_k : (getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)).val = ℓ - ϑ := by
        dsimp only [getLastOracleDomainIndex]
        rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
          Nat.div_mul_cancel (hdiv.out)]
      have hϑℓ : ϑ ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
      have h_k' : (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) * ϑ = ℓ - ϑ := by
        rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
          Nat.div_mul_cancel (hdiv.out)]
      have h_final := getLastOracle_finalFold_eq_eval' 𝔽q β (t := witIn.t)
        (challenges := stmtIn.challenges) (oStmt := oStmtIn) h_oracle_out
        (curIdx := ⟨(getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)).val, by omega⟩)
        (destIdx := ⟨(getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)).val + ϑ, by omega⟩)
        (hcur := h_k) (hdest := rfl)
        (hdest_le := by
          simp only [Fin.mk_le_mk]
          omega)
        (h_destIdx_oracle := rfl)
        (hpos := by omega)
        (rchal := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
          (i := Fin.last ℓ) stmtIn.challenges
          (getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)).val (h := by
            simp only [Fin.val_last]
            omega))
        (hrchal := rfl)
        (y := x)
      have h_codeword := finalSumcheckStep_final_codeword_eq_eval 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
        h_wit_struct
      exact h_final.trans h_codeword.symm
  · -- 3. statements agree
    rfl
  · -- 4. oracle statements agree
    rfl
/-
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑))
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  let c := transcript.messages ⟨0, rfl⟩

  -- Extract properties from h_relIn BEFORE any simp changes its structure
  simp only [finalSumcheckStepLogic, strictRoundRelation, strictRoundRelationProp,
    Set.mem_setOf_eq] at h_relIn
  obtain ⟨h_sumcheck_cons, h_strictOracleWitConsistency_In⟩ := h_relIn
  -- Extract t from strictOracleWitnessConsistency (which includes witnessStructuralInvariant)
  have h_wit_struct := h_strictOracleWitConsistency_In.1
  let t := witIn.t
  let h_VCheck_passed := finalSumcheckStep_verifierCheck_passed 𝔽q β (𝓑 := 𝓑) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
    (oStmtIn := oStmtIn) (challenges := challenges)
    (h_sumcheck_cons := h_sumcheck_cons)
    (h_strictOracleWitConsistency_In := by exact h_strictOracleWitConsistency_In)

  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, finalSumcheckStepLogic]

  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by rfl -- not new oracles added

  have h_first_oracle_eq : (getFirstOracle 𝔽q β verifierOStmtOut)
    = (getFirstOracle 𝔽q β oStmtIn) := by
    rw [← hOStmtOut_eq]
    simp only [proverOStmtOut, proverOutput, step, finalSumcheckStepLogic, getFirstOracle]

  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- clear_value h_VCheck_passed
    -- Fact 2: Output relation holds (foldStepRelOut)
    simp only [finalSumcheckStepLogic, strictRoundRelation, strictRoundRelationProp, Fin.val_last,
      Prod.mk.eta, Set.mem_setOf_eq, strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
      strictfinalSumcheckStepFoldingStateProp, exists_and_right, Subtype.exists, Fin.isValue, MessageIdx,
      Fin.eta, step]
    -- let r_i' := challenges ⟨1, rfl⟩
    -- rw [h_verifierOStmtOut_eq];
    dsimp only [strictOracleWitnessConsistency, Fin.val_last, OracleFrontierIndex.mkFromStmtIdx,
      strictOracleFoldingConsistencyProp, Fin.eta, ↓dreduceIte,
    Bool.false_eq_true] at h_strictOracleWitConsistency_In ⊢
    -- Extract the three components from the input
    let ⟨h_wit_struct_In, h_oracle_folding_In⟩ := h_strictOracleWitConsistency_In
    -- Now prove each component for the output
    refine ⟨?_, ?_⟩
    · -- Component 1: oracleFoldingConsistencyProp
      use t
      simp only [SetLike.coe_mem, exists_const]
      exact h_oracle_folding_In
    · -- Component 2: finalOracleFoldingConsistency
      funext y
      let res := iterated_fold_to_const_strict 𝔽q β (𝓑 := 𝓑) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
        (oStmtIn := oStmtIn) (challenges := challenges)
        (h_strictOracleWitConsistency_In := h_strictOracleWitConsistency_In)
      rw [res]; rfl

  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq
-/

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
