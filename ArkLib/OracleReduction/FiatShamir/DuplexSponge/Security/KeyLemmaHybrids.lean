/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFoundations

/-!
# The CO25 §5.8 hybrid ladder `Hyb₀ … Hyb₄` on the eager Key-Lemma surface

This module resurrects the Section 5.8 hybrid chain of the Chiesa–Orrù paper [CO25] that was
deleted together with the May-era sorry-scaffolded `KeyLemma.lean` (visible in git history at
commit `051801765`, file `Security/KeyLemma.lean`, defs `hyb_0 … hyb_4`, `hybridGame`,
`hybChallengeImpl`, `claim_5_21 … claim_5_24`), and rebuilds it on the repaired **eager**
statement surface of `KeyLemmaFoundations` (`basicFiatShamirGameEagerRand`,
`duplexSpongeFiatShamirGameRemappedEager`, `KeyLemmaStatementEager`).

## What is resurrected vs rebuilt

*Resurrected* (sound in the deleted ladder, adapted here):
- the five-hybrid structure with per-hybrid `(challenge-oracle distribution, gᵢ-realization,
  line-4 trace map)` triples and the claim assignment
  `Δ(Hyb₀,Hyb₁) ≤ Claim 5.21`, `Δ(Hyb₁,Hyb₂) ≤ Claim 5.22`, `Δ(Hyb₂,Hyb₃) = 0` (Claim 5.23),
  `Δ(Hyb₃,Hyb₄) ≤ Claim 5.24`;
- the common Figure-4 skeleton (lines 2–4) with the `tr_i` memo threaded from the prover run
  into the verifier run (CO25 §5.4 D2SAlgo Item 3) — here `hybGameEager`;
- the `gᵢ`-realizations: forward-to-`g` for `Hyb₁`, decode-then-`ψ⁻¹`-preimage for `Hyb₂`
  (CO25 §5.4 Item 4(e)i), the Eq. 16 memoized codec bridge for `Hyb₃`;
- the auxiliary-log projection `projectChallengePlusUnitQueryLog` and the line-4 remaps
  (`(φ⁻¹, ψ)` for `Hyb₁`, `φ⁻¹` for `Hyb₂`, identity for `Hyb₃`).

*Rebuilt* (the deleted ladder was wrong/incompatible here, and was deleted because every claim
and the main lemma were `sorry`s — against repo convention):
- the games live on the **unsalted eager surface**: split prover/verifier logs over
  `oSpec + fsChallengeOracle StmtIn pSpec`, oracles sampled **once** per game
  (`OracleDistribution.sample`), endpoints **definitionally** the two sides of
  `KeyLemmaStatementEager` (the deleted ladder used a salted single-log
  `BasicFiatShamirGameOutput` surface incompatible with the in-tree games, and its `lemma_5_1`
  targeted the numerically over-strong `ηStar` with exponent `C+1`);
- `Hyb₃`'s bridge `d2sCodecBridgeImplMemoEager` re-keys the salted Eq. 16 bridge onto the
  unsalted FS oracle by erasing the salt at the `fᵢ`-query boundary — exactly mirroring the
  salt erasure performed by the witness `eagerSimulatedProver`, so the `Hyb₃ → Hyb₄` step is
  the genuine verifier-replay gap (CO25 Claim 5.24) and not a salt-format mismatch;
- the per-step obligations are named `*Residual : Prop` definitions (never `sorry`s), and the
  ladder assembly `keyLemmaEager_of_steps` is **proven**: the four step residuals plus the
  witness budget residuals (M1c/M1d of `KeyLemmaFoundations`) imply `KeyLemmaEagerResidual`.

## Proven here (no `sorry`, axiom-clean)

- `hyb0_eq_duplexSpongeRemappedEager` / `hyb4_eq_basicFiatShamirEagerRand`: the ladder
  endpoints are (definitionally) the two sides of `KeyLemmaStatementEager`.
- `eagerMaliciousProver_*_budget`: budget transfer from the eager prover `P` to the salted
  malicious prover fed to `d2sAlgo`.
- `eagerSimulatedProver_challenge_budget` / `eagerSimulatedProver_shared_budget`: the witness
  `P'` inherits the `θ★`/shared budgets from the M1c/M1d residuals through the salt-erasing
  re-keying (via `IsQueryBoundP.simulateQ_of_step`).
- `keyLemmaEager_of_steps`: `Hyb01StepResidual → Hyb12StepResidual → Hyb23StepResidual →
  Hyb34StepResidual → SimulatedProverChallengeBudgetResidual →
  SimulatedProverSharedBudgetResidual → KeyLemmaEagerResidual`, assembled with
  `tvDist_chain4` and `claimSum_le_ηStarPaper`.

## Open core (named `*Residual : Prop`, NOT proven)

- `Hyb01StepResidual` — CO25 Claim 5.21 (Lemma 5.8 birthday bound: random permutation vs
  random encoded-challenge functions).
- `Hyb12StepResidual` — CO25 Claim 5.22 (codec decoding bias, Eq. 53).
- `Hyb23StepResidual` — CO25 Claim 5.23 (encoded/decoded query-format equivalence, exactly 0).
- `Hyb34StepResidual` — CO25 Claim 5.24 (verifier replay, Eq. 55).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.KeyLemmaHybrids

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations
open scoped NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  -- `Codec` (CO25 Def. 4.1) supplies `HasMessageSize`/`HasChallengeSize` and the
  -- `Serialize`/`Deserialize` instances; declaring standalone copies would diverge from the
  -- instances used by the §5.4/§5.5 simulator infrastructure.
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

/-! ## Auxiliary-log projection and the unsalted line-4 trace maps (CO25 §5.8, Figure 4 line 4)

Resurrected from the deleted ladder (`projectD2SChallengePlusUnitQueryLog`,
`hyb1Line4Trace`/`hyb2Line4Trace` — the in-tree versions in `TraceTransform` are salted), and
re-keyed onto the unsalted eager surface: the salt component of a `gSpec`/`eSpec` query is
dropped, matching the unsalted `d2sTrace` used by the `Hyb₀` endpoint (which keys remapped
entries at `(stmt, messagesBefore)` without a salt). -/

section LineFourEager

variable {δ : ℕ}

/-- CO25 §5.8. Project out the auxiliary `(Unit →ₒ U) + unifSpec` sampling queries from logs
over `oSpec + D2SChallengePlusUnitOracle challengeSpec`, retaining only shared and
challenge-oracle entries (resurrected from the deleted ladder; the auxiliary randomness is
internal to the simulator and not part of the paper's trace `tr_𝒫̃ ‖ tr_𝒱`). -/
def projectChallengePlusUnitQueryLog {κ : Type} {challengeSpec : OracleSpec κ}
    (log : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)) :
    QueryLog (oSpec + challengeSpec) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
    | ⟨.inr (.inl q), r⟩ => some ⟨.inr q, r⟩
    | ⟨.inr (.inr _), _⟩ => none

/-- CO25 §5.8 `Hyb₁` line 4, unsalted: the `(φ⁻¹, ψ)` per-entry remap. Encoded prover-prefix
and encoded verifier response are decoded (`φ⁻¹` on the message prefix, `ψ` on the response);
the on-sponge salt is dropped, matching the unsalted `d2sTrace` of the `Hyb₀` endpoint.
Entries with malformed encoded prefixes (`φ⁻¹ = ⊥`) are filtered. -/
noncomputable def hyb1Line4TraceEager
    (log : QueryLog (oSpec + gSpec (U := U) StmtIn pSpec δ)) :
    UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  pure (log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
    | ⟨.inr ⟨roundIdx, (stmt, _salt, encodedMessages)⟩, response⟩ =>
        match hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) roundIdx encodedMessages with
        | none => none
        | some messagesBefore =>
            let responseVec : Vector U (challengeSize (pSpec := pSpec) roundIdx) := response
            let challenge : pSpec.Challenge roundIdx := Deserialize.deserialize responseVec
            some ⟨.inr ⟨roundIdx, (stmt, messagesBefore)⟩, challenge⟩)

/-- CO25 §5.8 `Hyb₂` line 4, unsalted: the `φ⁻¹`-only per-entry remap. The encoded
prover-prefix is decoded; the response is already a decoded challenge; the salt is dropped
(see `hyb1Line4TraceEager`). -/
noncomputable def hyb2Line4TraceEager
    (log : QueryLog (oSpec + eSpec (U := U) StmtIn pSpec δ)) :
    UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  pure (log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
    | ⟨.inr ⟨roundIdx, (stmt, _salt, encodedMessages)⟩, challenge⟩ =>
        match hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) roundIdx encodedMessages with
        | none => none
        | some messagesBefore =>
            some ⟨.inr ⟨roundIdx, (stmt, messagesBefore)⟩,
              (challenge : pSpec.Challenge roundIdx)⟩)

/-- CO25 §5.8 `Hyb₃` line 4, unsalted output surface: the salt-erasing per-entry remap.
`Hyb₃` queries the **salted** basic-FS oracle `fᵢ((𝕩, τ̌), msgs)` (CO25 Eq. 54); the eager
output surface is the unsalted `fsChallengeOracle`, so the trace map projects the salt out
of every challenge-entry key. Shared-`oSpec` entries pass through verbatim. -/
noncomputable def hyb3Line4SaltErase (Salt : Type)
    (log : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :=
  pure (log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
    | ⟨.inr ⟨roundIdx, ((stmt, _salt), messagesBefore)⟩, challenge⟩ =>
        some ⟨.inr ⟨roundIdx, (stmt, messagesBefore)⟩, challenge⟩)

end LineFourEager

/-! ## Per-hybrid `gᵢ`-realizations (CO25 §5.8 / §5.4 Eq. 16) -/

section GRealizations

variable {δ : ℕ}

/-- CO25 §5.8 `Hyb₁` `gᵢ`-realization (resurrected): forward each `gSpec` query straight into
the external encoded challenge oracle. No `ψᵢ⁻¹` step is needed since the oracle already
returns the encoded `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}`. Trivial inner state `M := PUnit`. -/
noncomputable def gImplEncodedForward :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) PUnit :=
  fun q =>
    StateT.lift <|
      OptionT.lift <|
        (show OracleComp
            (D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
            (Vector U (challengeSize (pSpec := pSpec) q.1)) from
          query
            (spec := D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
            (.inl q))

variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- CO25 §5.8 `Hyb₂` `gᵢ`-realization (resurrected): query the decoded challenge oracle `eᵢ`
for `ρᵢ ∈ ℳ_{V,i}`, then sample a uniform `ψᵢ⁻¹` preimage to recover the encoded
`ρ̂ᵢ ∈ Σ^{ℓ_V(i)}` (CO25 §5.4 Item 4(e)i). Trivial inner state `M := PUnit`. -/
noncomputable def gImplDecodedChallenge :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (eSpec (U := U) StmtIn pSpec δ) PUnit :=
  fun q => do
    let challenge ←
      StateT.lift <|
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
              (pSpec.Challenge q.1) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
              (.inl q))
    StateT.lift <|
      OptionT.lift <|
        uniformDeserializePreimage (pSpec := pSpec) (U := U)
          (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge

variable {Salt : Type} [SaltCodec U δ Salt]

/-- **Memoized `Hyb₁` `gᵢ`-realization** (CO25 §5.4 D2SAlgo Item 3): the `tr_i` memo is part
of the simulator itself and therefore present in *every* hybrid, not only the `Hyb₃` bridge.
On a fresh full key `(i, 𝕩, τ̂, α̂)` the encoded challenge oracle is queried once and the
response committed; repeated keys replay the committed response without an external query.
(The memo-free forward realization is kept above as `gImplEncodedForward` for reference; the
ladder uses this memoized form so that the per-key log shapes and response stability agree
across `Hyb₁`–`Hyb₃` — see the issue #314 ladder-repair note.) -/
noncomputable def gImplEncodedForwardMemo (Salt : Type) [SaltCodec U δ Salt] :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) (D2SAlgoMemo StmtIn U δ Salt pSpec) :=
  fun q => do
    let memo ← get
    match lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
        (pSpec := pSpec) memo q.1 q.2.1
        (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) q.2.2.1) q.2.2.2 with
    | some response => pure response
    | none => do
        let response ←
          StateT.lift <|
            OptionT.lift <|
              (show OracleComp
                  (D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
                  (Vector U (challengeSize (pSpec := pSpec) q.1)) from
                query
                  (spec := D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
                  (.inl q))
        modify (fun m =>
          insertD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
            (pSpec := pSpec) m
            { roundIdx := q.1, stmt := q.2.1,
              salt := SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) q.2.2.1,
              encodedMessages := q.2.2.2, response := response })
        pure response

/-- **Memoized `Hyb₂` `gᵢ`-realization** (CO25 §5.4 Items 3 + 4(e)i): on a fresh full key,
query the decoded challenge oracle `eᵢ`, sample one uniform `ψᵢ⁻¹` preimage, and commit it to
the `tr_i` memo; repeated keys replay the committed encoding. Without the memo, a repeated
key would re-sample a fresh `ψ⁻¹` preimage (visible to the prover) and re-log the external
query — both divergences from the paper's simulator and from the `Hyb₃` bridge. -/
noncomputable def gImplDecodedChallengeMemo (Salt : Type) [SaltCodec U δ Salt] :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (eSpec (U := U) StmtIn pSpec δ) (D2SAlgoMemo StmtIn U δ Salt pSpec) :=
  fun q => do
    let memo ← get
    match lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
        (pSpec := pSpec) memo q.1 q.2.1
        (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) q.2.2.1) q.2.2.2 with
    | some response => pure response
    | none => do
        let challenge ←
          StateT.lift <|
            OptionT.lift <|
              (show OracleComp
                  (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
                  (pSpec.Challenge q.1) from
                query
                  (spec := D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
                  (.inl q))
        let response ←
          StateT.lift <|
            OptionT.lift <|
              uniformDeserializePreimage (pSpec := pSpec) (U := U)
                (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge
        modify (fun m =>
          insertD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
            (pSpec := pSpec) m
            { roundIdx := q.1, stmt := q.2.1,
              salt := SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) q.2.2.1,
              encodedMessages := q.2.2.2, response := response })
        pure response

/-- Salt-erasing spec re-keying for the §5.4 Eq. 16 bridge target: a salted basic-FS challenge
query `fᵢ((𝕩, τ̌), msgs)` is forwarded to the **unsalted** oracle as `fᵢ(𝕩, msgs)`; the
auxiliary `(Unit →ₒ U) + unifSpec` summand is forwarded verbatim. This is the in-monad
counterpart of the salt erasure performed by the eager witness (`saltEraseWitnessImpl`),
keeping the `Hyb₃` oracle surface identical to the `Hyb₄` witness surface. -/
noncomputable def saltEraseChallengePlusUnitImpl :
    QueryImpl
      (D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (OracleComp (D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle StmtIn pSpec))) :=
  fun q =>
    match q with
    | .inl qf =>
        query
          (spec := D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle StmtIn pSpec))
          (.inl ⟨qf.1, (qf.2.1.1, qf.2.2)⟩)
    | .inr aux =>
        query
          (spec := D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle StmtIn pSpec))
          (.inr aux)

/-- CO25 §5.8 `Hyb₃` `gᵢ`-realization: the **genuine** §5.4 Eq. 16 memoized codec bridge
`ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` (`d2sCodecBridgeImplMemo`, with the `tr_i` memo of D2SAlgo Item 3),
re-keyed onto the **unsalted** FS challenge oracle by erasing the salt at the `fᵢ`-query
boundary (`saltEraseChallengePlusUnitImpl`). The memo still keys on the full
`(i, 𝕩, τ̌, α̂)` tuple, so Item 3 determinism is unchanged. -/
noncomputable def d2sCodecBridgeImplMemoEager :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (fsChallengeOracle StmtIn pSpec) (D2SAlgoMemo StmtIn U δ Salt pSpec) :=
  fun gq => do
    let memo ← get
    let res ← StateT.lift <|
      OptionT.mk <|
        simulateQ
          (saltEraseChallengePlusUnitImpl (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (Salt := Salt))
          (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
              (δ := δ) (Salt := Salt) gq).run memo).run)
    set res.2
    pure res.1

end GRealizations

/-! ## The common eager hybrid-game skeleton (CO25 Figure 4 lines 2–4) -/

section Skeleton

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- CO25 §5.8, Figure 4 lines 2–4 on the eager surface (resurrected `hybridGame` +
`hybridGameDist`, rebuilt unsalted with split logs):

- sample one realization `c ← Dχ` of the per-hybrid challenge-oracle distribution
  (`𝒟_Σ` / `𝒟_e` / `𝒟_IP`), held fixed for the whole run;
- run the malicious prover `𝒫̃^{D2SQuery^g}` (line 2) via `d2fRaw` with the per-hybrid
  `gᵢ`-realization, logging at the simulator's outer spec;
- run the verifier `𝒱^{D2SQuery^g}` (line 3) through the same pipeline, **sharing the
  prover's `tr_i` memo** (CO25 §5.4 D2SAlgo Item 3);
- project away the auxiliary sampling randomness and push both logs through the per-hybrid
  line-4 trace map (line 4), landing on the unsalted eager output surface.

Abort (`OptionT` failure, `φ⁻¹ = ⊥`, or verifier rejection) collapses to `none`, matching the
abort collapse of the eager endpoints. -/
noncomputable def hybGameEager [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ} {M : Type} [Inhabited M] (δ : ℕ)
    (Dχ : OracleDistribution challengeSpec)
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (lineFour : QueryLog (oSpec + challengeSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    ProbComp (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) := do
  let c ← Dχ.sample
  let coins : QueryImpl unifSpec ProbComp := fun m => (liftM (unifSpec.query m) : ProbComp _)
  let impl : QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) ProbComp :=
    oImpl + (Dχ.toImpl c + (d2sUnitSampleImpl (U := U) + coins))
  let ⟨pRes?, pLogRaw⟩ ←
    simulateQ impl
      ((simulateQ loggingOracle
        ((d2fRaw (T_H := T_H) (T_P := T_P) gImpl P default).run)).run)
  match pRes? with
  | none => pure none
  | some ⟨⟨⟨stmtIn, messages⟩, _⟩, memo⟩ => do
      let ⟨vRes?, vLogRaw⟩ ←
        simulateQ impl
          ((simulateQ loggingOracle
            ((d2fRaw (T_H := T_H) (T_P := T_P) gImpl
              ((V.duplexSpongeFiatShamir.run
                stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run)
              memo).run)).run)
      match vRes? with
      | none => pure none
      | some ⟨⟨stmtOut?, _⟩, _⟩ =>
          match stmtOut? with
          | none => pure none
          | some stmtOut => do
              let pLog'? ←
                simulateQ (d2sUnitSampleImpl (U := U))
                  ((lineFour (projectChallengePlusUnitQueryLog (U := U) pLogRaw)).run)
              let vLog'? ←
                simulateQ (d2sUnitSampleImpl (U := U))
                  ((lineFour (projectChallengePlusUnitQueryLog (U := U) vLogRaw)).run)
              match pLog'?, vLog'? with
              | some pLog', some vLog' =>
                  pure (some ⟨stmtIn, stmtOut, messages, pLog', vLog'⟩)
              | _, _ => pure none

end Skeleton

/-! ## The ladder `Hyb₀ … Hyb₄` (CO25 §5.8) -/

section Ladder

/-- CO25 §5.8 `Hyb₀`: the remapped DSFS game on the eager surface — `(h, p, p⁻¹) ← 𝒟_𝔖`
(`D_DS`, one `Equiv.Perm` answering both `p` and `p⁻¹`), logs pushed through the §5.5
`D2STrace`. **Definitionally** the right-hand side of `KeyLemmaStatementEager`. -/
noncomputable def Hyb0 [SampleableType U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[duplexSpongeFiatShamirGameRemappedEager (T_H := T_H) (T_P := T_P) δ
      (D_DS StmtIn U) oImpl V P]

/-- CO25 §5.8 `Hyb₁`: prover and verifier run against the §5.4 simulator `D2SQuery^g` with
the encoded challenge functions `g = (gᵢ)ᵢ ← 𝒟_Σ` sampled eagerly as one uniform table
(CO25 Eq. 15), `gᵢ` realized through the `tr_i`-memoized forward (D2SAlgo Item 3 — the memo
is part of the simulator and present in every hybrid); line-4 map `(φ⁻¹, ψ)`. -/
noncomputable def Hyb1 [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[hybGameEager (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (gSpec (U := U) StmtIn pSpec δ))
      (gImplEncodedForwardMemo (StmtIn := StmtIn) (δ := δ) Salt)
      (hyb1Line4TraceEager (δ := δ)) oImpl V P]

/-- CO25 §5.8 `Hyb₂`: the decoded challenge functions `e = (eᵢ)ᵢ ← 𝒟_e` sampled eagerly as
one uniform table (CO25 Eq. 52), `gᵢ` realized as the `tr_i`-memoized `ψᵢ⁻¹ ∘ eᵢ` (uniform
preimage sampling on fresh keys, CO25 §5.4 Items 3 + 4(e)i); line-4 map `φ⁻¹`. -/
noncomputable def Hyb2 [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[hybGameEager (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (eSpec (U := U) StmtIn pSpec δ))
      (gImplDecodedChallengeMemo (StmtIn := StmtIn) (δ := δ) Salt)
      (hyb2Line4TraceEager (δ := δ)) oImpl V P]

/-- CO25 §5.8 `Hyb₃`: the **salted** basic-FS challenge functions `f = (fᵢ)ᵢ ← 𝒟_IP`
(CO25 Eq. 54 keys `fᵢ` on the salted statement `(𝕩, τ̌)`), `gᵢ` realized by the §5.4 Eq. 16
memoized codec bridge `ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` (`d2sCodecBridgeImplMemo`, **without** salt
erasure — the salt-erased bridge made `Δ(Hyb₂, Hyb₃) = 0` false by correlating challenges
across salts; see the issue #314 ladder-repair note); line-4 map = the salt-erasing log
projection onto the unsalted eager output surface. The salt-collision cost moves to the
`Hyb₃ → Hyb₄` leg, where the Claim 5.24 verifier-replay budget lives. -/
noncomputable def Hyb3 [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[hybGameEager (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec))
      (d2sCodecBridgeImplMemo (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (hyb3Line4SaltErase Salt) oImpl V P]

/-- CO25 §5.8 `Hyb₄`: the eager basic-FS game with `f ← 𝒟_IP` (uniform, the same distribution
as `Hyb₃`) against a basic-FS prover `P'`. **Definitionally** the left-hand side of
`KeyLemmaStatementEager` once `P'` is the simulated prover witness. -/
noncomputable def Hyb4
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P' : OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[basicFiatShamirGameEagerRand
      (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec)) oImpl V P']

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Endpoint identification, right-hand side: `Hyb₀` **is** the remapped eager DSFS game
distribution appearing in `KeyLemmaStatementEager` (with the canonical `D_DS` carrier). -/
lemma hyb0_eq_duplexSpongeRemappedEager [SampleableType U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    Hyb0 T_H T_P δ oImpl V P
      = 𝒟[duplexSpongeFiatShamirGameRemappedEager (T_H := T_H) (T_P := T_P) δ
          (D_DS StmtIn U) oImpl V P] := rfl

omit [SpongeSize] [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Endpoint identification, left-hand side: `Hyb₄` **is** the eager basic-FS game
distribution appearing in `KeyLemmaStatementEager` (with the canonical uniform FS-challenge
distribution). -/
lemma hyb4_eq_basicFiatShamirEagerRand
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P' : OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)
      (StmtIn × pSpec.Messages)) :
    Hyb4 oImpl V P'
      = 𝒟[basicFiatShamirGameEagerRand
          (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec)) oImpl V P'] := rfl

end Ladder

/-! ## The witness `P'` for `Hyb₄`: `D2SAlgo^f` on the unsalted coin-equipped spec -/

section Witness

variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- Attach a constant on-sponge salt to the eager malicious prover, producing the
`MaliciousProver` shape consumed by `d2sAlgo` (CO25 §5.4). The eager surface carries no
prover-chosen salt (the in-tree DSFS game output is salt-free), so the canonical all-zero
salt is used; it is erased again at the FS boundary by `saltEraseWitnessImpl`. -/
noncomputable def eagerMaliciousProver (δ : ℕ)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    MaliciousProver oSpec pSpec StmtIn U δ :=
  (fun xm => (xm.1, (Vector.replicate δ (0 : U), xm.2))) <$> P

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [DecidableEq StmtIn]
  [DecidableEq U] [Fintype U] codec [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, Fintype (pSpec.Challenge i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- Budget transfer onto the salted malicious prover: attaching a constant salt is a `map`
and preserves every predicate-targeted query budget. -/
lemma eagerMaliciousProver_budget {δ : ℕ}
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    {p : (ι ⊕ (StmtIn ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U)) → Prop}
    [DecidablePred p] {b : ℕ} (h : IsQueryBoundP P p b) :
    IsQueryBoundP (eagerMaliciousProver (δ := δ) P) p b :=
  (isQueryBoundP_map_iff _ _ _).mpr h

variable {Salt : Type} {δ : ℕ} [SaltCodec U δ Salt]

/-- Salt-erasing re-keying of the coin-equipped witness spec: a salted FS challenge query
`fᵢ((𝕩, τ̌), msgs)` becomes the unsalted `fᵢ(𝕩, msgs)`; shared-`oSpec` and `unifSpec` coin
queries are forwarded verbatim. This is the witness-side counterpart of
`saltEraseChallengePlusUnitImpl` (the `Hyb₃` bridge re-keying). -/
noncomputable def saltEraseWitnessImpl :
    QueryImpl ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)
      (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)) :=
  fun q =>
    match q with
    | .inl (.inl qo) =>
        query (spec := (oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)
          (.inl (.inl qo))
    | .inl (.inr qf) =>
        query (spec := (oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)
          (.inl (.inr ⟨qf.1, (qf.2.1.1, qf.2.2)⟩))
    | .inr m =>
        query (spec := (oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)
          (.inr m)

variable [SampleableType U] [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]

/-- The witness `P'` for the eager key lemma: CO25's `D2SAlgo^f(𝒫̃)` (§5.4 Items 1–6),
re-associated onto the coin-equipped witness spec with abort collapsed
(`simulatedProverSalted` of `KeyLemmaFoundations`, M1b), with the salt erased at the
FS-oracle boundary and dropped from the output proof. This is the prover plugged into the
`Hyb₄` endpoint by the assembly theorem. -/
noncomputable def eagerSimulatedProver
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ' : ℕ) (Salt' : Type)
    [SaltCodec U δ' Salt'] [Inhabited (StmtIn × FSSaltedProof pSpec Salt')]
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)
      (StmtIn × pSpec.Messages) :=
  (fun o => (o.1, o.2.2)) <$>
    simulateQ (saltEraseWitnessImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (Salt := Salt'))
      (simulatedProverSalted (T_H := T_H) (T_P := T_P) (Salt := Salt')
        (coinUnitImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (Salt := Salt'))
        (eagerMaliciousProver (δ := δ') P))

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- The witness inherits the `θ★` FS-challenge budget from the M1c residual
(`SimulatedProverChallengeBudgetResidual`) through the salt-erasing re-keying: each salted
challenge query becomes exactly one unsalted challenge query, and no other branch of
`saltEraseWitnessImpl` emits a challenge query. -/
lemma eagerSimulatedProver_challenge_budget
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (hM1c : SimulatedProverChallengeBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) T_H T_P)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ : ℕ)
    (hPerm : IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ) :
    IsQueryBoundP
      (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P)
      (fun j => isFSChallengeCoinIdx j = true) (θStar tₕ tₚ tₚᵢ) := by
  have hS := hM1c
    (coinUnitImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (Salt := Salt))
    (eagerMaliciousProver (δ := δ) P) tₕ tₚ tₚᵢ
    (fun qu => coinUnitImpl_challenge_budget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (Salt := Salt) qu)
    (eagerMaliciousProver_budget (δ := δ) P hPerm)
  unfold eagerSimulatedProver
  rw [isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_of_step hS ?_ ?_
  · intro t ht
    match t with
    | .inl (.inl qo) => simp [isFSChallengeCoinIdx] at ht
    | .inl (.inr qf) =>
        simp only [saltEraseWitnessImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => one_pos
    | .inr m => simp [isFSChallengeCoinIdx] at ht
  · intro t ht
    match t with
    | .inl (.inl qo) =>
        simp only [saltEraseWitnessImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isFSChallengeCoinIdx])
    | .inl (.inr qf) => simp [isFSChallengeCoinIdx] at ht
    | .inr m =>
        simp only [saltEraseWitnessImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isFSChallengeCoinIdx])

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- The witness inherits the shared-`oSpec` budgets from the M1d residual
(`SimulatedProverSharedBudgetResidual`) through the salt-erasing re-keying: shared queries
are forwarded 1:1 and no other branch emits a shared query. -/
lemma eagerSimulatedProver_shared_budget [DecidableEq ι]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (hM1d : SimulatedProverSharedBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) T_H T_P)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₒ : ι → ℕ)
    (hShared : ∀ i : ι, IsQueryBoundP P (fun j => j.getLeft? = some i) (tₒ i))
    (i : ι) :
    IsQueryBoundP
      (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P)
      (fun j => isSharedCoinIdx i j = true) (tₒ i) := by
  have hS := hM1d
    (coinUnitImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (Salt := Salt))
    (eagerMaliciousProver (δ := δ) P) tₒ
    (fun qu i' => coinUnitImpl_shared_budget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (Salt := Salt) qu i')
    (fun i' => eagerMaliciousProver_budget (δ := δ) P (hShared i'))
    i
  unfold eagerSimulatedProver
  rw [isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_of_step hS ?_ ?_
  · intro t ht
    match t with
    | .inl (.inl qo) =>
        simp only [saltEraseWitnessImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => one_pos
    | .inl (.inr qf) => simp [isSharedCoinIdx] at ht
    | .inr m => simp [isSharedCoinIdx] at ht
  · intro t ht
    match t with
    | .inl (.inl qo) =>
        simp only [saltEraseWitnessImpl, HasQuery.instOfMonadLift_query]
        refine (isQueryBoundP_query_iff _ _ _).mpr fun h => ?_
        simp only [isSharedCoinIdx] at h ht
        exact absurd h ht
    | .inl (.inr qf) =>
        simp only [saltEraseWitnessImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isSharedCoinIdx])
    | .inr m =>
        simp only [saltEraseWitnessImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isSharedCoinIdx])

end Witness

/-! ## The four per-step TV-bound obligations (CO25 Claims 5.21–5.24)

Each is a named `*Residual : Prop` (repo convention; never a `sorry`): the genuinely open
research core of the §5.8 chain. The bounds are **exactly** the `claim5_2x` bounds of
`KeyLemmaFoundations`, which sum to `ηStarPaper` via `claimSum_le_ηStarPaper`. -/

section StepResiduals

/-- CO25 Claim 5.21 residual — `Δ(Hyb₀, Hyb₁) ≤ (7T² − 3T)/(2|Σ|^c)`,
`T = tₕ + 1 + tₚ + L + tₚᵢ`: replacing the random permutation `p` (one `Equiv.Perm` answering
`p` and `p⁻¹`) by the independent encoded challenge functions `g ← 𝒟_Σ` costs at most the
Lemma 5.8 birthday bound at the `Hyb₀`/`Hyb₁` trace length. Open: requires the BackTrack
chain coupling of CO25 §5.6 off the bad event `E` (Lemmas 5.8–5.10). -/
def Hyb01StepResidual [SampleableType U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    SPMF.tvDist (Hyb0 T_H T_P δ oImpl V P) (Hyb1 T_H T_P δ Salt oImpl V P)
      ≤ claim5_21Bound U tₕ tₚ tₚᵢ L

/-- CO25 Claim 5.22 residual (Eq. 53) — `Δ(Hyb₁, Hyb₂) ≤ θ★ · maxᵢ ε_cdc,i + Σᵢ ε_cdc,i`:
switching the encoded challenge functions `g` for `ψ⁻¹ ∘ e` with decoded `e ← 𝒟_e` costs the
codec decoding bias once per prover-side `gᵢ` query (`θ★ = tₚ` many) plus once per round for
the verifier side. Open: requires `Codec.decode_isBiased` pushed through the simulator. -/
def Hyb12StepResidual [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    SPMF.tvDist (Hyb1 T_H T_P δ Salt oImpl V P) (Hyb2 T_H T_P δ Salt oImpl V P)
      ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ codec.decodingBias

/-- CO25 Claim 5.23 residual — `Δ(Hyb₂, Hyb₃) = 0`: the two hybrids differ only in the query
format of the external oracle (decoded `eᵢ` vs salted-then-erased `fᵢ` behind `φ⁻¹`/`ψ⁻¹`);
the induced output distributions are identical. Open: requires the codec roundtrip
(`decode_surjective` and serialization injectivity) plus the `tr_i` memo determinism bricks
(F6) to align repeated-key behaviour on both sides. -/
def Hyb23StepResidual [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb2 T_H T_P δ Salt oImpl V P) (Hyb3 T_H T_P δ Salt oImpl V P) = 0

/-- CO25 Claim 5.24 residual (Eq. 55) —
`Δ(Hyb₃, Hyb₄) ≤ 7L(2tₕ+2+2tₚ+L+2tₚᵢ)/(2|Σ|^c) − 5(L+1)/|Σ|^c`: `Hyb₃` and `Hyb₄` use the
**same** eager FS oracle distribution; the gap is the verifier asymmetry only — `Hyb₃`'s
verifier rederives challenges through `D2SQuery` (and can abort on parse failure), `Hyb₄`'s
standard FS verifier replays the transcript directly against `f`. Open: requires the
verifier-replay analysis of CO25 §5.8 (the event `E_𝒱` that the replayed transcript diverges
from the simulator's committed one). -/
def Hyb34StepResidual [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    SPMF.tvDist (Hyb3 T_H T_P δ Salt oImpl V P)
        (Hyb4 oImpl V
          (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
      ≤ claim5_24Bound U tₕ tₚ tₚᵢ L

end StepResiduals

/-! ## Ladder assembly: the four steps + witness budgets imply the eager key lemma -/

section Assembly

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- **Ladder assembly** (CO25 §5.8, the proof skeleton of Lemma 5.1): the four per-step
residuals (Claims 5.21–5.24) together with the witness budget residuals (M1c/M1d of
`KeyLemmaFoundations`) imply the full eager key lemma `KeyLemmaEagerResidual`.

The witness is `eagerSimulatedProver` (= CO25's `D2SAlgo^f(𝒫̃)` with abort collapsed and salt
erased); the distance bound is assembled with `tvDist_chain4` across
`Hyb₀ → Hyb₁ → Hyb₂ → Hyb₃ → Hyb₄` and closed numerically by `claimSum_le_ηStarPaper`
(Claim 5.23's step contributes exactly `0`). -/
theorem keyLemmaEager_of_steps
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (h01 : Hyb01StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h12 : Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h23 : Hyb23StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h34 : Hyb34StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (hM1c : SimulatedProverChallengeBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) T_H T_P)
    (hM1d : SimulatedProverSharedBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) T_H T_P) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl := by
  intro V P tₒ tₕ tₚ tₚᵢ L hL hShared hHash hPerm hPermInv
  refine ⟨eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P,
    ?_, ?_, ?_⟩
  · -- shared-oSpec budgets of the witness (via M1d)
    intro i
    exact eagerSimulatedProver_shared_budget (δ := δ) (Salt := Salt) T_H T_P hM1d P tₒ
      hShared i
  · -- θ★ FS-challenge budget of the witness (via M1c)
    exact eagerSimulatedProver_challenge_budget (δ := δ) (Salt := Salt) T_H T_P hM1c P
      tₕ tₚ tₚᵢ hPerm
  · -- the total-variation bound, assembled across the ladder
    have hchain :=
      tvDist_chain4
        (Hyb0 T_H T_P δ oImpl V P) (Hyb1 T_H T_P δ Salt oImpl V P)
        (Hyb2 T_H T_P δ Salt oImpl V P)
        (Hyb3 T_H T_P δ Salt oImpl V P)
        (Hyb4 oImpl V
          (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
        (h01 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
        (h12 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
        (le_of_eq (h23 V P))
        (h34 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
    rw [← hyb4_eq_basicFiatShamirEagerRand oImpl V
        (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P),
      ← hyb0_eq_duplexSpongeRemappedEager T_H T_P δ oImpl V P,
      SPMF.tvDist_comm]
    have hsum := claimSum_le_ηStarPaper (pSpec := pSpec) U tₕ tₚ tₚᵢ L codec.decodingBias
    linarith

end Assembly

#print axioms DuplexSpongeFS.KeyLemmaHybrids.hyb0_eq_duplexSpongeRemappedEager
#print axioms DuplexSpongeFS.KeyLemmaHybrids.hyb4_eq_basicFiatShamirEagerRand
#print axioms DuplexSpongeFS.KeyLemmaHybrids.eagerMaliciousProver_budget
#print axioms DuplexSpongeFS.KeyLemmaHybrids.eagerSimulatedProver_challenge_budget
#print axioms DuplexSpongeFS.KeyLemmaHybrids.eagerSimulatedProver_shared_budget
#print axioms DuplexSpongeFS.KeyLemmaHybrids.keyLemmaEager_of_steps

end DuplexSpongeFS.KeyLemmaHybrids

end
