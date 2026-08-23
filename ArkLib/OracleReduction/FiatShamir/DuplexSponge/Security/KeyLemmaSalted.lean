/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaHybrids
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SimulatorBudgets

/-!
# The salted + log-canonicalized CO25 §5.8 ladder (`Hyb₀ˢ … Hyb₄ˢ`)

This module rebuilds the §5.8 hybrid ladder of [CO25] on a **salted, log-canonicalized**
statement surface, repairing the two statement-level refutations of the unsalted eager ladder
(`KeyLemmaHybrids`) recorded on issue #314 (2026-06-10):

* **F1 (log-shape, all δ)**: the `tr_i`-memoized bridges of `Hyb₁`–`Hyb₃` are *query-silent*
  on memo hits, so the middle hybrids' verifier logs carry **zero** challenge entries, while
  both endpoints (`Hyb₀`'s remapped DS squeeze trace and `Hyb₄`'s `V.fiatShamir`) log one
  entry per (re-)derived challenge. The unsalted `Hyb01StepResidual` / `Hyb34StepResidual`
  are therefore false at every `δ` from log shape alone. Reading CO25 §5.4 (pp. 34–35)
  again: the paper's `D2SQuery` is memoless — the `tr_i` memo lives only in `D2SAlgo` — so
  the paper's per-hybrid line-4 traces carry *repeat* entries, and `QueryLog` multiplicity
  is an artifact of the in-tree memoization. The repair is **first-occurrence key-dedup**
  (`canonicalizeChallengeLog`) applied to both output logs of *every* game: a memo-silent
  log and a repeat-logged log canonicalize identically whenever per-key answers are stable
  (which is exactly what the memo and the eager tables guarantee).
* **F3 (salt erasure, δ ≥ 1)**: the unsalted `Hyb₄` endpoint erased the salt *inside the
  witness's oracle access* (`saltEraseWitnessImpl`), correlating challenges across distinct
  prover-chosen salts that are independent in `Hyb₃` — a deterministic salt-grinding
  distinguisher for any `δ ≥ 1`. CO25's endpoint is the **salted** basic FS (Construction
  3.17: `fᵢ` keyed on `(𝕩, τ̌)`, proofs `π̌ = (τ̌, α)`), so the repaired `Hyb₄ˢ` runs
  `Verifier.singleSaltFiatShamir` on `FSSaltedProof` over
  `fsChallengeOracle (StmtIn × Salt) pSpec`, and the witness is the **non-erasing**
  `simulatedProverSalted` pipeline.

The four salted step residuals (`Hyb01StepResidualS` … `Hyb34StepResidualS`, CO25 Claims
5.21–5.24 with the same `claim5_2x` bounds) supersede the refuted unsalted residuals of
`KeyLemmaHybrids`, and the assembly `keyLemmaEagerSalted_of_steps` is **proven**: the four
salted steps imply `KeyLemmaEagerSaltedResidual`, with the witness budgets discharged
directly by the proven `SimulatorBudgets.simulatedProverChallengeBudget` /
`simulatedProverSharedBudget` (which are stated for the non-erasing salted witness — no
re-keying transfer is needed, unlike the unsalted assembly).

## Output-proof salt convention

The ladder games `Hyb₀ˢ`–`Hyb₃ˢ` run the eager malicious prover `P` (whose in-tree DSFS
output carries no salt) and emit the **canonical** pre-encoded salt
`SaltCodec.encode (0^δ)` in the output proof — exactly the salt `eagerMaliciousProver`
attaches and `d2sAlgo` binarizes, so on the non-abort path `Hyb₄ˢ`'s witness emits the same
constant. The *prover-chosen per-chain salts* live where they matter for F3: in the
challenge-log **keys**, threaded by the salted trace maps (`d2sTraceSalted`,
`hyb1Line4Trace`/`hyb2Line4Trace`/`hyb3Line4Trace` of `TraceTransform` — all keying at
`(stmt, SaltCodec.encode τ̂)`). Nothing here is deferred: every game below is fully
definitional in terms of in-tree salted machinery; no `TraceTransform` edits were needed.

## δ = 0 recovery plan (docstring only; no proof obligation here)

For `δ = 0` the on-sponge salt type `Vector U 0` is a singleton, so `SaltCodec.encode` hits
a single canonical value `τ̌₀`, the salted FS oracle `fsChallengeOracle (StmtIn × Salt)`
restricted to reachable keys is in range-preserving bijection with the unsalted
`fsChallengeOracle StmtIn` (key map `(i, (x, τ̌₀), msgs) ↦ (i, x, msgs)`), and
`FSSaltedProof` carries no information beyond `pSpec.Messages`. Pushing both sides of
`KeyLemmaEagerSaltedResidual` through this bijection (a data-processing map applied to
*both* games, hence TV-preserving) recovers the unsalted `KeyLemmaEagerResidual` statement
of `KeyLemmaFoundations` — the bridge back to the original surface, to be formalized as a
separate brick once the salted ladder's step residuals are discharged.

## Proven here (no `sorry`, axiom-clean)

- `canonicalizeChallengeLog_idem` — canonicalization is idempotent.
- `projectLeftQueryLog_canonicalizeChallengeLog` — shared-`oSpec` entries pass through
  canonicalization verbatim and in place.
- `hyb0S_eq_duplexSpongeRemappedEagerSalted` / `hyb4S_eq_basicFiatShamirEagerRandSalted` —
  endpoint identifications (definitional).
- `eagerSimulatedProverSalted_challenge_budget` / `eagerSimulatedProverSalted_shared_budget`
  — witness budgets, directly from the proven `SimulatorBudgets` theorems.
- `keyLemmaEagerSalted_of_steps` — the salted ladder assembly.

## Open core (named `*Residual : Prop`, NOT proven)

- `Hyb01StepResidualS` / `Hyb12StepResidualS` / `Hyb23StepResidualS` / `Hyb34StepResidualS`
  — CO25 Claims 5.21–5.24 on the salted canonicalized surface.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.KeyLemmaSalted

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
open scoped NNReal

/-! ## Challenge-log canonicalization (first-occurrence key-dedup)

CO25 §5.4: the paper's `D2SQuery` is memoless, so paper traces carry one entry per
challenge (re-)derivation, with repeats; the in-tree `tr_i`-memoized realizations are
query-silent on hits. Both shapes have the same *canonical form*: keep `oSpec` entries
verbatim and in place, and keep a challenge entry iff no earlier entry carries the same
challenge key (the answer of the first occurrence wins). Under per-key answer stability
(the memo bricks F6a/F6b + eager tables) the memo-silent and repeat-logged logs of one
execution canonicalize identically, which kills the F1 multiplicity/silence asymmetry. -/

section Canonicalize

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

/-- Worker for `canonicalizeChallengeLog`: `seen` is the set (as a list) of right-summand
(challenge) keys already emitted. Left-summand entries pass through; a right-summand entry
is dropped iff its key is in `seen`, else emitted and its key recorded. -/
def canonicalizeChallengeLogAux [DecidableEq ι₂] :
    List ι₂ → QueryLog (spec₁ + spec₂) → QueryLog (spec₁ + spec₂)
  | _, [] => []
  | seen, ⟨.inl q, r⟩ :: rest =>
      ⟨.inl q, r⟩ :: canonicalizeChallengeLogAux seen rest
  | seen, ⟨.inr q, r⟩ :: rest =>
      if q ∈ seen then canonicalizeChallengeLogAux seen rest
      else ⟨.inr q, r⟩ :: canonicalizeChallengeLogAux (q :: seen) rest

/-- First-occurrence key-dedup of the challenge (right-summand) entries of a mixed query
log: `oSpec` (left-summand) entries are kept verbatim and in place; a challenge entry is
dropped iff an earlier entry carries the same challenge key, the answer being kept from the
first occurrence. This is the line-4 log normal form shared by every salted hybrid below
(see the module docstring, F1). -/
noncomputable def canonicalizeChallengeLog (log : QueryLog (spec₁ + spec₂)) :
    QueryLog (spec₁ + spec₂) :=
  letI : DecidableEq ι₂ := Classical.decEq ι₂
  canonicalizeChallengeLogAux [] log

/-- Worker idempotence: re-running the dedup with the same `seen` set is the identity on
already-deduped logs. -/
lemma canonicalizeChallengeLogAux_idem [DecidableEq ι₂]
    (log : QueryLog (spec₁ + spec₂)) :
    ∀ seen : List ι₂,
      canonicalizeChallengeLogAux (spec₁ := spec₁) (spec₂ := spec₂) seen
          (canonicalizeChallengeLogAux seen log)
        = canonicalizeChallengeLogAux seen log := by
  induction log with
  | nil => intro seen; rfl
  | cons e rest ih =>
      intro seen
      obtain ⟨q, r⟩ := e
      cases q with
      | inl q => simp [canonicalizeChallengeLogAux, ih seen]
      | inr q =>
          by_cases hq : q ∈ seen
          · simp [canonicalizeChallengeLogAux, hq, ih seen]
          · simp [canonicalizeChallengeLogAux, hq, List.mem_cons, ih (q :: seen)]

/-- Canonicalization is idempotent. -/
lemma canonicalizeChallengeLog_idem (log : QueryLog (spec₁ + spec₂)) :
    canonicalizeChallengeLog (spec₁ := spec₁) (spec₂ := spec₂)
        (canonicalizeChallengeLog log)
      = canonicalizeChallengeLog log := by
  letI : DecidableEq ι₂ := Classical.decEq ι₂
  unfold canonicalizeChallengeLog
  exact canonicalizeChallengeLogAux_idem log []

/-- Worker form of the left-projection commutation: dedup never touches left-summand
entries. -/
lemma projectLeftQueryLog_canonicalizeChallengeLogAux [DecidableEq ι₂]
    (log : QueryLog (spec₁ + spec₂)) :
    ∀ seen : List ι₂,
      projectLeftQueryLog
          (canonicalizeChallengeLogAux (spec₁ := spec₁) (spec₂ := spec₂) seen log)
        = projectLeftQueryLog log := by
  induction log with
  | nil => intro seen; rfl
  | cons e rest ih =>
      intro seen
      obtain ⟨q, r⟩ := e
      simp only [projectLeftQueryLog] at ih ⊢
      cases q with
      | inl q =>
          simp only [canonicalizeChallengeLogAux, List.filterMap_cons]
          rw [ih seen]
      | inr q =>
          by_cases hq : q ∈ seen
          · simp only [canonicalizeChallengeLogAux, if_pos hq, List.filterMap_cons]
            rw [ih seen]
          · simp only [canonicalizeChallengeLogAux, if_neg hq, List.filterMap_cons]
            rw [ih (q :: seen)]

/-- Shared-`oSpec` entries pass through canonicalization verbatim and in place: the
left-summand projection of a canonicalized log equals that of the original log. -/
lemma projectLeftQueryLog_canonicalizeChallengeLog (log : QueryLog (spec₁ + spec₂)) :
    projectLeftQueryLog (canonicalizeChallengeLog (spec₁ := spec₁) (spec₂ := spec₂) log)
      = projectLeftQueryLog log := by
  letI : DecidableEq ι₂ := Classical.decEq ι₂
  unfold canonicalizeChallengeLog
  exact projectLeftQueryLog_canonicalizeChallengeLogAux log []

end Canonicalize

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  -- `Codec` (CO25 Def. 4.1) supplies `HasMessageSize`/`HasChallengeSize` and the
  -- `Serialize`/`Deserialize` instances used by the §5.4/§5.5 simulator infrastructure.
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

/-! ## The common salted eager hybrid-game skeleton (CO25 Figure 4 lines 2–4, salted) -/

section Skeleton

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- CO25 §5.8, Figure 4 lines 2–4 on the **salted** eager surface: the salted twin of
`KeyLemmaHybrids.hybGameEager`. Identical lines 2–3 (the prover and the verifier run
through `d2fRaw` with the per-hybrid `gᵢ`-realization, sharing the `tr_i` memo); line 4
pushes both projected logs through a per-hybrid trace map landing on the **salted** FS
surface `fsChallengeOracle (StmtIn × Salt) pSpec` and then applies
`canonicalizeChallengeLog` to both (F1 repair). The output proof is the salted
`FSSaltedProof pSpec Salt` with the canonical pre-encoded salt
`SaltCodec.encode (0^δ)` (see the module docstring's salt convention). -/
noncomputable def hybGameEagerSalted [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ} {M : Type} [Inhabited M] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    (Dχ : OracleDistribution challengeSpec)
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (lineFour : QueryLog (oSpec + challengeSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    ProbComp (Option (StmtIn × StmtOut × FSSaltedProof pSpec Salt
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) := do
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
                  pure (some ⟨stmtIn, stmtOut,
                    (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt)
                      (Vector.replicate δ (0 : U)), messages),
                    canonicalizeChallengeLog pLog', canonicalizeChallengeLog vLog'⟩)
              | _, _ => pure none

/-- The salted eager remapped DSFS game (the `Hyb₀ˢ` carrier): the salted twin of
`KeyLemmaFoundations.duplexSpongeFiatShamirGameRemappedEager`, pushing both logs through
the **salted** §5.5 trace `d2sTraceSalted` — whose remap keys every synthesized entry at
`(stmt, SaltCodec.encode τ̂)` with the BackTrack-recovered (prover-chosen) on-sponge salt,
i.e. the binarized salt stays in the keys — then canonicalizing (F1 repair). Fully
definitional in terms of the in-tree `d2sTraceSalted`; no re-keying residual was needed. -/
noncomputable def duplexSpongeFiatShamirGameRemappedEagerSalted
    [SampleableType U] (δ : ℕ) (Salt : Type) [SaltCodec U δ Salt]
    (Dds : OracleDistribution (duplexSpongeChallengeOracle StmtIn U))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    ProbComp (Option (StmtIn × StmtOut × FSSaltedProof pSpec Salt
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) := do
  let c ← Dds.sample
  let out? ←
    simulateQ (oImpl + Dds.toImpl c)
      (DuplexSpongeFS.duplexSpongeFiatShamirGame (U := U) V P).run
  match out? with
  | none => pure none
  | some ⟨stmtIn, stmtOut, messages, pLog, vLog⟩ => do
      let pLog'? ←
        simulateQ (d2sUnitSampleImpl (U := U))
          ((TraceTransform.d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ)
            (Salt := Salt) (pSpec := pSpec) pLog).run)
      let vLog'? ←
        simulateQ (d2sUnitSampleImpl (U := U))
          ((TraceTransform.d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ)
            (Salt := Salt) (pSpec := pSpec) vLog).run)
      match pLog'?, vLog'? with
      | some pLog', some vLog' =>
          pure (some ⟨stmtIn, stmtOut,
            (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt)
              (Vector.replicate δ (0 : U)), messages),
            canonicalizeChallengeLog pLog', canonicalizeChallengeLog vLog'⟩)
      | _, _ => pure none

end Skeleton

/-! ## The salted `Hyb₄ˢ` endpoint: the eager **salted** basic-FS game (CO25 Constr. 3.17) -/

section SaltedEndpoint

/-- The eager **salted** basic-FS game with a coin-equipped salted witness prover: the
salted twin of `KeyLemmaFoundations.basicFiatShamirGameEagerRand` and the paper-faithful
CO25 endpoint (F3 repair). The FS challenge function is keyed at the augmented statement
`(𝕩, τ̌)` and sampled **once**; the prover `P'` outputs a salted proof
`π̌ = (τ̌, α) : FSSaltedProof pSpec Salt`; the verifier is the single-salt FS transform
`Verifier.singleSaltFiatShamir` (CO25 Construction 3.17) re-deriving challenges at the
proof's salt. Both output logs are canonicalized (F1 repair); the witness's private
`unifSpec` coins are projected out as in the unsalted game. -/
noncomputable def basicFiatShamirGameEagerRandSalted
    (Salt : Type) [VCVCompatible Salt]
    (Df : OracleDistribution (fsChallengeOracle (StmtIn × Salt) pSpec))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P' : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    ProbComp (Option (StmtIn × StmtOut × FSSaltedProof pSpec Salt
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) := do
  let c ← Df.sample
  let realImpl : QueryImpl (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) ProbComp :=
    oImpl + Df.toImpl c
  let coins : QueryImpl unifSpec ProbComp := fun m => (liftM (unifSpec.query m) : ProbComp _)
  let ⟨⟨stmtIn, proof⟩, pLogAll⟩ ←
    simulateQ (realImpl + coins) ((simulateQ loggingOracle P').run)
  let ⟨stmtOut?, vLog⟩ ←
    simulateQ realImpl
      ((simulateQ loggingOracle
        ((V.singleSaltFiatShamir (Salt := Salt)).run stmtIn
          (fun i => match i with | ⟨0, _⟩ => proof))).run)
  match stmtOut? with
  | none => pure none
  | some stmtOut =>
      pure (some ⟨stmtIn, stmtOut, proof,
        canonicalizeChallengeLog (projectLeftQueryLog pLogAll),
        canonicalizeChallengeLog vLog⟩)

end SaltedEndpoint

/-! ## The salted ladder `Hyb₀ˢ … Hyb₄ˢ` (CO25 §5.8) -/

section Ladder

variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- CO25 §5.8 `Hyb₀` on the salted canonicalized surface: the remapped DSFS game with
`(h, p, p⁻¹) ← 𝒟_𝔖` (`D_DS`), logs pushed through the **salted** §5.5 `D2STrace`
(`d2sTraceSalted`: binarized prover-chosen salts in the keys) and canonicalized.
**Definitionally** the right-hand side of `KeyLemmaStatementEagerSalted`. -/
noncomputable def Hyb0S [SampleableType U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × FSSaltedProof pSpec Salt
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) :=
  𝒟[duplexSpongeFiatShamirGameRemappedEagerSalted (T_H := T_H) (T_P := T_P) δ Salt
      (D_DS StmtIn U) oImpl V P]

/-- CO25 §5.8 `Hyb₁` on the salted canonicalized surface: encoded challenge functions
`g ← 𝒟_Σ` (one eager uniform table, CO25 Eq. 15), `gᵢ` realized through the
`tr_i`-memoized forward; line 4 = the **salted** `(φ⁻¹, ψ)` remap `hyb1Line4Trace`
(keys at `(stmt, SaltCodec.encode τ̂)`) + canonicalization. -/
noncomputable def Hyb1S [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × FSSaltedProof pSpec Salt
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) :=
  𝒟[hybGameEagerSalted (T_H := T_H) (T_P := T_P) δ Salt
      (OracleDistribution.uniform (gSpec (U := U) StmtIn pSpec δ))
      (gImplEncodedForwardMemo (StmtIn := StmtIn) (δ := δ) Salt)
      (hyb1Line4Trace (δ := δ) (Salt := Salt)) oImpl V P]

/-- CO25 §5.8 `Hyb₂` on the salted canonicalized surface: decoded challenge functions
`e ← 𝒟_e` (CO25 Eq. 52), `gᵢ` realized as the `tr_i`-memoized `ψᵢ⁻¹ ∘ eᵢ`; line 4 = the
**salted** `φ⁻¹` remap `hyb2Line4Trace` + canonicalization. -/
noncomputable def Hyb2S [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × FSSaltedProof pSpec Salt
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) :=
  𝒟[hybGameEagerSalted (T_H := T_H) (T_P := T_P) δ Salt
      (OracleDistribution.uniform (eSpec (U := U) StmtIn pSpec δ))
      (gImplDecodedChallengeMemo (StmtIn := StmtIn) (δ := δ) Salt)
      (hyb2Line4Trace (δ := δ) (Salt := Salt)) oImpl V P]

/-- CO25 §5.8 `Hyb₃` on the salted canonicalized surface: the **salted** basic-FS
challenge functions `f ← 𝒟_IP` (CO25 Eq. 54 keys `fᵢ` on `(𝕩, τ̌)`), `gᵢ` realized by the
§5.4 Eq. 16 memoized codec bridge `ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` (`d2sCodecBridgeImplMemo`, **no salt
erasure anywhere** — the line-4 map is the identity `hyb3Line4Trace` + canonicalization;
the unsalted ladder's `hyb3Line4SaltErase` is gone, since the output surface itself is now
salted). -/
noncomputable def Hyb3S [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × FSSaltedProof pSpec Salt
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) :=
  𝒟[hybGameEagerSalted (T_H := T_H) (T_P := T_P) δ Salt
      (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec))
      (d2sCodecBridgeImplMemo (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (hyb3Line4Trace (U := U) (Salt := Salt)) oImpl V P]

/-- CO25 §5.8 `Hyb₄` on the salted canonicalized surface: the eager **salted** basic-FS
game with `f ← 𝒟_IP` (the same uniform salted distribution as `Hyb₃ˢ`) against a salted
basic-FS prover `P'`. **Definitionally** the left-hand side of
`KeyLemmaStatementEagerSalted`. -/
noncomputable def Hyb4S
    (Salt : Type) [VCVCompatible Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P' : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    SPMF (Option (StmtIn × StmtOut × FSSaltedProof pSpec Salt
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      × QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) :=
  𝒟[basicFiatShamirGameEagerRandSalted Salt
      (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec)) oImpl V P']

/-- Endpoint identification, right-hand side: `Hyb₀ˢ` **is** the salted remapped eager
DSFS game distribution appearing in `KeyLemmaStatementEagerSalted` (with the canonical
`D_DS` carrier). -/
lemma hyb0S_eq_duplexSpongeRemappedEagerSalted [SampleableType U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    Hyb0S T_H T_P δ Salt oImpl V P
      = 𝒟[duplexSpongeFiatShamirGameRemappedEagerSalted (T_H := T_H) (T_P := T_P) δ Salt
          (D_DS StmtIn U) oImpl V P] := rfl

/-- Endpoint identification, left-hand side: `Hyb₄ˢ` **is** the eager salted basic-FS game
distribution appearing in `KeyLemmaStatementEagerSalted` (with the canonical uniform salted
FS-challenge distribution). -/
lemma hyb4S_eq_basicFiatShamirEagerRandSalted
    (Salt : Type) [VCVCompatible Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P' : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    Hyb4S Salt oImpl V P'
      = 𝒟[basicFiatShamirGameEagerRandSalted Salt
          (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec))
          oImpl V P'] := rfl

end Ladder

/-! ## The witness `P'` for `Hyb₄ˢ`: the non-erasing `D2SAlgo^f` (CO25 §5.4) -/

section Witness

variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [SampleableType U]

/-- The witness `P'` for the **salted** eager key lemma: CO25's `D2SAlgo^f(𝒫̃)` (§5.4
Items 1–6) on the coin-equipped salted witness spec with abort collapsed — i.e. exactly
`KeyLemmaFoundations.simulatedProverSalted` with the canonical coin realization
`coinUnitImpl` and the constant-salt malicious prover `eagerMaliciousProver`. Unlike the
unsalted `eagerSimulatedProver` (`KeyLemmaHybrids`), **no salt-erasing re-keying layer**
(`saltEraseWitnessImpl`) is applied and the output salt is **not** dropped: the witness
outputs the full salted proof `π̌ = (τ̌, α)` over the salted FS oracle, the natural
non-erasing witness (F3 repair). -/
noncomputable def eagerSimulatedProverSalted
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ' : ℕ) (Salt' : Type)
    [SaltCodec U δ' Salt'] [Inhabited (StmtIn × FSSaltedProof pSpec Salt')]
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt') pSpec) + unifSpec)
      (StmtIn × FSSaltedProof pSpec Salt') :=
  simulatedProverSalted (T_H := T_H) (T_P := T_P) (Salt := Salt')
    (coinUnitImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (Salt := Salt'))
    (eagerMaliciousProver (δ := δ') P)

variable {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt]
  [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]

/-- The salted witness satisfies the `θ★` FS-challenge budget — **directly** from the
proven `SimulatorBudgets.simulatedProverChallengeBudget` (M1c), which is stated for the
non-erasing salted witness; no re-keying transfer is needed (contrast
`eagerSimulatedProver_challenge_budget` in `KeyLemmaHybrids`). -/
lemma eagerSimulatedProverSalted_challenge_budget
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ : ℕ)
    (hPerm : IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ) :
    IsQueryBoundP
      (eagerSimulatedProverSalted (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P)
      (fun j => isFSChallengeCoinIdx j = true) (θStar tₕ tₚ tₚᵢ) :=
  SimulatorBudgets.simulatedProverChallengeBudget (oSpec := oSpec) (StmtIn := StmtIn)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
    (coinUnitImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (Salt := Salt))
    (eagerMaliciousProver (δ := δ) P) tₕ tₚ tₚᵢ
    (fun qu => coinUnitImpl_challenge_budget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (Salt := Salt) qu)
    (eagerMaliciousProver_budget (δ := δ) P hPerm)

/-- The salted witness respects the shared-`oSpec` budgets — **directly** from the proven
`SimulatorBudgets.simulatedProverSharedBudget` (M1d); no re-keying transfer is needed. -/
lemma eagerSimulatedProverSalted_shared_budget [DecidableEq ι]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₒ : ι → ℕ)
    (hShared : ∀ i : ι, IsQueryBoundP P (fun j => j.getLeft? = some i) (tₒ i))
    (i : ι) :
    IsQueryBoundP
      (eagerSimulatedProverSalted (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P)
      (fun j => isSharedCoinIdx i j = true) (tₒ i) :=
  SimulatorBudgets.simulatedProverSharedBudget (oSpec := oSpec) (StmtIn := StmtIn)
    (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
    (coinUnitImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (Salt := Salt))
    (eagerMaliciousProver (δ := δ) P) tₒ
    (fun qu i' => coinUnitImpl_shared_budget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (Salt := Salt) qu i')
    (fun i' => eagerMaliciousProver_budget (δ := δ) P (hShared i'))
    i

end Witness

/-! ## The four salted per-step TV-bound obligations (CO25 Claims 5.21–5.24)

Each is a named `*Residual : Prop` (repo convention; never a `sorry`) on the salted
canonicalized surface, with **exactly** the `claim5_2x` bounds of `KeyLemmaFoundations`
(summing to `ηStarPaper` via `claimSum_le_ηStarPaper`). These **supersede** the unsalted
`KeyLemmaHybrids.Hyb01StepResidual` / `Hyb34StepResidual`, which are refuted as stated:
the verifier-log challenge-entry asymmetry (memo-hit silence vs per-round logging) makes
the unsalted 0↔1 and 3↔4 legs false at every `δ` from log shape alone, and the
`saltEraseWitnessImpl` layer of the unsalted `Hyb₄` witness admits a deterministic
salt-grinding distinguisher for `δ ≥ 1` (cross-salt challenge correlation) — the same
definitional-deviation pattern as the refutation records `Lemma58EagerFalse`
(`PaperBadEvents` wave) and `Lemma514ForkFalse`/`Lemma516TimePFalse`; see the issue #314
comments of 2026-06-10 for the full analysis. -/

section StepResiduals

variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- CO25 Claim 5.21 residual, salted surface — `Δ(Hyb₀ˢ, Hyb₁ˢ) ≤ (7T² − 3T)/(2|Σ|^c)`,
`T = tₕ + 1 + tₚ + L + tₚᵢ`: replacing the random permutation by independent encoded
challenge functions costs at most the Lemma 5.8 birthday bound. Both sides now log on the
salted surface with canonicalized challenge entries, so the F1 endpoint asymmetry of the
refuted unsalted `Hyb01StepResidual` (remapped-trace entries vs memo-hit silence) is gone.
Open: the BackTrack chain coupling of CO25 §5.6 off the bad event `E` (Lemmas 5.8–5.10). -/
def Hyb01StepResidualS [SampleableType U]
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
    SPMF.tvDist (Hyb0S T_H T_P δ Salt oImpl V P) (Hyb1S T_H T_P δ Salt oImpl V P)
      ≤ claim5_21Bound U tₕ tₚ tₚᵢ L

/-- CO25 Claim 5.22 residual (Eq. 53), salted surface —
`Δ(Hyb₁ˢ, Hyb₂ˢ) ≤ θ★ · maxᵢ ε_cdc,i + Σᵢ ε_cdc,i`: switching `g` for `ψ⁻¹ ∘ e` costs the
codec decoding bias once per prover-side `gᵢ` query plus once per round for the verifier.
Open: requires `Codec.decode_isBiased` pushed through the simulator. -/
def Hyb12StepResidualS [SampleableType U]
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
    SPMF.tvDist (Hyb1S T_H T_P δ Salt oImpl V P) (Hyb2S T_H T_P δ Salt oImpl V P)
      ≤ claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ codec.decodingBias

/-- CO25 Claim 5.23 residual, salted surface — `Δ(Hyb₂ˢ, Hyb₃ˢ) = 0`: the two hybrids
differ only in the query format of the external oracle (decoded `eᵢ` at raw salted keys vs
salted `fᵢ` behind `φ⁻¹`/`ψ⁻¹`); both keep the salt, both canonicalize, and the memo is
keyed at the encoded salt on both sides, so the induced output distributions are
identical. Open: the table-coupling + pointwise program-equality campaign (the
`SaltCodec.encode_injective`-keyed re-keying spine). -/
def Hyb23StepResidualS [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    SPMF.tvDist (Hyb2S T_H T_P δ Salt oImpl V P) (Hyb3S T_H T_P δ Salt oImpl V P) = 0

/-- CO25 Claim 5.24 residual (Eq. 55), salted surface —
`Δ(Hyb₃ˢ, Hyb₄ˢ) ≤ 7L(2tₕ+2+2tₚ+L+2tₚᵢ)/(2|Σ|^c) − 5(L+1)/|Σ|^c`: both hybrids use the
**same** uniform salted FS distribution; the gap is the genuine verifier-replay asymmetry
(CO25 `E_𝒱`) plus the prover-abort collapse — `Hyb₃ˢ`'s verifier rederives challenges
through `D2SQuery` (and can abort on parse failure), `Hyb₄ˢ`'s single-salt FS verifier
replays the salted transcript directly against `f`. With the salted endpoint and the
canonicalized logs, the F1/F3 falsifiers of the refuted unsalted `Hyb34StepResidual`
(challenge-free vs per-round verifier logs; salt-grinding through `saltEraseWitnessImpl`)
no longer apply; what remains is the CO25 §5.8 replay analysis. Open. -/
def Hyb34StepResidualS [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt] [VCVCompatible Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
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
    SPMF.tvDist (Hyb3S T_H T_P δ Salt oImpl V P)
        (Hyb4S Salt oImpl V
          (eagerSimulatedProverSalted (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
      ≤ claim5_24Bound U tₕ tₚ tₚᵢ L

end StepResiduals

/-! ## The salted eager statement surface and ladder assembly -/

section Assembly

variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- The **salted** repaired key-lemma surface (per-prover): eager-sampled salted oracles
on both sides, coin-equipped salted witness outputting `FSSaltedProof`, canonicalized
challenge logs, paper-exponent error bound `ηStarPaper`. This is the CO25-faithful
statement the salted §5.8 hybrid chain proves; it supersedes the unsalted
`KeyLemmaStatementEager` endpoints (see the module docstring for why the unsalted surface
is refutable as a chain target). -/
def KeyLemmaStatementEagerSalted [SampleableType U]
    [DecidableEq ι]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt] [VCVCompatible Salt]
    (Df : OracleDistribution (fsChallengeOracle (StmtIn × Salt) pSpec))
    (Dds : OracleDistribution (duplexSpongeChallengeOracle StmtIn U))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₒ : ι → ℕ) (tₕ tₚ tₚᵢ L : ℕ) : Prop :=
  ∃ P' : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)
      (StmtIn × FSSaltedProof pSpec Salt),
    (∀ i : ι, IsQueryBoundP P' (fun j => isSharedCoinIdx i j = true) (tₒ i)) ∧
    IsQueryBoundP P' (fun j => isFSChallengeCoinIdx j = true) (θStar tₕ tₚ tₚᵢ) ∧
    SPMF.tvDist
        𝒟[basicFiatShamirGameEagerRandSalted Salt Df oImpl V P']
        𝒟[duplexSpongeFiatShamirGameRemappedEagerSalted (T_H := T_H) (T_P := T_P) δ Salt
            Dds oImpl V P]
      ≤ ηStarPaper (pSpec := pSpec) U tₕ tₚ tₚᵢ L codec.decodingBias

/-- The salted eager key-lemma residual: the full quantified CO25 Lemma 5.1 on the salted
canonicalized surface with the canonical oracle distributions (uniform **salted** FS
challenge functions, `D_DS`). The salted §5.8 ladder (`keyLemmaEagerSalted_of_steps`)
reduces this to the four salted step residuals. The bridge back to the unsalted
`KeyLemmaEagerResidual` is the `δ = 0` recovery plan of the module docstring. -/
def KeyLemmaEagerSaltedResidual [SampleableType U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    [DecidableEq ι]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt] [VCVCompatible Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₒ : ι → ℕ) (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    (∀ i : ι, IsQueryBoundP P (fun j => j.getLeft? = some i) (tₒ i)) →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    KeyLemmaStatementEagerSalted (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
      (StmtOut := StmtOut) δ Salt
      (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec))
      (D_DS StmtIn U) oImpl V P tₒ tₕ tₚ tₚᵢ L

/-- **Salted ladder assembly** (CO25 §5.8, the proof skeleton of Lemma 5.1 on the repaired
surface): the four salted per-step residuals (Claims 5.21–5.24) imply the full salted
eager key lemma `KeyLemmaEagerSaltedResidual`. The witness is `eagerSimulatedProverSalted`
(= CO25's `D2SAlgo^f(𝒫̃)` with abort collapsed, **no** salt erasure); its budgets are
discharged directly by the proven `SimulatorBudgets` theorems (no budget hypotheses are
needed, unlike the unsalted `keyLemmaEager_of_steps`); the distance bound is assembled
with `tvDist_chain4` across `Hyb₀ˢ → Hyb₁ˢ → Hyb₂ˢ → Hyb₃ˢ → Hyb₄ˢ` and closed
numerically by `claimSum_le_ηStarPaper` (Claim 5.23's step contributes exactly `0`). -/
theorem keyLemmaEagerSalted_of_steps
    [DecidableEq ι] [SampleableType U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (Salt : Type) [SaltCodec U δ Salt] [VCVCompatible Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (h01 : Hyb01StepResidualS (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h12 : Hyb12StepResidualS (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h23 : Hyb23StepResidualS (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h34 : Hyb34StepResidualS (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    KeyLemmaEagerSaltedResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl := by
  intro V P tₒ tₕ tₚ tₚᵢ L hL hShared hHash hPerm hPermInv
  refine ⟨eagerSimulatedProverSalted (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P,
    ?_, ?_, ?_⟩
  · -- shared-oSpec budgets of the witness (proven M1d, applied directly)
    intro i
    exact eagerSimulatedProverSalted_shared_budget (δ := δ) (Salt := Salt) T_H T_P P tₒ
      hShared i
  · -- θ★ FS-challenge budget of the witness (proven M1c, applied directly)
    exact eagerSimulatedProverSalted_challenge_budget (δ := δ) (Salt := Salt) T_H T_P P
      tₕ tₚ tₚᵢ hPerm
  · -- the total-variation bound, assembled across the salted ladder
    have hchain :=
      tvDist_chain4
        (Hyb0S T_H T_P δ Salt oImpl V P) (Hyb1S T_H T_P δ Salt oImpl V P)
        (Hyb2S T_H T_P δ Salt oImpl V P)
        (Hyb3S T_H T_P δ Salt oImpl V P)
        (Hyb4S Salt oImpl V
          (eagerSimulatedProverSalted (T_H := T_H) (T_P := T_P) (δ' := δ)
            (Salt' := Salt) P))
        (h01 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
        (h12 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
        (le_of_eq (h23 V P))
        (h34 V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv)
    rw [← hyb4S_eq_basicFiatShamirEagerRandSalted Salt oImpl V
        (eagerSimulatedProverSalted (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P),
      ← hyb0S_eq_duplexSpongeRemappedEagerSalted T_H T_P δ Salt oImpl V P,
      SPMF.tvDist_comm]
    have hsum := claimSum_le_ηStarPaper (pSpec := pSpec) U tₕ tₚ tₚᵢ L codec.decodingBias
    linarith

end Assembly

#print axioms DuplexSpongeFS.KeyLemmaSalted.canonicalizeChallengeLogAux_idem
#print axioms DuplexSpongeFS.KeyLemmaSalted.canonicalizeChallengeLog_idem
#print axioms DuplexSpongeFS.KeyLemmaSalted.projectLeftQueryLog_canonicalizeChallengeLogAux
#print axioms DuplexSpongeFS.KeyLemmaSalted.projectLeftQueryLog_canonicalizeChallengeLog
#print axioms DuplexSpongeFS.KeyLemmaSalted.hyb0S_eq_duplexSpongeRemappedEagerSalted
#print axioms DuplexSpongeFS.KeyLemmaSalted.hyb4S_eq_basicFiatShamirEagerRandSalted
#print axioms DuplexSpongeFS.KeyLemmaSalted.eagerSimulatedProverSalted_challenge_budget
#print axioms DuplexSpongeFS.KeyLemmaSalted.eagerSimulatedProverSalted_shared_budget
#print axioms DuplexSpongeFS.KeyLemmaSalted.keyLemmaEagerSalted_of_steps

end DuplexSpongeFS.KeyLemmaSalted

end
