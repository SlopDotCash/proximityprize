/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.VerifierReplay

/-!
# H23-6a: fresh-path normal forms for the Claim 5.23 coupling (issue #316)

The Claim 5.23 (`Δ(Hyb₂, Hyb₃) = 0`) coupling matches the two memoized `gᵢ`-realizations
query-by-query. `VerifierReplay` already exposes the `Hyb₃` bridge's hit/miss run shapes
(`d2sCodecBridgeImplMemo_run_hit` / `_run_miss`); this module supplies the missing duals:

- `gImplDecodedChallengeMemo_run_hit` / `gImplDecodedChallengeMemo_run_miss` — the `Hyb₂`
  realization's run shapes: a hit is `pure` with the memo untouched; a miss is the decoded
  `eᵢ` query followed by the uniform `ψ⁻¹` preimage sample and the same `bridgeMemoEntry`
  insert.
- `d2sCodecBridgeImpl_run_parse_success` — the raw Eq. 16 bridge on a decode-success key,
  with the parse guard eliminated and the `f`-query exposed at the re-keyed salted key
  `(i, ((𝕩, bin(τ̂)), φ⁻¹(α̂)))` (`Hyb23Bricks.betaKey`, the H23-4' injection): the salted
  `f` query followed by the same uniform `ψ⁻¹` sample.

Together the two miss shapes present both sides of the coupling in the same
`query >>= uniform-preimage >>= insert` form, differing **only** in which table is read
(`e` at the raw key vs `f` at the re-keyed salted key) — exactly the surface on which the
H23-5 uniform-family comap (`evalDist_uniformFamily_comap_injective`) and H23-4'
(`Hyb23Bricks.betaKey_injOn`) apply.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.VerifierReplay

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {δ : ℕ} {Salt : Type} [SaltCodec U δ Salt]

/-! ## The `Hyb₂` realization's run shapes -/

/-- Hit purity for the `Hyb₂` decoded-challenge realization (dual of
`d2sCodecBridgeImplMemo_run_hit`): on a `tr_i` memo hit, no oracle query is made and the
memo is untouched. -/
lemma gImplDecodedChallengeMemo_run_hit
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r) :
    ((gImplDecodedChallengeMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        Salt gq).run memo).run
      = pure (some (r, memo)) := by
  unfold gImplDecodedChallengeMemo
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hl]
  rfl

/-- Miss shape for the `Hyb₂` decoded-challenge realization (dual of
`d2sCodecBridgeImplMemo_run_miss` after `d2sCodecBridgeImpl_run_parse_success`): the
decoded `eᵢ` query at the **raw** key, the uniform `ψ⁻¹` preimage sample, and the
`bridgeMemoEntry` insert. -/
lemma gImplDecodedChallengeMemo_run_miss
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = none) :
    ((gImplDecodedChallengeMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        Salt gq).run memo).run
      = (query (spec := D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (.inl gq) :
          OracleComp (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
            (pSpec.Challenge gq.1)) >>= fun challenge =>
        uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge >>= fun resp =>
          pure (some (resp, insertD2SAlgoMemo memo
            (bridgeMemoEntry (Salt := Salt) gq resp))) := by
  unfold gImplDecodedChallengeMemo
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hl]
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_modify, StateT.run_pure,
    OptionT.run_bind, OptionT.run_lift, bind_assoc, pure_bind]
  rfl

/-! ## The raw bridge on a decode-success key -/

/-- The raw Eq. 16 bridge on a decode-success key, parse guard eliminated: the salted `f`
query at the re-keyed salted key followed by the uniform `ψ⁻¹` sample. Together with
`d2sCodecBridgeImplMemo_run_miss`, this puts the `Hyb₃` miss path in the same
`query >>= uniform-preimage` form as `gImplDecodedChallengeMemo_run_miss`, with the table
read at the `Hyb23Bricks.betaKey` image of `gq` instead of `gq` itself. -/
lemma d2sCodecBridgeImpl_run_parse_success
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    {mb : pSpec.MessagesUpTo gq.1.1.castSucc}
    (hp : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some mb) :
    (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run
      = (query (spec := D2SChallengePlusUnitOracle (U := U)
            (fsChallengeOracle (StmtIn × Salt) pSpec))
          (.inl ⟨gq.1, ((gq.2.1, SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1),
            mb)⟩) :
          OracleComp (D2SChallengePlusUnitOracle (U := U)
            (fsChallengeOracle (StmtIn × Salt) pSpec))
            (pSpec.Challenge gq.1)) >>= fun challenge =>
        uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) challenge >>= fun resp =>
          pure (some resp) := by
  obtain ⟨i, stmt, salt, em⟩ := gq
  unfold d2sCodecBridgeImpl
  simp only [hp, OptionT.run_bind, OptionT.run_lift, bind_assoc, pure_bind]
  rfl

end DuplexSpongeFS.VerifierReplay

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.VerifierReplay.gImplDecodedChallengeMemo_run_hit
#print axioms DuplexSpongeFS.VerifierReplay.gImplDecodedChallengeMemo_run_miss
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImpl_run_parse_success
