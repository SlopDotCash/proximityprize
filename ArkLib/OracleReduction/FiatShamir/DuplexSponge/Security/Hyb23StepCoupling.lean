/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23TableComap
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23FreshPath

/-!
# H23-8: the per-query step coupling for Claim 5.23 (issue #316)

Pointwise in the salted table `f`, against deterministic table reads, the two memoized
`gᵢ`-realizations agree at every decode-success key when the `Hyb₂` side reads the
comapped table `f ∘ β`:

* `stepCoupling_hit` — on a `tr_i` memo hit both sides are `pure (some (r, memo))`
  (no oracle interaction), so the simulated runs are equal outright;
* `stepCoupling_miss` — on a miss, both sides reduce (H23-6a normal forms) to
  `table-read >>= ψ⁻¹-sample >>= insert`; the table reads agree by construction of the
  comap (`betaTable`), the `ψ⁻¹` sampler queries only the shared auxiliary summand
  (`simulateQ_sampleFromList_left_agnostic`), and the inserts are the same
  `bridgeMemoEntry`;
* `stepCoupling` — the combined statement, by cases on the lookup.

The memo invariant is plain equality (both realizations share `D2SAlgoMemo`, the key
fields, and the insert), so no memo translation appears. Downstream (H23-9) this is the
per-query atom of the relational `simulateQ` induction through `d2fRaw`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb23Bricks

open TraceTransform ProverTransform DuplexSpongeFS.VerifierReplay DuplexSpongeFS.KeyLemmaHybrids

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U] [Fintype U]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [∀ i, Inhabited (pSpec.Challenge i)]
  {δ : Nat} {Salt : Type} [SaltCodec U δ Salt]

/-- The `e`-table induced by a salted table `f` along the `β` re-keying: decode-success
keys read `f` at their `β`-image; decode-failure keys (never reachable behind the
codec-image guard) answer a default. -/
def betaTable (f : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    OracleFamily (eSpec (U := U) StmtIn pSpec δ) := fun q =>
  if h : (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) q.1 q.2.2.2).isSome then
    f (betaKeyOf (Salt := Salt) ⟨q, h⟩)
  else (default : pSpec.Challenge q.1)

/-- `betaTable` reads `f` at the `β`-image on decode-success keys. -/
lemma betaTable_apply_of_isSome (f : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (q : (eSpec (U := U) StmtIn pSpec δ).Domain)
    (h : (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) q.1 q.2.2.2).isSome) :
    betaTable (δ := δ) f q = f (betaKeyOf (Salt := Salt) ⟨q, h⟩) :=
  dif_pos h

/-- **The `ψ⁻¹` sampler ignores the challenge summand**: simulating `sampleFromList`
through any two composite implementations sharing the auxiliary (unit + coins) summand
gives the same distribution, across different challenge specs. -/
lemma simulateQ_sampleFromList_left_agnostic
    {κ₁ κ₂ : Type} {chA : OracleSpec κ₁} {chB : OracleSpec κ₂} {α : Type}
    (X : QueryImpl chA ProbComp) (X' : QueryImpl chB ProbComp)
    (W : QueryImpl ((Unit →ₒ U) + unifSpec) ProbComp)
    (l : List α) (hl : l ≠ []) (hl' : l ≠ []) :
    simulateQ (X + W) (sampleFromList (U := U) (challengeSpec := chA) l hl)
      = simulateQ (X' + W) (sampleFromList (U := U) (challengeSpec := chB) l hl') := by
  unfold sampleFromList
  simp only [simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inr, simulateQ_pure]
  rfl

/-- The same agnosticism for the full `ψ⁻¹` preimage sampler. -/
lemma simulateQ_uniformDeserializePreimage_left_agnostic
    {κ₁ κ₂ : Type} {chA : OracleSpec κ₁} {chB : OracleSpec κ₂}
    (X : QueryImpl chA ProbComp) (X' : QueryImpl chB ProbComp)
    (W : QueryImpl ((Unit →ₒ U) + unifSpec) ProbComp)
    {i : pSpec.ChallengeIdx} (challenge : pSpec.Challenge i) :
    simulateQ (X + W) (uniformDeserializePreimage (pSpec := pSpec)
        (challengeSpec := chA) challenge)
      = simulateQ (X' + W) (uniformDeserializePreimage (pSpec := pSpec)
        (challengeSpec := chB) challenge) := by
  unfold uniformDeserializePreimage
  exact simulateQ_sampleFromList_left_agnostic X X' W _ _ _

/-- **H23-8, hit case**: on a memo hit both simulated runs are `pure (some (r, memo))`. -/
theorem stepCoupling_hit
    (f : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (W W' : QueryImpl ((Unit →ₒ U) + unifSpec) ProbComp)
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r) :
    simulateQ (tableQueryImpl f + W)
        (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run memo).run)
      = simulateQ (tableQueryImpl (betaTable (Salt := Salt) (δ := δ) f) + W')
        (((gImplDecodedChallengeMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          Salt gq).run memo).run) := by
  rw [d2sCodecBridgeImplMemo_run_hit gq memo r hl,
    gImplDecodedChallengeMemo_run_hit gq memo r hl]
  exact (simulateQ_pure _ _).trans (simulateQ_pure _ _).symm

/-- **H23-8, miss case**: on a memo miss at a decode-success key, both simulated runs are
the same table value followed by the same `ψ⁻¹` sample and the same memo insert. -/
theorem stepCoupling_miss
    (f : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (W : QueryImpl ((Unit →ₒ U) + unifSpec) ProbComp)
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    {mb : pSpec.MessagesUpTo gq.1.1.castSucc}
    (hp : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some mb)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = none) :
    simulateQ (tableQueryImpl f + W)
        (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run memo).run)
      = simulateQ (tableQueryImpl (betaTable (Salt := Salt) (δ := δ) f) + W)
        (((gImplDecodedChallengeMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          Salt gq).run memo).run) := by
  have hsome : (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2).isSome :=
    hp ▸ rfl
  have hkey : (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2).get hsome
      = mb := by simp [hp]
  -- collapse the bridge side to the bare miss chain at the OracleComp level
  have hL : ((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run
      = (query (spec := D2SChallengePlusUnitOracle (U := U)
            (fsChallengeOracle (StmtIn × Salt) pSpec))
          (.inl (betaKey (Salt := Salt) (StmtIn := StmtIn) gq mb)) :
          OracleComp _ (pSpec.Challenge gq.1)) >>= fun challenge =>
        uniformDeserializePreimage (pSpec := pSpec)
            (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) challenge >>=
          fun resp => pure (some (resp, insertD2SAlgoMemo memo
            (bridgeMemoEntry (Salt := Salt) gq resp))) := by
    rw [d2sCodecBridgeImplMemo_run_miss gq memo hl,
      d2sCodecBridgeImpl_run_parse_success (Salt := Salt) gq hp]
    refine (bind_assoc _ _ _).trans ?_
    refine bind_congr fun challenge => ?_
    refine (bind_assoc _ _ _).trans ?_
    refine bind_congr fun resp => ?_
    exact (pure_bind _ _)
  rw [hL, gImplDecodedChallengeMemo_run_miss gq memo hl]
  -- push the simulations through the shared shape
  simp only [bind_pure_comp]
  rw [show (query (spec := D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec))
      (.inl (betaKey (Salt := Salt) (StmtIn := StmtIn) gq mb)) :
      OracleComp _ (pSpec.Challenge gq.1))
    = liftM (OracleSpec.query (Sum.inl (betaKey (Salt := Salt) (StmtIn := StmtIn) gq mb)))
    from rfl]
  rw [show (query (spec := D2SChallengePlusUnitOracle (U := U)
        (eSpec (U := U) StmtIn pSpec δ)) (.inl gq) :
      OracleComp _ (pSpec.Challenge gq.1))
    = liftM (OracleSpec.query (Sum.inl gq)) from rfl]
  refine ((simulateQ_bind _ _ _).trans ?_).trans (Eq.symm (simulateQ_bind _ _ _))
  rw [simulateQ_query, simulateQ_query]
  have hbk : betaTable (Salt := Salt) (δ := δ) f gq
      = f (betaKey (Salt := Salt) (StmtIn := StmtIn) gq mb) := by
    rw [betaTable_apply_of_isSome (Salt := Salt) f gq hsome]
    unfold betaKeyOf
    rw [show (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2).get hsome
      = mb from hkey]
  show ((tableQueryImpl f (betaKey (Salt := Salt) (StmtIn := StmtIn) gq mb)) >>= _)
    = ((tableQueryImpl (betaTable (Salt := Salt) (δ := δ) f) gq) >>= _)
  simp only [tableQueryImpl, hbk]
  refine ((pure_bind _ _).trans ?_).trans (Eq.symm (pure_bind _ _))
  refine ((simulateQ_map _ _ _).trans ?_).trans (Eq.symm (simulateQ_map _ _ _))
  exact congrArg _ (simulateQ_uniformDeserializePreimage_left_agnostic
    (tableQueryImpl f) (tableQueryImpl (betaTable (Salt := Salt) (δ := δ) f)) W _)

/-- **H23-8 — the per-query step coupling**: pointwise in `f`, at every decode-success
key and equal memos, the two memoized realizations simulate identically when `Hyb₂` reads
the comapped table. -/
theorem stepCoupling
    (f : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (W : QueryImpl ((Unit →ₒ U) + unifSpec) ProbComp)
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    {mb : pSpec.MessagesUpTo gq.1.1.castSucc}
    (hp : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some mb)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    simulateQ (tableQueryImpl f + W)
        (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run memo).run)
      = simulateQ (tableQueryImpl (betaTable (Salt := Salt) (δ := δ) f) + W)
        (((gImplDecodedChallengeMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          Salt gq).run memo).run) := by
  cases hlk : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
      (pSpec := pSpec) memo gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r => exact stepCoupling_hit f W W gq memo r hlk
  | none => exact stepCoupling_miss f W gq hp memo hlk

end DuplexSpongeFS.Hyb23Bricks

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.Hyb23Bricks.simulateQ_sampleFromList_left_agnostic
#print axioms DuplexSpongeFS.Hyb23Bricks.stepCoupling_hit
#print axioms DuplexSpongeFS.Hyb23Bricks.stepCoupling_miss
#print axioms DuplexSpongeFS.Hyb23Bricks.stepCoupling
