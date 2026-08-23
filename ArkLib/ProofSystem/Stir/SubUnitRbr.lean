/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Stir.CheckingVerifier
import ArkLib.ProofSystem.Whir.ThresholdKSF
import ArkLib.OracleReduction.FullPredKSF
import ArkLib.ProofSystem.Whir.SubUnitRbr
import ArkLib.Data.Probability.MarginalBound
import ArkLib.ProofSystem.Component.SendWitness


/-!
# Issue #301 — GENUINE sub-unit RBR knowledge soundness of the STIR checking verifier

This file discharges the named open soundness math of #301, `stirCheckingCABridge`, at an
explicit, genuinely sub-unit budget — by proving the rbr knowledge-soundness residual
OUTRIGHT (`stirCheckingRbrSoundness_genuine`), with **no correlated-agreement residuals, no
bridge hypothesis, and no vacuity**.

**The decisive observation**: the in-tree wire model (`stirMultiVSpec`, single-domain
identity fold, ONE challenge-derived point per binding check) is degenerate relative to
paper-STIR — and in it, the checking verifier's soundness analysis does not need the
BCIKS20 proximity gap at all.  The proximity gap is needed only when folding genuinely
reduces degree (paper-STIR; the #304 `UnifiedProducer` lane remains the route for the
Johnson-regime CA core and the L5.4 budgets, which require the `t`-repetition wire model).

Contents:
1. **`ThresholdKSF.predKSF` / `ThresholdKSF.rbrKnowledgeSoundness_of_flipBounds`** — the
   generic MULTI-FLIP rbr lemma: an un-truncated round-indexed predicate with `hEmpty`,
   direction-conditioned `hConcat`, an explicit `hFull` (acceptance ⟹ predicate at the
   final round), and a per-challenge genuine flip-event bound
   `Pr[¬pred(before) ∧ pred(after the fresh challenge)] ≤ ε i`.  Generalizes
   `rbrKnowledgeSoundness_of_flipBound` (single threshold challenge, `True`-padded) — and is
   exactly the "non-threshold knowledge state function" upgrade that
   `Whir/SubUnitRbr.lean`'s honesty note identifies as the missing piece for consuming the
   salvage-game bounds at sub-unit budgets.
2. **The 'retired-prefix winnable' state predicate** `stirCheckingPred`: the input is
   δ-close, OR (all committed point-checks pass ∧ the fully-committed pair whose binding
   challenge is pending is locked ∧ the last committed message is a codeword).  Seam lemmas:
   `_empty`, `_concat_zero` (fold/shift invariance), `_concat_msg` (no up-flip at prover
   rounds: the pending-pair clause is what defeats the one-point-copy adversary),
   `_full_of_accept` (via `checkingBool_eq_true_iff`; the partial-transcript readers align
   with `checkingBool`'s accessors definitionally), and the flip characterizations
   `_flip_two` / `_flip_out`.
3. **The flip bounds** (the quantitative core, in the exact RBR game shape, mirroring the
   `Whir302SubUnit.probEvent_salvage_game_le` peeling): `stirFlip_le_zero` (fold/shift:
   pointwise-empty event), `stirFlip_le_round2` (input-link binding challenge:
   `(|F| − (⌊δ·|ι|⌋+1))/|F|`, via the disagreement set of the δ-far input against the
   committed first message forced into the code), `stirFlip_le_out` (later pair-binding
   challenges: `(|F|−1)/|F|`).
4. **The discharge**: `stirEpsStar` (the genuine budget), `stirCheckingRbrSoundness_genuine`
   (T1), `stirCheckingCABridge_genuine` (T2 — the named open bridge of #301, a fortiori),
   `stirCheckingIOP_isSecureWithGap_genuine` (the first hypothesis-free `IsSecureWithGap`
   for the assembled STIR IOPP at a non-vacuous budget), and
   `stir_main_of_checkingIOP_genuine` (Theorem 5.1 with the soundness leg proven).

HONESTY NOTES:
* `stirEpsStar` is the model's TRUE security level: the switch prover (send the codeword
  nearest to the δ-far input and echo it) is caught only when the round-2 challenge lands on
  the disagreement set, so the round-2 budget `(|F| − (⌊δ·|ι|⌋+1))/|F|` is essentially tight.
  Consequently `2^{-secpar}` budgets at large `secpar` are NOT achievable in this wire model
  (the `hε` leg of the front door pins `secpar` accordingly); paper-STIR's L5.4 budgets
  require `t`-fold repetition per round, which is the natural next wire-model upgrade.
* The generic multi-flip lemma is now a thin wrapper around the shared home
  `FullPredKSF.rbrKnowledgeSoundness_of_salvageBound` (consolidated; statement kept for
  consumers).
-/


open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal WhirIOP.Construction VectorIOP
open OracleInterface
open scoped ENNReal

noncomputable section

namespace ThresholdKSF

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **Un-truncated predicate knowledge state function**: a round-indexed predicate family
`pred` over partial transcripts that
* agrees with the input relation on the empty transcript (`hEmpty`),
* is stable under removing the last message at every prover round (`hConcat`), and
* is implied at the final round by positive acceptance probability (`hFull`)

is itself a knowledge state function (with `Unit` middle witnesses) for the verifier — no
truncation threshold needed. -/
def predKSF (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hConcat : ∀ (m : Fin n), pSpec.dir m = .P_to_V →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr)
    (hFull : ∀ stmtIn tr (witOut : WitOut),
      Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut
        | OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] > 0 →
      pred (.last n) stmtIn tr) :
    verifier.KnowledgeStateFunction init impl relIn relOut
      (unitExtractor (WitOut := WitOut)) where
  toFun := fun m stmtIn tr _ => pred m stmtIn tr
  toFun_empty := fun stmtIn _w => hEmpty stmtIn _
  toFun_next := fun m hdir stmtIn tr msg _ h => hConcat m hdir stmtIn tr msg h
  toFun_full := fun stmtIn tr witOut h => hFull stmtIn tr witOut h

/-- **Multi-flip RBR knowledge soundness**: if the round-indexed predicate family `pred`
forms an (un-truncated) knowledge state function (hypotheses `hEmpty`, `hConcat`, `hFull`),
and at EVERY challenge round `i` the probability that the prover reaches round `i` with the
predicate false AND the freshly drawn challenge makes it true is at most `ε i` (`hFlip` — the
genuine false→true flip event, supporting sub-unit budgets), then the verifier satisfies RBR knowledge
soundness with the per-challenge budget `ε`. Generalizes
`rbrKnowledgeSoundness_of_flipBound` from a single flip challenge to arbitrary budgets. -/
theorem rbrKnowledgeSoundness_of_flipBounds (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hConcat : ∀ (m : Fin n), pSpec.dir m = .P_to_V →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr)
    (hFull : ∀ stmtIn tr (witOut : WitOut),
      Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut
        | OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] > 0 →
      pred (.last n) stmtIn tr)
    (hFlip : ∀ (i : pSpec.ChallengeIdx) stmtIn witIn
      (prover : Prover oSpec StmtIn Unit StmtOut WitOut pSpec),
      Pr[fun x : pSpec.Transcript i.1.castSucc × pSpec.Challenge i ×
          (oSpec + [pSpec.Challenge]ₒ).QueryLog =>
          ¬ pred i.1.castSucc stmtIn x.1 ∧ pred i.1.succ stmtIn (x.1.concat x.2.1)
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ (ε i : ℝ≥0∞)) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut ε :=
  -- consolidation (#301 dedup): this is `FullPredKSF.rbrKnowledgeSoundness_of_salvageBound`
  -- (the shared multi-flip home) with the flip-bound arguments reordered; the local
  -- `predKSF` shape is preserved for consumers, the proof is no longer duplicated.
  FullPredKSF.rbrKnowledgeSoundness_of_salvageBound init impl verifier relIn relOut pred ε
    hEmpty hConcat hFull (fun stmtIn witIn prover i => hFlip i stmtIn witIn prover)

end ThresholdKSF

namespace StirIOP

namespace MultiRound

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [Nonempty ι]

section Readers

variable {M : ℕ}

/-- Message-round payload length of `stirMultiVSpec` at a raw index. -/
theorem stirMulti_length_msg_raw (k : ℕ) (hk : k < 3 * M + 3) (hmod : k % 3 = 1) :
    Fintype.card ι = (stirMultiVSpec M ι).length ⟨k, hk⟩ := by
  simp [stirVSpec, hmod]

/-- Challenge-round payload length of `stirMultiVSpec` at a raw index. -/
theorem stirMulti_length_chal_raw (k : ℕ) (hk : k < 3 * M + 3) (hmod : k % 3 ≠ 1) :
    (stirMultiVSpec M ι).length ⟨k, hk⟩ = 1 := by
  simp [stirVSpec, hmod]

/-- Challenge-round payload length of `stirMultiVSpec` at a `Fin` index. -/
theorem stirMulti_length_chal (i : Fin (3 * M + 3)) (hmod : (i : ℕ) % 3 ≠ 1) :
    (stirMultiVSpec M ι).length i = 1 := by
  simp [stirVSpec, hmod]

/-- Read the raw vector payload at round `k` from a partial transcript. -/
def trVec {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F))
    (k : ℕ) (hk : k < (m : ℕ)) :
    Vector F ((stirMultiVSpec M ι).length ⟨k, lt_of_lt_of_le hk m.is_le⟩) :=
  tr ⟨k, hk⟩

/-- Read the (unpacked) message function at message round `3j + 1` (raw `ℕ` index `j ≤ M`). -/
def trMsgF {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F))
    (j : ℕ) (h : 3 * j + 1 < (m : ℕ)) : ι → F :=
  fun x => (trVec tr (3 * j + 1) h).get
    (Fin.cast (stirMulti_length_msg_raw _ _ (by omega)) (Fintype.equivFin ι x))

/-- Read the field value of the (length-1) challenge at challenge round `k`. -/
def trChalF {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F))
    (k : ℕ) (hk : k < (m : ℕ)) (hmod : k % 3 ≠ 1) : F :=
  (trVec tr k hk).get ⟨0, by
    rw [stirMulti_length_chal_raw (M := M) (ι := ι) k _ hmod]; omega⟩

/-- Reading strictly below the concatenation point is reading the original transcript. -/
theorem trVec_concat {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (msg : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (k : ℕ) (hk : k < (m.castSucc : ℕ)) (hk' : k < (m.succ : ℕ)) :
    trVec (tr.concat msg) k hk' = trVec tr k hk := by
  exact Fin.snoc_castSucc
    (α := fun j => ((stirMultiVSpec M ι).toProtocolSpec F).Type
      (Fin.castLE m.succ.is_le j)) msg tr ⟨k, hk⟩

/-- Reading at the concatenation point gives the new element. -/
theorem trVec_concat_last {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (msg : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (hk' : (m : ℕ) < (m.succ : ℕ)) :
    trVec (tr.concat msg) (m : ℕ) hk' = msg := by
  exact Fin.snoc_last
    (α := fun j => ((stirMultiVSpec M ι).toProtocolSpec F).Type
      (Fin.castLE m.succ.is_le j)) msg tr

/-- Message reads below the concat point are unchanged. -/
theorem trMsgF_concat {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (msg : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (j : ℕ) (h : 3 * j + 1 < (m.castSucc : ℕ))
    (h' : 3 * j + 1 < (m.succ : ℕ)) :
    trMsgF (tr.concat msg) j h' = trMsgF tr j h := by
  funext x
  unfold trMsgF
  rw [trVec_concat (hk := h)]

/-- Challenge reads below the concat point are unchanged. -/
theorem trChalF_concat {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (msg : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (k : ℕ) (hk : k < (m.castSucc : ℕ)) (hk' : k < (m.succ : ℕ)) (hmod : k % 3 ≠ 1) :
    trChalF (tr.concat msg) k hk' hmod = trChalF tr k hk hmod := by
  unfold trChalF
  congr 1
  rw [trVec_concat (hk := hk)]

end Readers

section Pred

variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)

/-- All point-checks fully committed strictly below round `m` hold: the input-link check `C0`
(committed once `m ≥ 3`), the binding `xa`-checks of pair `j` (committed once `m ≥ 3j+6`), and
the copyable `xb`-checks of pair `j` (committed once `m ≥ 3j+5`, i.e. at the message round of
the second member). -/
def stirChecksBelow (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F)) : Prop :=
  (∀ _ : 3 ≤ (m : ℕ),
    inputAns stmtIn.2 (queryPoint φ (trChalF tr 2 (by omega) (by omega)))
      = trMsgF tr 0 (by omega) (queryPoint φ (trChalF tr 2 (by omega) (by omega)))) ∧
  (∀ j : Fin M, ∀ _ : 3 * (j : ℕ) + 6 ≤ (m : ℕ),
    trMsgF tr (j : ℕ) (by omega)
        (queryPoint φ (trChalF tr (3 * (j : ℕ) + 5) (by omega) (by omega)))
      = trMsgF tr ((j : ℕ) + 1) (by omega)
        (queryPoint φ (trChalF tr (3 * (j : ℕ) + 5) (by omega) (by omega)))) ∧
  (∀ j : Fin M, ∀ _ : 3 * (j : ℕ) + 5 ≤ (m : ℕ),
    trMsgF tr (j : ℕ) (by omega)
        (queryPoint φ (trChalF tr (3 * (j : ℕ) + 3) (by omega) (by omega)))
      = trMsgF tr ((j : ℕ) + 1) (by omega)
        (queryPoint φ (trChalF tr (3 * (j : ℕ) + 3) (by omega) (by omega))))

/-- The unique fully-committed pair whose binding challenge is still pending is locked
(equal everywhere): at `m = 2` the pair is (input, g₁); at `m = 3j+5` it is
(g_{j+1}, g_{j+2}). -/
def stirPendingLocked (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F)) : Prop :=
  (∀ _ : (m : ℕ) = 2, ∀ x : ι,
    inputAns stmtIn.2 x = trMsgF tr 0 (by omega) x) ∧
  (∀ j : Fin M, ∀ _ : (m : ℕ) = 3 * (j : ℕ) + 5, ∀ x : ι,
    trMsgF tr (j : ℕ) (by omega) x
      = trMsgF tr ((j : ℕ) + 1) (by omega) x)

/-- The last committed message is a Reed–Solomon codeword (the input function itself when no
message has been sent). -/
def stirLastInRS (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F)) : Prop :=
  ((m : ℕ) ≤ 1 → stmtIn.2 () ∈ ReedSolomon.code φ deg) ∧
  (∀ j : ℕ, ∀ h1 : 3 * j + 1 < (m : ℕ), (m : ℕ) ≤ 3 * j + 4 →
    trMsgF tr j h1 ∈ ReedSolomon.code φ deg)

/-- **The 'retired-prefix winnable' state**: all committed checks pass, the pending
fully-committed pair (if any) is locked, and the last committed message is a codeword. -/
def stirWinnable (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F)) : Prop :=
  stirChecksBelow M φ m stmtIn tr ∧ stirPendingLocked M m stmtIn tr ∧
    stirLastInRS M φ deg m stmtIn tr

/-- **The checking-verifier state predicate** (#301): the input is δ-close, or the partial
transcript is in the winnable state. -/
def stirCheckingPred (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F)) : Prop :=
  ((stmtIn, ()) ∈ stirRelation deg φ δ) ∨ stirWinnable M φ deg m stmtIn tr

-- defeq probes
example (oStmt : ∀ i, OracleStatement ι F i) (x : ι) :
    inputAns oStmt x = (oStmt ()) x := rfl

/-- A codeword is at relative distance ≤ δ from the code. -/
theorem relDist_le_of_mem {u : ι → F} (hu : u ∈ ReedSolomon.code φ deg) :
    δᵣ(u, (ReedSolomon.code φ deg : Set (ι → F))) ≤ (δ : ℝ≥0∞) := by
  refine le_trans (Code.relDistFromCode_le_relDist_to_mem u u hu) ?_
  have h0 : Code.relHammingDist u u = 0 := by
    simp [Code.relHammingDist, hammingDist_self]
  rw [h0, ← ENNReal.coe_nnratCast]
  norm_num

/-- Seam lemma `hEmpty`: the predicate at round 0 is input-relation membership. -/
theorem stirCheckingPred_empty (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript 0 ((stirMultiVSpec M ι).toProtocolSpec F)) :
    (stmtIn, ()) ∈ stirRelation deg φ δ ↔ stirCheckingPred M φ deg δ 0 stmtIn tr := by
  constructor
  · intro h; exact Or.inl h
  · rintro (h | ⟨_, _, hlast, _⟩)
    · exact h
    · exact relDist_le_of_mem φ deg δ (hlast (by simp))

/-- Reading the challenge AT the concatenation point gives the new element's field value. -/
theorem trChalF_concat_last {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (c : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (hk' : (m : ℕ) < (m.succ : ℕ)) (hmod : (m : ℕ) % 3 ≠ 1) :
    trChalF (tr.concat c) (m : ℕ) hk' hmod
      = c.get ⟨0, by rw [stirMulti_length_chal (M := M) (ι := ι) m hmod]; omega⟩ := by
  unfold trChalF
  congr 1
  exact trVec_concat_last tr c hk'

/-- **Uniform down-transport of committed checks**: every check committed below `m` is
committed below `m+1`, and its reads sit strictly below `m`, so they are unchanged by the
concatenation. Holds for EVERY round (message or challenge). -/
theorem stirChecksBelow_concat {m : Fin (3 * M + 3)}
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (msg : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (h : stirChecksBelow M φ m.succ stmtIn (tr.concat msg)) :
    stirChecksBelow M φ m.castSucc stmtIn tr := by
  obtain ⟨h0, ha, hb⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro h3
    simp only [Fin.val_castSucc] at h3
    have := h0 (by simp only [Fin.val_succ]; omega)
    rwa [trChalF_concat tr msg 2 (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega) (by omega),
      trMsgF_concat tr msg 0 (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at this
  · intro j hj
    simp only [Fin.val_castSucc] at hj
    have := ha j (by simp only [Fin.val_succ]; omega)
    rwa [trChalF_concat tr msg (3 * (j : ℕ) + 5) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega) (by omega),
      trMsgF_concat tr msg (j : ℕ) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega),
      trMsgF_concat tr msg ((j : ℕ) + 1) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at this
  · intro j hj
    simp only [Fin.val_castSucc] at hj
    have := hb j (by simp only [Fin.val_succ]; omega)
    rwa [trChalF_concat tr msg (3 * (j : ℕ) + 3) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega) (by omega),
      trMsgF_concat tr msg (j : ℕ) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega),
      trMsgF_concat tr msg ((j : ℕ) + 1) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at this

/-- **No up-flip at the fold and shift challenges**: the predicate at `m+1` on the extended
transcript implies the predicate at `m` (round value `≡ 0 mod 3`). -/
theorem stirCheckingPred_concat_zero {m : Fin (3 * M + 3)}
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (c : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (hmod : (m : ℕ) % 3 = 0)
    (h : stirCheckingPred M φ deg δ m.succ stmtIn (tr.concat c)) :
    stirCheckingPred M φ deg δ m.castSucc stmtIn tr := by
  rcases h with h | ⟨hchk, hpend, hlast⟩
  · exact Or.inl h
  refine Or.inr ⟨stirChecksBelow_concat M φ stmtIn tr c hchk, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h2; exfalso; simp only [Fin.val_castSucc] at h2; omega
  · intro j h5; exfalso; simp only [Fin.val_castSucc] at h5; omega
  · intro h1
    simp only [Fin.val_castSucc] at h1
    exact hlast.1 (by simp only [Fin.val_succ]; omega)
  · intro j h1 h2
    simp only [Fin.val_castSucc] at h1 h2
    have := hlast.2 j (by simp only [Fin.val_succ]; omega)
      (by simp only [Fin.val_succ]; omega)
    rwa [trMsgF_concat tr c j (by simp only [Fin.val_castSucc]; omega)
      (by simp only [Fin.val_succ]; omega)] at this

/-- **No up-flip at message rounds** (`toFun_next` seam): the predicate at `m+1` on the
extended transcript implies the predicate at `m`, when round `m` is a prover message. -/
theorem stirCheckingPred_concat_msg {m : Fin (3 * M + 3)}
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (msg : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (hmod : (m : ℕ) % 3 = 1)
    (h : stirCheckingPred M φ deg δ m.succ stmtIn (tr.concat msg)) :
    stirCheckingPred M φ deg δ m.castSucc stmtIn tr := by
  rcases h with h | ⟨hchk, hpend, hlast⟩
  · exact Or.inl h
  by_cases hm1 : (m : ℕ) = 1
  · -- g₁ has just been sent: the source pending pair (input, g₁) is locked and g₁ ∈ code,
    -- hence the input itself is a codeword and the LEFT disjunct holds at the target.
    refine Or.inl ?_
    have hpend1 := hpend.1 (by simp only [Fin.val_succ]; omega)
    have hlast1 := hlast.2 0 (by simp only [Fin.val_succ]; omega)
      (by simp only [Fin.val_succ]; omega)
    have hf : stmtIn.2 () = trMsgF (tr.concat msg) 0
        (by simp only [Fin.val_succ]; omega) := by
      funext x; exact hpend1 x
    show δᵣ(stmtIn.2 (), (ReedSolomon.code φ deg : Set (ι → F))) ≤ (δ : ℝ≥0∞)
    exact relDist_le_of_mem φ deg δ (by rw [hf]; exact hlast1)
  · -- a later message g_{j+2} (round 3j+4): the source pending pair (g_{j+1}, g_{j+2})
    -- is locked and g_{j+2} ∈ code, hence g_{j+1} ∈ code is the target's last-in-code fact.
    refine Or.inr ⟨stirChecksBelow_concat M φ stmtIn tr msg hchk, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro h2; exfalso; simp only [Fin.val_castSucc] at h2; omega
    · intro j h5; exfalso; simp only [Fin.val_castSucc] at h5; omega
    · intro h1; exfalso; simp only [Fin.val_castSucc] at h1; omega
    · intro j h1 h2
      simp only [Fin.val_castSucc] at h1 h2
      -- here (m : ℕ) = 3j + 4 for THIS j (the window pins it)
      have hmj : (m : ℕ) = 3 * j + 4 := by omega
      have hjM : j < M := by have := m.isLt; omega
      have hpend2 := hpend.2 ⟨j, hjM⟩ (by simp only [Fin.val_succ]; omega)
      have hlast2 := hlast.2 (j + 1) (by simp only [Fin.val_succ]; omega)
        (by simp only [Fin.val_succ]; omega)
      have hEq : trMsgF (tr.concat msg) j
          (by simp only [Fin.val_succ]; omega)
            = trMsgF (tr.concat msg) (j + 1) (by simp only [Fin.val_succ]; omega) := by
        funext x; exact hpend2 x
      have hmem : trMsgF (tr.concat msg) j (by simp only [Fin.val_succ]; omega)
          ∈ ReedSolomon.code φ deg := by rw [hEq]; exact hlast2
      rwa [trMsgF_concat tr msg j (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at hmem

/-- `getD` of a mapped `finRange` at an in-range index. -/
theorem listGetD_finRange_map {n : ℕ} (f : Fin n → F) (i : ℕ) (h : i < n) :
    (((List.finRange n).map f).getD i 0) = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
  simp [List.getElem_map, List.getElem_finRange]

/-- Generalized `trChalF_concat_last` with the round value abstracted. -/
theorem trChalF_concat_last' {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (c : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (k : ℕ) (hkm : k = (m : ℕ)) (hk' : k < (m.succ : ℕ)) (hmod : k % 3 ≠ 1) :
    trChalF (tr.concat c) k hk' hmod
      = c.get ⟨0, by
          subst hkm
          rw [stirMulti_length_chal (M := M) (ι := ι) m hmod]; omega⟩ := by
  subst hkm
  exact trChalF_concat_last M tr c hk' hmod

/-- **Acceptance forces the predicate at the final round** (`toFun_full` seam). -/
theorem stirCheckingPred_full_of_accept
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript (Fin.last (3 * M + 3)) ((stirMultiVSpec M ι).toProtocolSpec F))
    (hacc : checkingBool M φ deg stmtIn.2
      (FullTranscript.messages (pSpec := (stirMultiVSpec M ι).toProtocolSpec F) tr)
      (FullTranscript.challenges (pSpec := (stirMultiVSpec M ι).toProtocolSpec F) tr)
      = true) :
    stirCheckingPred M φ deg δ (Fin.last (3 * M + 3)) stmtIn tr := by
  obtain ⟨h0, hcons, hfin⟩ := (checkingBool_eq_true_iff (M := M) (φ := φ) (deg := deg) stmtIn.2 _ _).mp hacc
  refine Or.inr ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro _
    exact h0
  · intro j _
    exact (hcons j).1
  · intro j _
    exact (hcons j).2
  · intro h2; exfalso; simp only [Fin.val_last] at h2; omega
  · intro j h5; exfalso; simp only [Fin.val_last] at h5; omega
  · intro h1; exfalso; simp only [Fin.val_last] at h1; omega
  · intro j h1 h2
    simp only [Fin.val_last] at h1 h2
    have hjM : M = j := by omega
    subst hjM
    have hbridge : (fun x : ι =>
        (((List.finRange (Fintype.card ι)).map (fun k =>
          msgAns (FullTranscript.messages (pSpec := (stirMultiVSpec M ι).toProtocolSpec F) tr)
            (msgIdx M (Fin.last M))
            (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))).getD
          ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0))
        = trMsgF tr M h1 := by
      funext x
      rw [listGetD_finRange_map
        (fun k => msgAns (FullTranscript.messages
            (pSpec := (stirMultiVSpec M ι).toProtocolSpec F) tr)
          (msgIdx M (Fin.last M))
          (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))
        ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) (Fin.isLt _)]
      rfl
    rw [← hbridge]
    exact hfin

/-- **Flip characterization at the round-2 challenge**: a genuine flip forces the input to be
δ-far, the first message to be a codeword, and the input-link check to pass at the freshly
drawn challenge point. -/
theorem stirCheckingPred_flip_two {m : Fin (3 * M + 3)} (hm : (m : ℕ) = 2)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (c : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (hno : ¬ stirCheckingPred M φ deg δ m.castSucc stmtIn tr)
    (hyes : stirCheckingPred M φ deg δ m.succ stmtIn (tr.concat c)) :
    ¬ ((stmtIn, ()) ∈ stirRelation deg φ δ) ∧
    trMsgF tr 0 (by simp only [Fin.val_castSucc]; omega) ∈ ReedSolomon.code φ deg ∧
    inputAns stmtIn.2 (queryPoint φ
        (c.get ⟨0, by rw [stirMulti_length_chal (M := M) (ι := ι) m (by omega)]; omega⟩))
      = trMsgF tr 0 (by simp only [Fin.val_castSucc]; omega) (queryPoint φ
        (c.get ⟨0, by rw [stirMulti_length_chal (M := M) (ι := ι) m (by omega)]; omega⟩)) := by
  have hrel : ¬ ((stmtIn, ()) ∈ stirRelation deg φ δ) := fun h => hno (Or.inl h)
  rcases hyes with h | ⟨hchk, _, hlast⟩
  · exact absurd h hrel
  refine ⟨hrel, ?_, ?_⟩
  · -- last-in-code at the source window j = 0, transported below the concat point
    have := hlast.2 0 (by simp only [Fin.val_succ]; omega) (by simp only [Fin.val_succ]; omega)
    rwa [trMsgF_concat tr c 0 (by simp only [Fin.val_castSucc]; omega)
      (by simp only [Fin.val_succ]; omega)] at this
  · -- the committed C0 check, with the challenge read rewritten to the fresh element
    have hC0 := hchk.1 (by simp only [Fin.val_succ]; omega)
    rwa [trChalF_concat_last' M tr c 2 hm.symm (by simp only [Fin.val_succ]; omega) (by omega),
      trMsgF_concat tr c 0 (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at hC0

/-- **Flip characterization at a later out-challenge** (round `3j+5`): a genuine flip forces
the committed pair to differ somewhere while agreeing at the freshly drawn challenge point. -/
theorem stirCheckingPred_flip_out {m : Fin (3 * M + 3)} {j : ℕ} (hjM : j < M)
    (hm : (m : ℕ) = 3 * j + 5)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (c : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (hno : ¬ stirCheckingPred M φ deg δ m.castSucc stmtIn tr)
    (hyes : stirCheckingPred M φ deg δ m.succ stmtIn (tr.concat c)) :
    (∃ x : ι, trMsgF tr j (by simp only [Fin.val_castSucc]; omega) x
      ≠ trMsgF tr (j + 1) (by simp only [Fin.val_castSucc]; omega) x) ∧
    trMsgF tr j (by simp only [Fin.val_castSucc]; omega) (queryPoint φ
        (c.get ⟨0, by rw [stirMulti_length_chal (M := M) (ι := ι) m (by omega)]; omega⟩))
      = trMsgF tr (j + 1) (by simp only [Fin.val_castSucc]; omega) (queryPoint φ
        (c.get ⟨0, by rw [stirMulti_length_chal (M := M) (ι := ι) m (by omega)]; omega⟩)) := by
  have hrel : ¬ ((stmtIn, ()) ∈ stirRelation deg φ δ) := fun h => hno (Or.inl h)
  rcases hyes with h | ⟨hchk, hpend, hlast⟩
  · exact absurd h hrel
  constructor
  · -- if the pair agreed everywhere, the source state would already be winnable
    by_contra hcon
    push_neg at hcon
    refine hno (Or.inr ⟨stirChecksBelow_concat M φ stmtIn tr c hchk, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩)
    · intro h2; exfalso; simp only [Fin.val_castSucc] at h2; omega
    · intro j' hj'
      simp only [Fin.val_castSucc] at hj'
      have hjj : (j' : ℕ) = j := by omega
      intro x
      simp only [hjj]
      exact hcon x
    · intro h1; exfalso; simp only [Fin.val_castSucc] at h1; omega
    · intro j'' h1 h2
      simp only [Fin.val_castSucc] at h1 h2
      have hj'' : j'' = j + 1 := by omega
      subst hj''
      have := hlast.2 (j + 1) (by simp only [Fin.val_succ]; omega)
        (by simp only [Fin.val_succ]; omega)
      rwa [trMsgF_concat tr c (j + 1) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at this
  · -- the committed xa check at pair j, with the challenge read rewritten to the fresh element
    have hxa := hchk.2.1 ⟨j, hjM⟩ (by simp only [Fin.val_succ]; omega)
    rwa [trChalF_concat_last' M tr c (3 * j + 5) hm.symm (by simp only [Fin.val_succ]; omega)
        (by omega),
      trMsgF_concat tr c j (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega),
      trMsgF_concat tr c (j + 1) (by simp only [Fin.val_castSucc]; omega)
        (by simp only [Fin.val_succ]; omega)] at hxa


section FlipBounds

open Whir302SubUnit

variable {ιo : Type} {oSpec : OracleSpec ιo} {σ : Type}
variable {StmtOut WitOut : Type}
variable [∀ i, SampleableType ((((stirMultiVSpec M ι)).toProtocolSpec F).Challenge i)]

/-- **Zero flip probability at the fold and shift challenges** (rounds `≡ 0 mod 3`): the
predicate is invariant across these challenges, so the flip event is pointwise empty. -/
theorem stirFlip_le_zero
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (i : ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx) (hi : (i.1 : ℕ) % 3 = 0)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (witIn : Unit)
    (prover : Prover oSpec (Unit × ∀ i, OracleStatement ι F i) Unit StmtOut WitOut
      ((stirMultiVSpec M ι).toProtocolSpec F)) :
    Pr[fun x : ((stirMultiVSpec M ι).toProtocolSpec F).Transcript i.1.castSucc ×
          ((stirMultiVSpec M ι).toProtocolSpec F).Challenge i ×
          (oSpec + [((stirMultiVSpec M ι).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).QueryLog =>
        ¬ stirCheckingPred M φ deg δ i.1.castSucc stmtIn x.1 ∧
          stirCheckingPred M φ deg δ i.1.succ stmtIn (x.1.concat x.2.1)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp
              (((stirMultiVSpec M ι).toProtocolSpec F).getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      ≤ (0 : ℝ≥0∞) := by
  refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
  rintro ⟨tr, ch, lg⟩ _ ⟨hn, hy⟩
  exact hn (stirCheckingPred_concat_zero M φ deg δ stmtIn tr ch hi hy)

/-- **The round-2 flip bound**: the flip probability at the input-link binding challenge is at
most `(|F| − (⌊δ·|ι|⌋ + 1)) / |F|` — genuinely sub-unit, the model's true security level. -/
theorem stirFlip_le_round2
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (i : ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx) (hi : (i.1 : ℕ) = 2)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (witIn : Unit)
    (prover : Prover oSpec (Unit × ∀ i, OracleStatement ι F i) Unit StmtOut WitOut
      ((stirMultiVSpec M ι).toProtocolSpec F)) :
    Pr[fun x : ((stirMultiVSpec M ι).toProtocolSpec F).Transcript i.1.castSucc ×
          ((stirMultiVSpec M ι).toProtocolSpec F).Challenge i ×
          (oSpec + [((stirMultiVSpec M ι).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).QueryLog =>
        ¬ stirCheckingPred M φ deg δ i.1.castSucc stmtIn x.1 ∧
          stirCheckingPred M φ deg δ i.1.succ stmtIn (x.1.concat x.2.1)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp
              (((stirMultiVSpec M ι).toProtocolSpec F).getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      ≤ ((Fintype.card F - (⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := by
  classical
  have hmod : (i.1 : ℕ) % 3 ≠ 1 := by omega
  -- peel the init draw
  refine probEvent_bind_le_of_forall_support init _ _ _ (fun s _ => ?_)
  -- distribute the simulation over the prefix bind
  rw [simulateQ_bind, StateT.run'_bind_lib]
  -- peel the prover prefix
  refine probEvent_bind_le_of_forall_support _ _ _ _ (fun rk _ => ?_)
  obtain ⟨⟨⟨tr, pst⟩, log⟩, s'⟩ := rk
  dsimp only
  -- the challenge draw in `liftM` form, then the uniform average over the drawn challenge
  rw [liftComp_eq_liftM]
  rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind impl s' i
    (fun ch => pure (tr, ch, log)) _]
  simp only [simulateQ_pure, StateT.run'_pure_lib]
  rw [← probEvent_bind_eq_tsum]
  -- case analysis at the fixed prefix
  by_cases hno : stirCheckingPred M φ deg δ i.1.castSucc stmtIn tr
  · -- the state is already good: no flip possible
    refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
    rintro x hx ⟨hn, -⟩
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hx
    obtain ⟨ch, -, rfl⟩ := hx
    exact hn hno
  · by_cases hrel : (stmtIn, ()) ∈ stirRelation deg φ δ
    · exact absurd (Or.inl hrel) hno
    · have h1 : 3 * 0 + 1 < (i.1.castSucc : ℕ) := by
        simp only [Fin.val_castSucc]; omega
      by_cases hg : trMsgF tr 0 h1 ∈ ReedSolomon.code φ deg
      · -- the genuine bound: the check point must avoid the disagreement set
        set f : ι → F := stmtIn.2 () with hf
        set g1 : ι → F := trMsgF tr 0 h1 with hg1
        -- the disagreement set is large: δ·|ι| < |D|
        have hfar : (δ : ℝ≥0∞) < δᵣ(f, (ReedSolomon.code φ deg : Set (ι → F))) :=
          not_le.mp (fun hle => hrel hle)
        have hle : δᵣ(f, (ReedSolomon.code φ deg : Set (ι → F)))
            ≤ ((Code.relHammingDist f g1 : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_nnratCast]
          exact Code.relDistFromCode_le_relDist_to_mem f g1 hg
        have hδrel : δ < (Code.relHammingDist f g1 : ℝ≥0) := by
          exact_mod_cast lt_of_lt_of_le hfar hle
        set D : Finset ι := Finset.univ.filter (fun x => f x ≠ g1 x) with hD
        have hham : hammingDist f g1 = D.card := rfl
        have hcard : δ * (Fintype.card ι : ℝ≥0) < (D.card : ℝ≥0) := by
          have hn : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
            exact_mod_cast Fintype.card_pos
          have hrw : (Code.relHammingDist f g1 : ℝ≥0)
              = (D.card : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
            rw [Code.relHammingDist, hham]
            push_cast
            ring
          rw [hrw] at hδrel
          calc δ * (Fintype.card ι : ℝ≥0)
              < ((D.card : ℝ≥0) / (Fintype.card ι : ℝ≥0)) * (Fintype.card ι : ℝ≥0) :=
                mul_lt_mul_of_pos_right hδrel hn
            _ = (D.card : ℝ≥0) := div_mul_cancel₀ _ (ne_of_gt hn)
        have hfloor : ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ D.card := by
          have := (Nat.floor_lt (zero_le _)).mpr hcard
          omega
        -- the agreement set of challenge values
        set L : Set F := {r : F | inputAns stmtIn.2 (queryPoint φ r)
          = trMsgF tr 0 h1 (queryPoint φ r)} with hL
        refine le_trans (probEvent_bind_le_uniform_marginal_comap
          ($ᵗ (((stirMultiVSpec M ι).toProtocolSpec F).Challenge i))
          (chalElemOf (stirMultiVSpec M ι) i)
          (fun ch => pure (tr, ch, log)) _ L
          (fun x => le_of_eq (probEvent_chalElemOf_eq_uniform (stirMultiVSpec M ι) i
            (stirMulti_length_chal (M := M) (ι := ι) i.1 hmod) x)) ?_) ?_
        · -- outside the agreement set the flip event is impossible
          intro ch hch
          refine probEvent_eq_zero ?_
          rintro x hx ⟨hn, hy⟩
          simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx
          have hflip := stirCheckingPred_flip_two M φ deg δ (m := i.1) hi stmtIn tr ch hn hy
          refine hch ?_
          show inputAns stmtIn.2 (queryPoint φ (chalElemOf (stirMultiVSpec M ι) i ch))
            = trMsgF tr 0 h1 (queryPoint φ (chalElemOf (stirMultiVSpec M ι) i ch))
          have hread : chalElemOf (stirMultiVSpec M ι) i ch
              = ch.get ⟨0, by
                  rw [stirMulti_length_chal (M := M) (ι := ι) i.1 hmod]; omega⟩ := by
            rw [chalElemOf, dif_pos]
          rw [hread]
          exact hflip.2.2
        · -- the agreement set avoids the φ-image of the disagreement set
          have hsub : (Finset.univ.filter (· ∈ L)) ⊆ (D.image φ)ᶜ := by
            intro r hr
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
            rw [Finset.mem_compl]
            intro hmem
            obtain ⟨x, hxD, rfl⟩ := Finset.mem_image.mp hmem
            have hqp : queryPoint φ (φ x) = x :=
              Function.leftInverse_invFun φ.injective x
            have hLx := hr
            rw [hL] at hLx
            simp only [Set.mem_setOf_eq, hqp] at hLx
            have hfx : f x ≠ g1 x := by
              simpa [hD] using hxD
            exact hfx hLx
          have hcardL : (Finset.univ.filter (· ∈ L)).card
              ≤ Fintype.card F - (⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ + 1) := by
            refine le_trans (Finset.card_le_card hsub) ?_
            rw [Finset.card_compl, Finset.card_image_of_injective _ φ.injective]
            omega
          exact ENNReal.div_le_div_right (by exact_mod_cast hcardL) _
      · -- the first message is not a codeword: the flip event is impossible
        refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
        rintro x hx ⟨hn, hy⟩
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          exists_prop] at hx
        obtain ⟨ch, -, rfl⟩ := hx
        exact hg (stirCheckingPred_flip_two M φ deg δ (m := i.1) hi stmtIn tr ch hn hy).2.1

/-- **The later out-challenge flip bound**: the flip probability at the pair binding challenge
of round `3j+5` is at most `(|F| − 1) / |F|`. -/
theorem stirFlip_le_out
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (i : ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx)
    (j : ℕ) (hjM : j < M) (hi : (i.1 : ℕ) = 3 * j + 5)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (witIn : Unit)
    (prover : Prover oSpec (Unit × ∀ i, OracleStatement ι F i) Unit StmtOut WitOut
      ((stirMultiVSpec M ι).toProtocolSpec F)) :
    Pr[fun x : ((stirMultiVSpec M ι).toProtocolSpec F).Transcript i.1.castSucc ×
          ((stirMultiVSpec M ι).toProtocolSpec F).Challenge i ×
          (oSpec + [((stirMultiVSpec M ι).toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).QueryLog =>
        ¬ stirCheckingPred M φ deg δ i.1.castSucc stmtIn x.1 ∧
          stirCheckingPred M φ deg δ i.1.succ stmtIn (x.1.concat x.2.1)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp
              (((stirMultiVSpec M ι).toProtocolSpec F).getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  have hmod : (i.1 : ℕ) % 3 ≠ 1 := by omega
  refine probEvent_bind_le_of_forall_support init _ _ _ (fun s _ => ?_)
  rw [simulateQ_bind, StateT.run'_bind_lib]
  refine probEvent_bind_le_of_forall_support _ _ _ _ (fun rk _ => ?_)
  obtain ⟨⟨⟨tr, pst⟩, log⟩, s'⟩ := rk
  dsimp only
  rw [liftComp_eq_liftM]
  rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind impl s' i
    (fun ch => pure (tr, ch, log)) _]
  simp only [simulateQ_pure, StateT.run'_pure_lib]
  rw [← probEvent_bind_eq_tsum]
  by_cases hno : stirCheckingPred M φ deg δ i.1.castSucc stmtIn tr
  · refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
    rintro x hx ⟨hn, -⟩
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hx
    obtain ⟨ch, -, rfl⟩ := hx
    exact hn hno
  · have hA : 3 * j + 1 < (i.1.castSucc : ℕ) := by simp only [Fin.val_castSucc]; omega
    have hB : 3 * (j + 1) + 1 < (i.1.castSucc : ℕ) := by simp only [Fin.val_castSucc]; omega
    by_cases hAB : ∀ x : ι, trMsgF tr j hA x = trMsgF tr (j + 1) hB x
    · -- the pair is locked: no flip is possible (the source state would be winnable)
      refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
      rintro x hx ⟨hn, hy⟩
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
        exists_prop] at hx
      obtain ⟨ch, -, rfl⟩ := hx
      obtain ⟨⟨x₀, hx₀⟩, -⟩ :=
        stirCheckingPred_flip_out M φ deg δ (m := i.1) hjM hi stmtIn tr ch hn hy
      exact hx₀ (hAB x₀)
    · obtain ⟨x₀, hx₀⟩ := not_forall.mp hAB
      set L : Set F := {r : F | trMsgF tr j hA (queryPoint φ r)
        = trMsgF tr (j + 1) hB (queryPoint φ r)} with hL
      refine le_trans (probEvent_bind_le_uniform_marginal_comap
        ($ᵗ (((stirMultiVSpec M ι).toProtocolSpec F).Challenge i))
        (chalElemOf (stirMultiVSpec M ι) i)
        (fun ch => pure (tr, ch, log)) _ L
        (fun x => le_of_eq (probEvent_chalElemOf_eq_uniform (stirMultiVSpec M ι) i
          (stirMulti_length_chal (M := M) (ι := ι) i.1 hmod) x)) ?_) ?_
      · intro ch hch
        refine probEvent_eq_zero ?_
        rintro x hx ⟨hn, hy⟩
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx
        have hflip := stirCheckingPred_flip_out M φ deg δ (m := i.1) hjM hi stmtIn tr ch hn hy
        refine hch ?_
        show trMsgF tr j hA (queryPoint φ (chalElemOf (stirMultiVSpec M ι) i ch))
          = trMsgF tr (j + 1) hB (queryPoint φ (chalElemOf (stirMultiVSpec M ι) i ch))
        have hread : chalElemOf (stirMultiVSpec M ι) i ch
            = ch.get ⟨0, by
                rw [stirMulti_length_chal (M := M) (ι := ι) i.1 hmod]; omega⟩ := by
          rw [chalElemOf, dif_pos]
        rw [hread]
        exact hflip.2
      · have hsub : (Finset.univ.filter (· ∈ L)) ⊆ Finset.univ.erase (φ x₀) := by
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ r⟩
          intro hreq
          subst hreq
          have hqp : queryPoint φ (φ x₀) = x₀ :=
            Function.leftInverse_invFun φ.injective x₀
          rw [hL] at hr
          simp only [Set.mem_setOf_eq, hqp] at hr
          exact hx₀ hr
        have hcardL : (Finset.univ.filter (· ∈ L)).card ≤ Fintype.card F - 1 := by
          refine le_trans (Finset.card_le_card hsub) ?_
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        exact ENNReal.div_le_div_right (by exact_mod_cast hcardL) _

end FlipBounds


section Weld

/-- **The genuine per-challenge budget of the STIR checking verifier** (#301): zero at the
fold and shift challenges, `(|F| − (⌊δ·|ι|⌋+1))/|F|` at the round-2 input-link binding
challenge, and `(|F|−1)/|F|` at the later pair-binding out-challenges.  Genuinely sub-unit at
every binding challenge (for `|F| ≥ 2`), and the model's TRUE security level (the switch
prover achieves it up to the integer rounding) — NOT the paper-STIR L5.4 budgets, which
require the `t`-repetition wire model. -/
noncomputable def stirEpsStar (M : ℕ) (δ : ℝ≥0) :
    ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx → ℝ≥0 := fun c =>
  if (c.1 : ℕ) = 2 then
    ((Fintype.card F - (⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ≥0)
      / ((Fintype.card F : ℕ) : ℝ≥0)
  else if (c.1 : ℕ) % 3 = 2 then
    ((Fintype.card F - 1 : ℕ) : ℝ≥0) / ((Fintype.card F : ℕ) : ℝ≥0)
  else 0

/-- **T1 — genuine sub-unit rbr knowledge soundness of the STIR checking verifier** (#301):
the named soundness residual holds OUTRIGHT at the explicit budget `stirEpsStar` — no
correlated-agreement residuals, no bridge hypothesis, no vacuity.  The knowledge state
function is the retired-prefix winnable predicate; the flip bounds are the three lemmas
above. -/
theorem stirCheckingRbrSoundness_genuine :
    stirCheckingRbrSoundnessResidual M φ deg δ (stirEpsStar (F := F) (ι := ι) M δ) := by
  have hcardF : (Fintype.card F : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := F)
  refine ThresholdKSF.rbrKnowledgeSoundness_of_flipBounds (pure ()) isEmptyElim
    ((stirCheckingIOP M φ deg).verifier.toVerifier)
    (stirRelation deg φ δ) acceptRejectOracleRel
    (stirCheckingPred M φ deg δ) (stirEpsStar (F := F) (ι := ι) M δ)
    (fun stmtIn _ => stirCheckingPred_empty M φ deg δ stmtIn default)
    (fun m hdir stmtIn tr msg h => by
      rw [show ((stirMultiVSpec M ι).toProtocolSpec F).dir m = (stirMultiVSpec M ι).dir m
        from rfl, stirVSpec_dir_eq_msg_iff] at hdir
      exact stirCheckingPred_concat_msg M φ deg δ stmtIn tr msg hdir h)
    (fun stmtIn tr witOut hpr => by
      rw [gt_iff_lt, probEvent_pos_iff] at hpr
      obtain ⟨x, hx, hrel⟩ := hpr
      rw [OptionT.mem_support_iff] at hx
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
      obtain ⟨s, _, hx⟩ := hx
      have hrun : Verifier.run stmtIn tr (stirCheckingIOP M φ deg).verifier.toVerifier
          = (pure (checkingBool M φ deg stmtIn.2 tr.messages tr.challenges,
              fun i : Empty => i.elim) : OptionT (OracleComp []ₒ) _) :=
        checkingVerifier_toVerifier_verify M φ deg stmtIn tr
      erw [hrun, simulateQ_optionT_pure_run'] at hx
      cases (Option.some.inj hx)
      refine stirCheckingPred_full_of_accept M φ deg δ stmtIn tr ?_
      simpa [acceptRejectOracleRel, Prod.ext_iff] using hrel)
    (fun i stmtIn witIn prover => by
      by_cases h2 : (i.1 : ℕ) = 2
      · refine le_trans
          (stirFlip_le_round2 M φ deg δ (pure ()) isEmptyElim i h2 stmtIn witIn prover) ?_
        rw [stirEpsStar, if_pos h2, ENNReal.coe_div hcardF]
        simp only [ENNReal.coe_natCast]
        exact le_refl _
      · by_cases hmod2 : (i.1 : ℕ) % 3 = 2
        · obtain ⟨j, hj⟩ : ∃ j, (i.1 : ℕ) = 3 * j + 5 := ⟨((i.1 : ℕ) - 5) / 3, by omega⟩
          have hjM : j < M := by have := i.1.isLt; omega
          refine le_trans
            (stirFlip_le_out M φ deg δ (pure ()) isEmptyElim i j hjM hj stmtIn witIn prover) ?_
          rw [stirEpsStar, if_neg h2, if_pos hmod2, ENNReal.coe_div hcardF]
          simp only [ENNReal.coe_natCast]
          exact le_refl _
        · have hdir := i.2
          rw [show ((stirMultiVSpec M ι).toProtocolSpec F).dir i.1
              = (stirMultiVSpec M ι).dir i.1 from rfl,
            stirVSpec_dir_eq_chal_iff] at hdir
          have h0 : (i.1 : ℕ) % 3 = 0 := by omega
          refine le_trans
            (stirFlip_le_zero M φ deg δ (pure ()) isEmptyElim i h0 stmtIn witIn prover) ?_
          rw [stirEpsStar, if_neg h2, if_neg hmod2]
          simp)

/-- **T2 — the named open CA bridge of #301, DISCHARGED at the genuine budget**: since the
rbr soundness residual holds outright (`stirCheckingRbrSoundness_genuine`), the implication
from the correlated-agreement residuals is true a fortiori.  In the degenerate single-domain
identity-fold wire model, the protocol-level soundness needs NO proximity-gap input: the
proximity gap is only needed when folding genuinely reduces degree (paper-STIR; the #304
`UnifiedProducer` lane). -/
theorem stirCheckingCABridge_genuine (e ProxGapBound : Fin (M + 1) → ℝ≥0) :
    stirCheckingCABridge M φ deg δ (stirEpsStar (F := F) (ι := ι) M δ) e ProxGapBound :=
  fun _ _ => stirCheckingRbrSoundness_genuine M φ deg δ

/-- **The first hypothesis-free `IsSecureWithGap` for the assembled STIR checking IOPP at a
non-vacuous budget**: perfect completeness (landed) + the genuine rbr soundness (T1). -/
theorem stirCheckingIOP_isSecureWithGap_genuine :
    IsSecureWithGap (stirRelation deg φ 0) (stirRelation deg φ δ)
      (stirEpsStar (F := F) (ι := ι) M δ) (stirCheckingIOP M φ deg) :=
  stirCheckingIOP_isSecureWithGap M φ deg δ _
    (stirCheckingRbrSoundness_genuine M φ deg δ)


/-- **Theorem 5.1 through the checking IOPP at the GENUINE budget** (#301): `stir_main`
discharged with the soundness leg PROVEN (no CA residuals, no bridge hypothesis, no vacuity)
— the caller supplies only the statement's own free-parameter legs (`hε`/`hM`/`hLen`/`hQin`/
`hQpf` and the field/degree constraints).  HONESTY: the `hε` leg pins `secpar` to the genuine
security of the single-query wire model (`ε⋆ ≤ 2^{-secpar}`); real `secpar` requires the
`t`-repetition wire model (the budget is essentially tight by the switch-prover attack). -/
theorem stir_main_of_checkingIOP_genuine
    {M : ℕ} (secpar : ℕ)
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / LinearCode.rate (code φ degree)))
    (hε : ∀ i, stirEpsStar (F := F) (ι := ι) M δ i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hM : ∃ c > 0, M ≤ c * (Real.log degree / Real.log k))
    (hLen : ∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree))
    (hQin : (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ)))
    (hQpf : ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
      (cₖ k) * ((Real.log degree) +
        secpar * (Real.log ((Real.log degree) / Real.log (1 / LinearCode.rate (code φ degree)))))) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF :=
  stir_main_of_secure_vectorIOP secpar hk hkGe δ hδub hF
    (stirEpsStar (F := F) (ι := ι) M δ) (stirCheckingIOP M φ degree)
    (stirCheckingIOP_isSecureWithGap_genuine M φ degree δ)
    hε hM hLen hQin hQpf

end Weld

end Pred

end MultiRound

end StirIOP

end

#print axioms StirIOP.MultiRound.stirCheckingPred_empty
#print axioms StirIOP.MultiRound.stirCheckingPred_concat_zero
#print axioms StirIOP.MultiRound.stirCheckingPred_concat_msg
#print axioms StirIOP.MultiRound.stirCheckingPred_full_of_accept
#print axioms StirIOP.MultiRound.stirCheckingPred_flip_two
#print axioms StirIOP.MultiRound.stirCheckingPred_flip_out

#print axioms StirIOP.MultiRound.stirFlip_le_zero
#print axioms StirIOP.MultiRound.stirFlip_le_round2
#print axioms StirIOP.MultiRound.stirFlip_le_out
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundness_genuine
#print axioms StirIOP.MultiRound.stirCheckingCABridge_genuine
#print axioms StirIOP.MultiRound.stirCheckingIOP_isSecureWithGap_genuine
#print axioms StirIOP.MultiRound.stir_main_of_checkingIOP_genuine
#print axioms ThresholdKSF.rbrKnowledgeSoundness_of_flipBounds
