/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.MarginalBridgeProof
import ArkLib.ProofSystem.Logup.Protocol

/-!
# Outer soundness game, decomposed around its two challenge draws (issue #13, piece γ of `hOuter`)

The remaining `hOuter` obligation of issue #13's soundness side is stated for an **arbitrary
(malicious) prover** `P` interacting with the honest outer verifier
(`(outerVerifier …).toVerifier.soundness …`).  Its measure core is already discharged in plug-in
form (`outer_bad_accept_le_outerSoundnessError_sharp{,_comap}` and
`probEvent_bind_le_uniform_marginal_indexed`), but those bricks consume the game in the
**nested-bind shape** `m₀ >>= fun c => mx c >>= k c` where `mx c` is the (uniform) challenge draw.
This file produces exactly that shape, *unconditionally*, for an arbitrary opaque prover:

* generic layer (`namespace Verifier`): for **any** reduction `Reduction.mk P V` over **any**
  `pSpec` and **any** challenge round `i`, the simulated soundness run factors as

  `(prefix through round i-1, state-threaded) >>= (uniform challenge draw) >>= (tail)`,

  as a plain `ProbComp` **equality** (`game_eq_challenge_bind`); and each such tail factors again
  around any **later** challenge round `j` (`run'_simulateQ_challengeTail_eq_challenge_bind`).
  The proof composes the proven run-decomposition bricks: `Verifier.reduction_run_run_nf`,
  `Prover.run_eq_runToRound_last`, `Prover.runToRound_eq_bind_continueFromTo`,
  `Prover.continueFromTo_trans`/`_succ_of_ne`/`_self`, `Prover.processRound_challenge`, and the
  challenge-coherence brick `ChallengeCoherence.run'_simulateQ_addLift_getChallenge_bind`.

* LogUp layer (`namespace Logup`): instantiation at the outer protocol's two verifier challenges —
  round `1` (the `x`-challenge, `outerXChallengeIdx`) and round `3` (the batching challenge
  `(z, λ)`, `outerBatchChallengeIdx`).  The headline `outerGame_eq_double_challenge_bind` exposes
  **both** draws nested; `probEvent_outerGame_eq_xChallenge_bind` /
  `probEvent_outerGame_eq_double_challenge_bind` restate the literal soundness-game `probEvent`
  over the decomposed program, which is the form the indexed marginal bound
  (`probEvent_bind_le_uniform_marginal_indexed`) consumes directly.

The pole-rejection guard of the outer verifier sits entirely inside the (opaque) trailing verifier
stage `(V.run stmt tr).run`, so it does not disturb this prover-side decomposition; the
conditioning on it enters only downstream (piece δ).

No `sorry`; everything is a plain monadic/`probEvent` equality.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Verifier

open Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type}

/-- **The post-draw continuation of the soundness run at challenge round `i`.**  Given the
round-`i.castSucc` prefix result `rk` (transcript + prover state) and the drawn challenge `c`,
the rest of the run is: the prover receives `c`, plays rounds `i+1 … n-1`, produces its output,
and the verifier checks the full transcript (its `Option` short-circuit absorbed into an
`Option.map` of the final pairing, as in `Verifier.reduction_run_run_nf`). -/
def challengeTail
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (i : pSpec.ChallengeIdx)
    (rk : pSpec.Transcript i.1.castSucc × prover.PrvState i.1.castSucc)
    (c : pSpec.Challenge i) :
    OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)) :=
  liftM (prover.receiveChallenge i rk.2) >>= fun rcv =>
    Prover.continueFromTo prover stmtIn witIn i.1.succ (Fin.last n)
        (Transcript.concat c rk.1, rcv c) >>= fun rl =>
      liftM (prover.output rl.2) >>= fun out =>
        liftM ((verifier.run stmtIn rl.1).run) >>= fun o =>
          pure (Option.map (fun v => ((rl.1, out), v)) o)

/-- **The middle segment between two challenge rounds `i < j`.**  Given the round-`i.castSucc`
prefix result `rk` and the round-`i` challenge `c`, run the prover from receiving `c` up to (but
not including) round `j` — i.e. produce the round-`j.castSucc` prefix result.  For the LogUp outer
protocol with `i = 1`, `j = 3` this is: receive the `x`-challenge, then send the round-2 helper
message. -/
def challengeSegment
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (i j : pSpec.ChallengeIdx)
    (rk : pSpec.Transcript i.1.castSucc × prover.PrvState i.1.castSucc)
    (c : pSpec.Challenge i) :
    OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.1.castSucc × prover.PrvState j.1.castSucc) :=
  liftM (prover.receiveChallenge i rk.2) >>= fun rcv =>
    Prover.continueFromTo prover stmtIn witIn i.1.succ j.1.castSucc
      (Transcript.concat c rk.1, rcv c)

/-- **The (raw) soundness run factors around any challenge round `i`.**  The full reduction run —
for an *arbitrary* prover — equals: prover prefix to round `i.castSucc`, then the (lifted) round-`i`
`getChallenge` query, then the post-draw continuation `challengeTail`.  A plain `OracleComp`
equality; the decomposition bricks are `reduction_run_run_nf`, `run_eq_runToRound_last`,
`runToRound_eq_bind_continueFromTo`, `continueFromTo_trans`/`_succ_of_ne`/`_self`, and
`processRound_challenge`. -/
theorem reduction_run_run_eq_challengeTail_bind
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (i : pSpec.ChallengeIdx) :
    ((Reduction.mk prover verifier).run stmtIn witIn).run
      = prover.runToRound i.1.castSucc stmtIn witIn >>= fun rk =>
          (liftM (pSpec.getChallenge i) :
              OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i)) >>= fun c =>
            challengeTail prover verifier stmtIn witIn i rk c := by
  have hle₁ : i.1.castSucc ≤ Fin.last n := Fin.le_last _
  -- Decompose `prover.run` to expose `runToRound i.castSucc >>= continueFromTo`.
  have hdecomp :
      ((Reduction.mk prover verifier).run stmtIn witIn).run
        = prover.runToRound i.1.castSucc stmtIn witIn >>= fun rk =>
            (continueFromTo prover stmtIn witIn i.1.castSucc (Fin.last n) rk >>= fun rl =>
              liftM (prover.output rl.2) >>= fun out =>
                (liftM ((verifier.run stmtIn rl.1).run) >>= fun o =>
                  pure (o.map (fun v => ((rl.1, out), v))))) := by
    rw [reduction_run_run_nf, run_eq_runToRound_last,
      runToRound_eq_bind_continueFromTo prover stmtIn witIn i.1.castSucc (Fin.last n) hle₁]
    simp only [bind_assoc, pure_bind, OracleComp.liftComp_eq_liftM]
    rfl
  -- Expose the round-`i` challenge at the head of the continuation.
  have hsucc_le : i.1.succ ≤ Fin.last n := by
    rw [Fin.le_def, Fin.val_succ, Fin.val_last]; exact i.1.isLt
  have hcs_le_succ : i.1.castSucc ≤ i.1.succ := by
    rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega
  have hne : (i.1.castSucc : Fin (n + 1)) ≠ i.1.succ := by
    rw [Ne, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
  have hcft : ∀ rk : pSpec.Transcript i.1.castSucc × prover.PrvState i.1.castSucc,
      continueFromTo prover stmtIn witIn i.1.castSucc (Fin.last n) rk
        = (prover.processRound i.1 (pure rk) >>=
            continueFromTo prover stmtIn witIn i.1.succ (Fin.last n)) := by
    intro rk
    rw [continueFromTo_trans prover stmtIn witIn i.1.castSucc i.1.succ (Fin.last n)
      hcs_le_succ hsucc_le rk]
    rw [continueFromTo_succ_of_ne prover stmtIn witIn i.1.castSucc i.1 hne rk,
      continueFromTo_self]
  rw [hdecomp]
  simp only [hcft, processRound_challenge, bind_assoc, pure_bind]
  refine bind_congr fun rk => ?_
  obtain ⟨tr, st⟩ := rk
  simp only [challengeTail]
  rfl

/-- **The post-draw continuation at round `i` factors around any later challenge round `j`.**
`challengeTail i` equals: the middle segment to round `j.castSucc`, then the (lifted) round-`j`
`getChallenge` query, then the post-draw continuation `challengeTail j`.  A plain `OracleComp`
equality, valid for an arbitrary prover. -/
theorem challengeTail_eq_challengeSegment_bind
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (i j : pSpec.ChallengeIdx) (hij : i.1 < j.1)
    (rk : pSpec.Transcript i.1.castSucc × prover.PrvState i.1.castSucc)
    (c : pSpec.Challenge i) :
    challengeTail prover verifier stmtIn witIn i rk c
      = challengeSegment prover stmtIn witIn i j rk c >>= fun rl =>
          (liftM (pSpec.getChallenge j) :
              OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge j)) >>= fun b =>
            challengeTail prover verifier stmtIn witIn j rl b := by
  have hsucc_le_cs : i.1.succ ≤ j.1.castSucc := by
    rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    exact hij
  have hcs_le_last : (j.1.castSucc : Fin (n + 1)) ≤ Fin.last n := Fin.le_last _
  have hsucc_le : j.1.succ ≤ Fin.last n := by
    rw [Fin.le_def, Fin.val_succ, Fin.val_last]; exact j.1.isLt
  have hcs_le_succ : (j.1.castSucc : Fin (n + 1)) ≤ j.1.succ := by
    rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega
  have hne : (j.1.castSucc : Fin (n + 1)) ≠ j.1.succ := by
    rw [Ne, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
  have hcft : ∀ rl : pSpec.Transcript j.1.castSucc × prover.PrvState j.1.castSucc,
      continueFromTo prover stmtIn witIn j.1.castSucc (Fin.last n) rl
        = (prover.processRound j.1 (pure rl) >>=
            continueFromTo prover stmtIn witIn j.1.succ (Fin.last n)) := by
    intro rl
    rw [continueFromTo_trans prover stmtIn witIn j.1.castSucc j.1.succ (Fin.last n)
      hcs_le_succ hsucc_le rl]
    rw [continueFromTo_succ_of_ne prover stmtIn witIn j.1.castSucc j.1 hne rl,
      continueFromTo_self]
  unfold challengeTail challengeSegment
  simp only [bind_assoc]
  refine bind_congr fun rcv => ?_
  rw [continueFromTo_trans prover stmtIn witIn i.1.succ j.1.castSucc (Fin.last n)
    hsucc_le_cs hcs_le_last, bind_assoc]
  refine bind_congr fun rl => ?_
  rw [hcft rl]
  obtain ⟨tr, st⟩ := rl
  simp only [processRound_challenge, bind_assoc, pure_bind]

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- **Threaded-prefix challenge-coherence brick.**  Simulating (under the honest interactive
implementation `impl.addLift challengeQueryImpl`, from state `s`) a computation of the shape
`A >>= fun a => getChallenge i >>= k a` equals: run the simulated prefix `A` (state-threaded),
draw the challenge **uniformly**, then run the simulated tail from the threaded state.  This is
the `m₀ >>= fun c => mx c >>= k c` exposure step; the head case is the proven
`ChallengeCoherence.run'_simulateQ_addLift_getChallenge_bind`. -/
theorem run'_simulateQ_addLift_bind_getChallenge_bind
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    {α β : Type} (A : OracleComp (oSpec + [pSpec.Challenge]ₒ) α)
    (i : pSpec.ChallengeIdx)
    (k : α → pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) β) :
    (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (A >>= fun a =>
          (liftM (pSpec.getChallenge i) :
              OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i)) >>= fun c =>
            k a c)).run' s
      = (simulateQ (impl.addLift challengeQueryImpl :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) A).run s >>= fun p =>
          ($ᵗ pSpec.Challenge i) >>= fun c =>
            (simulateQ (impl.addLift challengeQueryImpl :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
              (k p.1 c)).run' p.2 := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine bind_congr fun p => ?_
  rw [← StateT.run'_eq]
  exact ChallengeCoherence.run'_simulateQ_addLift_getChallenge_bind impl p.2 i (k p.1)

/-- **(γ1, per init-state) The simulated soundness run factors around challenge round `i`.**
For an arbitrary prover, the simulated reduction run from state `s` equals: simulated prefix to
round `i.castSucc` (state-threaded), **uniform** round-`i` challenge draw, simulated post-draw
continuation from the threaded state. -/
theorem run'_simulateQ_reduction_run_eq_challenge_bind
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (i : pSpec.ChallengeIdx) :
    (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        ((Reduction.mk prover verifier).run stmtIn witIn).run).run' s
      = (simulateQ (impl.addLift challengeQueryImpl :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
          (prover.runToRound i.1.castSucc stmtIn witIn)).run s >>= fun rk =>
          ($ᵗ pSpec.Challenge i) >>= fun c =>
            (simulateQ (impl.addLift challengeQueryImpl :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
              (challengeTail prover verifier stmtIn witIn i rk.1 c)).run' rk.2 := by
  rw [reduction_run_run_eq_challengeTail_bind prover verifier stmtIn witIn i]
  exact run'_simulateQ_addLift_bind_getChallenge_bind impl s _ i _

/-- **(γ2, per state) The simulated post-draw continuation factors around a later challenge round.**
For an arbitrary prover and challenge rounds `i < j`, the simulated `challengeTail i` from state
`s` equals: simulated middle segment to round `j.castSucc` (state-threaded), **uniform** round-`j`
challenge draw, simulated post-draw continuation `challengeTail j` from the threaded state. -/
theorem run'_simulateQ_challengeTail_eq_challenge_bind
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (i j : pSpec.ChallengeIdx) (hij : i.1 < j.1)
    (rk : pSpec.Transcript i.1.castSucc × prover.PrvState i.1.castSucc)
    (c : pSpec.Challenge i) :
    (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (challengeTail prover verifier stmtIn witIn i rk c)).run' s
      = (simulateQ (impl.addLift challengeQueryImpl :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
          (challengeSegment prover stmtIn witIn i j rk c)).run s >>= fun rl =>
          ($ᵗ pSpec.Challenge j) >>= fun b =>
            (simulateQ (impl.addLift challengeQueryImpl :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
              (challengeTail prover verifier stmtIn witIn j rl.1 b)).run' rl.2 := by
  rw [challengeTail_eq_challengeSegment_bind prover verifier stmtIn witIn i j hij rk c]
  exact run'_simulateQ_addLift_bind_getChallenge_bind impl s _ j _

/-- **(γ1) The soundness game factors around challenge round `i` (`m₀ >>= mx >>= k` shape).**
The full game (averaging over the `init` state sample) equals the nested-bind shape consumed by
`probEvent_bind_le_uniform_marginal_indexed`: a first stage `m₀` (init + simulated prover prefix),
a **uniform** challenge draw, and a prefix-indexed continuation. -/
theorem game_eq_challenge_bind
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (i : pSpec.ChallengeIdx) :
    (init >>= fun s =>
      (simulateQ (impl.addLift challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        ((Reduction.mk prover verifier).run stmtIn witIn).run).run' s)
      = (init >>= fun s =>
          (simulateQ (impl.addLift challengeQueryImpl :
              QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
            (prover.runToRound i.1.castSucc stmtIn witIn)).run s) >>= fun rk =>
          ($ᵗ pSpec.Challenge i) >>= fun c =>
            (simulateQ (impl.addLift challengeQueryImpl :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
              (challengeTail prover verifier stmtIn witIn i rk.1 c)).run' rk.2 := by
  conv_rhs => rw [bind_assoc]
  exact bind_congr fun s =>
    run'_simulateQ_reduction_run_eq_challenge_bind impl s prover verifier stmtIn witIn i

/-- **(γ1 ∘ γ2) The soundness game with both challenge draws exposed, nested.**  For an arbitrary
prover and challenge rounds `i < j`, the full game equals: `m₀` (init + simulated prover prefix to
round `i.castSucc`), **uniform** round-`i` draw, simulated middle segment to round `j.castSucc`,
**uniform** round-`j` draw, simulated final stage.  Both draws are in the exact
`… >>= fun c => mx c >>= k c` shape the indexed marginal bound consumes (at either level). -/
theorem game_eq_double_challenge_bind
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (i j : pSpec.ChallengeIdx) (hij : i.1 < j.1) :
    (init >>= fun s =>
      (simulateQ (impl.addLift challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        ((Reduction.mk prover verifier).run stmtIn witIn).run).run' s)
      = (init >>= fun s =>
          (simulateQ (impl.addLift challengeQueryImpl :
              QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
            (prover.runToRound i.1.castSucc stmtIn witIn)).run s) >>= fun rk =>
          ($ᵗ pSpec.Challenge i) >>= fun c =>
            (simulateQ (impl.addLift challengeQueryImpl :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
              (challengeSegment prover stmtIn witIn i j rk.1 c)).run rk.2 >>= fun rl =>
              ($ᵗ pSpec.Challenge j) >>= fun b =>
                (simulateQ (impl.addLift challengeQueryImpl :
                    QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
                  (challengeTail prover verifier stmtIn witIn j rl.1 b)).run' rl.2 := by
  rw [game_eq_challenge_bind init impl prover verifier stmtIn witIn i]
  refine bind_congr fun rk => bind_congr fun c => ?_
  exact run'_simulateQ_challengeTail_eq_challenge_bind impl rk.2 prover verifier
    stmtIn witIn i j hij rk.1 c

end Verifier

namespace Logup

open Verifier

section OuterRunDecomposition

variable {ι : Type} {oSpec : OracleSpec ι}
  {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  {n M : ℕ} {params : ProtocolParams M}
  {σ : Type} {WitIn WitOut : Type}

/-- The LogUp outer challenges are oracle-accessible (uniform challenge oracle interface), needed
to name the combined oracle spec `oSpec + [(outerPSpec F n params).Challenge]ₒ` (same device as
`Security/OuterSoundnessReal.lean`). -/
local instance instOuterDecompChallengeOI {F : Type} {n M : ℕ} {params : ProtocolParams M} :
    ∀ i, OracleInterface ((outerPSpec F n params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- The round-1 `x`-challenge index of the outer LogUp protocol. -/
def outerXChallengeIdx (F : Type) (n : ℕ) {M : ℕ} (params : ProtocolParams M) :
    (outerPSpec F n params).ChallengeIdx := ⟨1, rfl⟩

/-- The round-3 batching-challenge index of the outer LogUp protocol. -/
def outerBatchChallengeIdx (F : Type) (n : ℕ) {M : ℕ} (params : ProtocolParams M) :
    (outerPSpec F n params).ChallengeIdx := ⟨3, rfl⟩

/-- The `x`-challenge round strictly precedes the batching-challenge round. -/
theorem outerXChallengeIdx_lt_outerBatchChallengeIdx (F : Type) (n : ℕ) {M : ℕ}
    (params : ProtocolParams M) :
    (outerXChallengeIdx F n params).1 < (outerBatchChallengeIdx F n params).1 := by
  show (1 : Fin 4) < (3 : Fin 4)
  decide

/-- The success payload of the outer LogUp soundness game for an arbitrary prover with output
witness type `WitOut`. -/
abbrev OuterGameResult (F : Type) [Field F] [Fintype F] (n M : ℕ)
    (params : ProtocolParams M) (WitOut : Type) : Type :=
  ((outerPSpec F n params).FullTranscript ×
      (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i) × WitOut) ×
    (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i)

/-- **(γ1, LogUp) The outer soundness game factors around the round-1 `x`-challenge draw.**
For an **arbitrary** (opaque) prover `P` against the honest outer verifier, the soundness game's
underlying `ProbComp` equals the nested-bind shape `m₀ >>= fun rk => mx >>= k rk`: a first stage
(init + the simulated prover round-0 multiplicity-message prefix, state-threaded), the **uniform**
`x`-challenge draw, and the prefix-indexed continuation.  This is exactly the shape
`probEvent_bind_le_uniform_marginal_indexed` consumes for the outer Schwartz–Zippel step. -/
theorem outerGame_eq_xChallenge_bind
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (P : Prover oSpec (StmtIn F n M × ∀ i, OStmtIn F n M i) WitIn
      (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i) WitOut
      (outerPSpec F n params))
    (stmtIn : StmtIn F n M × ∀ i, OStmtIn F n M i) (witIn : WitIn) :
    (init >>= fun s =>
      (simulateQ (impl.addLift challengeQueryImpl :
          QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
        ((Reduction.mk P (outerVerifier oSpec F n M params).toVerifier).run
          stmtIn witIn).run).run' s)
      = (init >>= fun s =>
          (simulateQ (impl.addLift challengeQueryImpl :
              QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
            (P.runToRound (outerXChallengeIdx F n params).1.castSucc stmtIn witIn)).run s)
          >>= fun rk =>
          ($ᵗ (outerPSpec F n params).Challenge (outerXChallengeIdx F n params)) >>= fun c =>
            (simulateQ (impl.addLift challengeQueryImpl :
                QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
              (challengeTail P (outerVerifier oSpec F n M params).toVerifier stmtIn witIn
                (outerXChallengeIdx F n params) rk.1 c)).run' rk.2 :=
  game_eq_challenge_bind init impl P (outerVerifier oSpec F n M params).toVerifier
    stmtIn witIn (outerXChallengeIdx F n params)

/-- **(γ2, LogUp) Each post-`x` continuation factors around the round-3 batching draw.**
For an arbitrary prover, the simulated post-`x` continuation from any threaded state `s` equals:
the simulated middle segment (receive `x`, send the round-2 helper message), the **uniform**
batching-challenge `(z, λ)` draw, and the final stage (receive the batching challenge, prover
output, verifier check — including the pole-rejection guard, untouched inside the verifier). -/
theorem outerChallengeTail_eq_batchChallenge_bind
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (P : Prover oSpec (StmtIn F n M × ∀ i, OStmtIn F n M i) WitIn
      (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i) WitOut
      (outerPSpec F n params))
    (stmtIn : StmtIn F n M × ∀ i, OStmtIn F n M i) (witIn : WitIn)
    (rk : (outerPSpec F n params).Transcript (outerXChallengeIdx F n params).1.castSucc ×
      P.PrvState (outerXChallengeIdx F n params).1.castSucc)
    (c : (outerPSpec F n params).Challenge (outerXChallengeIdx F n params)) :
    (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
        (challengeTail P (outerVerifier oSpec F n M params).toVerifier stmtIn witIn
          (outerXChallengeIdx F n params) rk c)).run' s
      = (simulateQ (impl.addLift challengeQueryImpl :
            QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
          (challengeSegment P stmtIn witIn (outerXChallengeIdx F n params)
            (outerBatchChallengeIdx F n params) rk c)).run s >>= fun rl =>
          ($ᵗ (outerPSpec F n params).Challenge (outerBatchChallengeIdx F n params)) >>= fun b =>
            (simulateQ (impl.addLift challengeQueryImpl :
                QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
              (challengeTail P (outerVerifier oSpec F n M params).toVerifier stmtIn witIn
                (outerBatchChallengeIdx F n params) rl.1 b)).run' rl.2 :=
  run'_simulateQ_challengeTail_eq_challenge_bind impl s P
    (outerVerifier oSpec F n M params).toVerifier stmtIn witIn
    (outerXChallengeIdx F n params) (outerBatchChallengeIdx F n params)
    (outerXChallengeIdx_lt_outerBatchChallengeIdx F n params) rk c

/-- **(γ headline) The outer soundness game with both challenge draws exposed, nested.**
For an arbitrary prover, the game equals: `m₀` (init + simulated round-0 prefix), **uniform**
`x`-draw, simulated middle segment (receive `x` + round-2 helper message), **uniform** batching
draw, simulated final stage.  Each draw is in the `… >>= fun c => mx c >>= k c` shape consumed by
`probEvent_bind_le_uniform_marginal_indexed`. -/
theorem outerGame_eq_double_challenge_bind
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (P : Prover oSpec (StmtIn F n M × ∀ i, OStmtIn F n M i) WitIn
      (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i) WitOut
      (outerPSpec F n params))
    (stmtIn : StmtIn F n M × ∀ i, OStmtIn F n M i) (witIn : WitIn) :
    (init >>= fun s =>
      (simulateQ (impl.addLift challengeQueryImpl :
          QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
        ((Reduction.mk P (outerVerifier oSpec F n M params).toVerifier).run
          stmtIn witIn).run).run' s)
      = (init >>= fun s =>
          (simulateQ (impl.addLift challengeQueryImpl :
              QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
            (P.runToRound (outerXChallengeIdx F n params).1.castSucc stmtIn witIn)).run s)
          >>= fun rk =>
          ($ᵗ (outerPSpec F n params).Challenge (outerXChallengeIdx F n params)) >>= fun c =>
            (simulateQ (impl.addLift challengeQueryImpl :
                QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
              (challengeSegment P stmtIn witIn (outerXChallengeIdx F n params)
                (outerBatchChallengeIdx F n params) rk.1 c)).run rk.2 >>= fun rl =>
              ($ᵗ (outerPSpec F n params).Challenge (outerBatchChallengeIdx F n params))
                >>= fun b =>
                (simulateQ (impl.addLift challengeQueryImpl :
                    QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ)
                      (StateT σ ProbComp))
                  (challengeTail P (outerVerifier oSpec F n M params).toVerifier stmtIn witIn
                    (outerBatchChallengeIdx F n params) rl.1 b)).run' rl.2 :=
  game_eq_double_challenge_bind init impl P (outerVerifier oSpec F n M params).toVerifier
    stmtIn witIn (outerXChallengeIdx F n params) (outerBatchChallengeIdx F n params)
    (outerXChallengeIdx_lt_outerBatchChallengeIdx F n params)

/-- **(γ1, `probEvent` form) The literal soundness-game probability over the decomposed program.**
The outer soundness game's event probability (the exact `OptionT.mk`-shaped game of
`Verifier.soundness`, for an arbitrary prover and an arbitrary event `p` on the success payload)
equals the `none`-excluded event probability over the γ1-decomposed nested-bind program.  This is
the statement piece δ rewrites with before applying the indexed marginal bound at the `x` draw. -/
theorem probEvent_outerGame_eq_xChallenge_bind
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (P : Prover oSpec (StmtIn F n M × ∀ i, OStmtIn F n M i) WitIn
      (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i) WitOut
      (outerPSpec F n params))
    (stmtIn : StmtIn F n M × ∀ i, OStmtIn F n M i) (witIn : WitIn)
    (p : OuterGameResult F n M params WitOut → Prop) :
    Pr[p | (OptionT.mk (do
        (simulateQ (impl.addLift challengeQueryImpl :
            QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
          ((Reduction.mk P (outerVerifier oSpec F n M params).toVerifier).run
            stmtIn witIn).run).run' (← init)) :
        OptionT ProbComp (OuterGameResult F n M params WitOut))]
      = Pr[fun o => Option.elim o False p |
          (init >>= fun s =>
            (simulateQ (impl.addLift challengeQueryImpl :
                QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
              (P.runToRound (outerXChallengeIdx F n params).1.castSucc stmtIn witIn)).run s)
            >>= fun rk =>
            ($ᵗ (outerPSpec F n params).Challenge (outerXChallengeIdx F n params)) >>= fun c =>
              (simulateQ (impl.addLift challengeQueryImpl :
                  QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
                (challengeTail P (outerVerifier oSpec F n M params).toVerifier stmtIn witIn
                  (outerXChallengeIdx F n params) rk.1 c)).run' rk.2] := by
  rw [OptionTStateT.probEvent_optionT_mk,
    outerGame_eq_xChallenge_bind init impl P stmtIn witIn]

/-- **(γ headline, `probEvent` form) The literal soundness-game probability over the fully
decomposed program.**  Same as `probEvent_outerGame_eq_xChallenge_bind`, with **both** the
round-1 `x` draw and the round-3 batching draw exposed (nested) in the program. -/
theorem probEvent_outerGame_eq_double_challenge_bind
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (P : Prover oSpec (StmtIn F n M × ∀ i, OStmtIn F n M i) WitIn
      (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i) WitOut
      (outerPSpec F n params))
    (stmtIn : StmtIn F n M × ∀ i, OStmtIn F n M i) (witIn : WitIn)
    (p : OuterGameResult F n M params WitOut → Prop) :
    Pr[p | (OptionT.mk (do
        (simulateQ (impl.addLift challengeQueryImpl :
            QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
          ((Reduction.mk P (outerVerifier oSpec F n M params).toVerifier).run
            stmtIn witIn).run).run' (← init)) :
        OptionT ProbComp (OuterGameResult F n M params WitOut))]
      = Pr[fun o => Option.elim o False p |
          (init >>= fun s =>
            (simulateQ (impl.addLift challengeQueryImpl :
                QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
              (P.runToRound (outerXChallengeIdx F n params).1.castSucc stmtIn witIn)).run s)
            >>= fun rk =>
            ($ᵗ (outerPSpec F n params).Challenge (outerXChallengeIdx F n params)) >>= fun c =>
              (simulateQ (impl.addLift challengeQueryImpl :
                  QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
                (challengeSegment P stmtIn witIn (outerXChallengeIdx F n params)
                  (outerBatchChallengeIdx F n params) rk.1 c)).run rk.2 >>= fun rl =>
                ($ᵗ (outerPSpec F n params).Challenge (outerBatchChallengeIdx F n params))
                  >>= fun b =>
                  (simulateQ (impl.addLift challengeQueryImpl :
                      QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ)
                        (StateT σ ProbComp))
                    (challengeTail P (outerVerifier oSpec F n M params).toVerifier stmtIn witIn
                      (outerBatchChallengeIdx F n params) rl.1 b)).run' rl.2] := by
  rw [OptionTStateT.probEvent_optionT_mk,
    outerGame_eq_double_challenge_bind init impl P stmtIn witIn]

end OuterRunDecomposition

end Logup

