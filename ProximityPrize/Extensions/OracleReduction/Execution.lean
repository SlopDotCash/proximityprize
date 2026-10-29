/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Execution

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ProximityPrize.Extensions.OracleReduction.Basic
import ProximityPrize.Extensions.Data.Fin.Basic
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Constructions.Replicate
import VCVio.EvalDist.List
import ToMathlib.Data.Vector

/-!
  # Execution Semantics of Interactive Oracle Reductions

  We define what it means to execute an interactive oracle reduction, and prove some basic
  properties.
-/

open OracleComp OracleSpec SubSpec ProtocolSpec

universe u v



section Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
 {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

namespace Prover

private lemma fst_map_simulateQ_loggingOracle_run {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) :
    Prod.fst <$> WriterT.run (simulateQ loggingOracle oa) = oa := by
  exact loggingOracle.fst_map_run_simulateQ oa

end Prover

private lemma fst_map_liftComp_simulateQ_loggingOracle_run {ι τ : Type}
    {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α : Type}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) :
    Prod.fst <$> (WriterT.run (simulateQ loggingOracle oa)).liftComp superSpec =
      oa.liftComp superSpec := by
  rw [← OracleComp.liftComp_map]
  exact congrArg (fun x => x.liftComp superSpec)
    (loggingOracle.fst_map_run_simulateQ oa)

/-- Note: figure out a better name for this -/
private lemma Monad.map_of_prod_fst_eq_prod_fst {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α β γ : Type u} (ma : m (α × β)) (c : γ) :
    (fun a => (c, a.1)) <$> ma = Prod.mk c <$> Prod.fst <$> ma := by
  simp only [Functor.map_map]

/-- In OptionT, lifting a pair-valued computation and projecting the first component
in the continuation equals lifting the map and binding directly. -/
private lemma OptionT_liftM_bind_fst {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β γ : Type} (x : m (α × β)) (f : α → OptionT m γ) :
    ((liftM x : OptionT m _) >>= fun p => f p.1) =
    (liftM (Prod.fst <$> x) : OptionT m _) >>= f := by
  rw [← bind_map_left]
  show (Prod.fst <$> monadLift x) >>= f = monadLift (Prod.fst <$> x) >>= f
  congr 1
  simp [liftM]

namespace Prover

/-! ### Prefix / round-range decomposition of `runToRound`

These additive lemmas relate the prover's full run to its per-round partial runs.  The keystone is
`runToRound_eq_bind_continueFromTo`: for any earlier round `k ≤ j`, the run up to round `j` factors
as the run up to `k` followed by a continuation `continueFromTo` that folds `processRound` over the
remaining rounds `k .. j-1`.  This is a plain `OracleComp` *equality* (the continuation only
`processRound`s further rounds), which is the structural connective consumed by both the
`rbrSoundness → soundness` probability bridge and the sequential-composition `append_run`
characterization. -/

/-- **`processRound` at a challenge (V_to_P) round.**  Specialization of `processRound` to a round
  `i` that is a challenge round (so `pSpec.dir i = .V_to_P`). -/
theorem processRound_challenge (i : pSpec.ChallengeIdx)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.1.castSucc × prover.PrvState i.1.castSucc)) :
    prover.processRound i.1 currentResult = (do
      let ⟨transcript, state⟩ ← currentResult
      let challenge ← pSpec.getChallenge i
      let newState := (← prover.receiveChallenge i state) challenge
      return ⟨transcript.concat challenge, newState⟩) := by
  unfold processRound
  obtain ⟨j, hj⟩ := i
  simp only
  congr 1
  funext x
  split <;> rename_i hDir
  · rfl
  · rw [hj] at hDir; exact absurd hDir (by decide)

/-- **Kleisli continuation folding `processRound` over rounds `k .. j-1`.**  Transforms a round-`k`
partial result `(transcript, state)` into the round-`j` partial run, by folding `processRound`.
Defined by `Fin.induction` on the *target* index `j`: when the running index reaches `k` exactly it
returns the supplied start `rk` (`pure`), and each subsequent `succ` step applies one more
`processRound`.  (The `j < k` branches are never used; for those the dependent-`Fin` base is filled
with the `runToRound 0` seed value, kept only to make the fold total.) -/
noncomputable def continueFromTo (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k : Fin (n + 1)) :
    (j : Fin (n + 1)) →
      (pSpec.Transcript k × prover.PrvState k) →
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript j × prover.PrvState j) :=
  Fin.induction
    (motive := fun j => (pSpec.Transcript k × prover.PrvState k) →
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript j × prover.PrvState j))
    (fun rk => if h : (k : Fin (n + 1)) = 0 then h ▸ pure rk
               else pure (default, prover.input (stmt, wit)))
    (fun m prev rk =>
      if h : (k : Fin (n + 1)) = m.succ then h ▸ pure rk
      else prover.processRound m (prev rk))

/-- **`continueFromTo` step at a `succ` target that has not yet reached the start.**  When the target
`m.succ` is *strictly past* the start index `k` (`k ≠ m.succ`), the continuation applies one more
`processRound m` on top of the round-`m.castSucc` continuation. -/
theorem continueFromTo_succ_of_ne (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k : Fin (n + 1)) (m : Fin n)
    (hne : (k : Fin (n + 1)) ≠ m.succ)
    (rk : pSpec.Transcript k × prover.PrvState k) :
    continueFromTo prover stmt wit k m.succ rk
      = prover.processRound m (continueFromTo prover stmt wit k m.castSucc rk) := by
  unfold continueFromTo
  rw [Fin.induction_succ]
  simp only [hne, ↓reduceDIte]

/-- **`continueFromTo` at the diagonal is the identity (`pure`).**  Continuing from round `k` to
round `k` returns the start result unchanged. -/
theorem continueFromTo_self (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (k : Fin (n + 1)) (rk : pSpec.Transcript k × prover.PrvState k) :
    continueFromTo prover stmt wit k k rk = pure rk := by
  unfold continueFromTo
  induction k using Fin.induction with
  | zero => simp [Fin.induction_zero]
  | succ m _ => simp [Fin.induction_succ]

/-- **`processRound` factors as a bind on its input.**  Since `processRound j cur` first runs `cur`
and then performs a round-`j` step depending only on `cur`'s output, it equals
`cur >>= (round-j step on a `pure`d result)`. -/
theorem processRound_eq_bind (j : Fin n) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (cur : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
    prover.processRound j cur = cur >>= (fun r => prover.processRound j (pure r)) := by
  unfold processRound
  simp only [pure_bind]

/-- **Round-range decomposition of `runToRound` (THE keystone).**  For any earlier round `k ≤ j`, the
prover run up to round `j` equals the run up to round `k` followed by the continuation
`continueFromTo` that folds `processRound` over rounds `k .. j-1`.  A plain `OracleComp` equality,
proved by `Fin.induction` on `j` (with `k` fixed) via `runToRound_succ`, `processRound_eq_bind`, and
monad associativity. -/
theorem runToRound_eq_bind_continueFromTo
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k j : Fin (n + 1)) (hkj : k ≤ j) :
    prover.runToRound j stmt wit
      = prover.runToRound k stmt wit >>= continueFromTo prover stmt wit k j := by
  induction j using Fin.induction with
  | zero =>
    have hk0 : k = 0 := le_antisymm hkj (Fin.zero_le _)
    subst hk0
    conv_rhs => rw [show (continueFromTo prover stmt wit 0 0)
                      = (fun rk => pure rk) from funext (continueFromTo_self prover stmt wit 0)]
    rw [bind_pure]
  | succ m ih =>
    rcases eq_or_lt_of_le hkj with heq | hlt
    · subst heq
      conv_rhs => rw [show (continueFromTo prover stmt wit (m.succ) (m.succ))
                        = (fun rk => pure rk)
                          from funext (continueFromTo_self prover stmt wit _)]
      rw [bind_pure]
    · have hkm : k ≤ m.castSucc := by rw [Fin.le_castSucc_iff]; exact hlt
      have hne : (k : Fin (n + 1)) ≠ m.succ := ne_of_lt hlt
      rw [runToRound_succ, ih hkm]
      have hcont : continueFromTo prover stmt wit k m.succ
          = fun rk => prover.processRound m (continueFromTo prover stmt wit k m.castSucc rk) :=
        funext (fun rk => continueFromTo_succ_of_ne prover stmt wit k m hne rk)
      rw [hcont, processRound_eq_bind m prover
            (runToRound k stmt wit prover >>= continueFromTo prover stmt wit k m.castSucc),
          bind_assoc]
      refine bind_congr (fun rk => ?_)
      rw [← processRound_eq_bind]

/-- **Transitivity / range-split of `continueFromTo`.**  For `k ≤ k' ≤ j`, continuing the prover's
run from round `k` to round `j` equals continuing `k → k'` and then `k' → j`.  Proved by
`Fin.induction` on `j` via `continueFromTo_succ_of_ne`, `processRound_eq_bind`, and `bind_assoc`
(the `continueFromTo`-prefix analogue of `runToRound_eq_bind_continueFromTo`).  This is the split a
sequential-composition right-block run characterization needs to peel the seam round off the interior
rounds. -/
theorem continueFromTo_trans (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k k' j : Fin (n + 1)) (hkk' : k ≤ k') (hk'j : k' ≤ j)
    (rk : pSpec.Transcript k × prover.PrvState k) :
    continueFromTo prover stmt wit k j rk
      = continueFromTo prover stmt wit k k' rk >>= continueFromTo prover stmt wit k' j := by
  induction j using Fin.induction with
  | zero =>
    have hk'0 : k' = 0 := le_antisymm hk'j (Fin.zero_le _)
    have hk0 : k = 0 := le_antisymm (hkk'.trans hk'j) (Fin.zero_le _)
    subst hk'0; subst hk0
    simp only [continueFromTo_self, pure_bind]
  | succ m ih =>
    rcases eq_or_lt_of_le hk'j with heq | hlt
    · subst heq
      conv_rhs => rw [show (continueFromTo prover stmt wit (m.succ) (m.succ))
                        = (fun rk => pure rk)
                          from funext (continueFromTo_self prover stmt wit _)]
      rw [bind_pure]
    · have hk'm : k' ≤ m.castSucc := by rw [Fin.le_castSucc_iff]; exact hlt
      have hne : (k : Fin (n + 1)) ≠ m.succ := ne_of_lt (lt_of_le_of_lt hkk' hlt)
      have hne' : (k' : Fin (n + 1)) ≠ m.succ := ne_of_lt hlt
      rw [continueFromTo_succ_of_ne prover stmt wit k m hne rk, ih hk'm]
      have hcont : continueFromTo prover stmt wit k' m.succ
          = fun rk => prover.processRound m (continueFromTo prover stmt wit k' m.castSucc rk) :=
        funext (fun rk => continueFromTo_succ_of_ne prover stmt wit k' m hne' rk)
      rw [hcont, processRound_eq_bind m prover
            (continueFromTo prover stmt wit k k' rk >>= continueFromTo prover stmt wit k' m.castSucc),
          bind_assoc]
      refine bind_congr (fun rk => ?_)
      rw [← processRound_eq_bind]

/-- **Seam→`runToRound` bridge.**  `processRound 0` applied to the (pure) round-0 default state is
exactly `runToRound 1` (i.e. `runToRound (⟨0,hn⟩.succ)`).  Glue for the sequential-composition
right-block assembly: it turns the seam round's `processRound 0 (pure(default, input))` shape (from
the `append_continueFromTo_seam_start_*` lemmas) into `runToRound 1`, so `runToRound_eq_bind_continueFromTo`
can fold it with the interior `continueFromTo` into a single `runToRound`.  By `runToRound_succ` and the
definitional `runToRound 0 = pure(default, input)`. -/
theorem processRound_zero_pure_eq_runToRound {n : ℕ} {pSpec : ProtocolSpec n} (hn : 0 < n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (s : StmtIn) (w : WitIn) :
    prover.processRound (⟨0, hn⟩ : Fin n)
        (pure ((default : pSpec.Transcript (⟨0, by omega⟩ : Fin (n + 1))), prover.input (s, w)))
      = prover.runToRound (⟨0, hn⟩ : Fin n).succ s w := by
  rw [runToRound_succ]
  congr 1

/-- **P₂-side right-block assembly.**  The seam round's `processRound 0 (pure(default, input))` bound
with the interior continuation `continueFromTo 1 → last` is exactly `runToRound (Fin.last n)` — i.e.
the appended right block, projected to `P₂`, reconstructs `P₂`'s full run-to-round.  Combines
`processRound_zero_pure_eq_runToRound` (seam → `runToRound 1`) with `runToRound_eq_bind_continueFromTo`
(`runToRound 1 >>= continueFromTo 1 last = runToRound last`). -/
theorem processRound_zero_continueFromTo_eq_runToRound_last {n : ℕ} {pSpec : ProtocolSpec n}
    (hn : 0 < n) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (s : StmtIn) (w : WitIn) :
    (prover.processRound (⟨0, hn⟩ : Fin n)
        (pure ((default : pSpec.Transcript (⟨0, by omega⟩ : Fin (n + 1))), prover.input (s, w)))
      >>= prover.continueFromTo s w (⟨0, hn⟩ : Fin n).succ (Fin.last n))
      = prover.runToRound (Fin.last n) s w := by
  rw [processRound_zero_pure_eq_runToRound hn]
  exact (runToRound_eq_bind_continueFromTo prover s w (⟨0, hn⟩ : Fin n).succ (Fin.last n)
    (by rw [Fin.le_def, Fin.val_succ, Fin.val_last]; omega)).symm

/-- **`continueFromTo` target-index transport.**  Continuing to two propositionally-equal target
rounds is heterogeneously equal.  The non-`rw`-able bridge (the result type depends on the target, so
in-place rewriting hits a non-type-correct motive) for aligning `Fin.last`-shaped targets with the
`⟨k₀ + j⟩`-shaped targets produced by the right-block interior induction (`1 + (n-1) = n` is not
definitional).  Proved by `subst`. -/
theorem continueFromTo_heq_target {n : ℕ} {pSpec : ProtocolSpec n} {k j₁ j₂ : Fin (n + 1)}
    (h : j₁ = j₂) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (rk : pSpec.Transcript k × prover.PrvState k) :
    HEq (prover.continueFromTo stmt wit k j₁ rk) (prover.continueFromTo stmt wit k j₂ rk) := by
  subst h; rfl

/-- **`liftComp ∘ continueFromTo` target-index transport.**  The `liftComp`-lifted analogue of
`continueFromTo_heq_target`: continuing to two propositionally-equal target rounds and lifting along a
`SubSpec` is heterogeneously equal.  Used in the sequential-composition right-block assembly to align
the `liftComp`-of-`continueFromTo` produced by the interior induction (target `⟨k₀ + j⟩`) with the
`Fin.last` target of the run characterization.  Proved by `subst`. -/
theorem liftComp_continueFromTo_heq_target {n : ℕ} {pSpec : ProtocolSpec n} {k j₁ j₂ : Fin (n + 1)}
    (h : j₁ = j₂) {τ : Type} {superSpec : OracleSpec τ}
    [MonadLiftT (OracleQuery (oSpec + [pSpec.Challenge]ₒ)) (OracleQuery superSpec)]
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (rk : pSpec.Transcript k × prover.PrvState k) :
    HEq ((prover.continueFromTo stmt wit k j₁ rk).liftComp superSpec)
      ((prover.continueFromTo stmt wit k j₂ rk).liftComp superSpec) := by
  subst h; rfl

/-! ### Direction-resolved single-round peels

The two lemmas below resolve the `processRound` direction match into the two honest round shapes,
so a fixed-`n` honest run can be peeled one round at a time without unfolding the `match` by hand.
They sit on top of `runToRound_succ` (the one-round unfolding) and `processRound`'s definition. -/

/-- Unfold `processRound` into its `do`-block: take the previous round's `(transcript, state)`,
then branch on the round direction.  A rewrite handle; once the direction of the round is known use
the direction-resolved `runToRound_succ_challenge`/`runToRound_succ_message`. -/
theorem processRound_def (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
      prover.processRound j currentResult = (do
        let ⟨transcript, state⟩ ← currentResult
        match hDir : pSpec.dir j with
        | .V_to_P => do
          let challenge ← pSpec.getChallenge ⟨j, hDir⟩
          letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
          return ⟨transcript.concat challenge, newState⟩
        | .P_to_V => do
          let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
          return ⟨transcript.concat msg, newState⟩) := rfl

/-- **Message-round peel.** When round `j` is a `P_to_V` (prover-message) round, peeling one round
binds over the previous result and then runs `sendMessage`, appending the message to the
transcript. -/
theorem runToRound_succ_message (j : Fin n)
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hDir : pSpec.dir j = .P_to_V) :
      prover.runToRound j.succ stmt wit = (do
        let ⟨transcript, state⟩ ← prover.runToRound j.castSucc stmt wit
        let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
        return ⟨transcript.concat msg, newState⟩) := by
  rw [runToRound_succ, processRound_def]
  apply bind_congr
  rintro ⟨transcript, state⟩
  -- Collapse the tuple match, then resolve the direction match: the `V_to_P` branch is impossible
  -- by `hDir`, the `P_to_V` branch is the honest message shape (proof-irrelevant in `hDir`).
  dsimp only
  split <;> rename_i hDir'
  · exact absurd (hDir.symm.trans hDir') (by decide)
  · rfl

/-- **Challenge-round peel.** When round `j` is a `V_to_P` (verifier-challenge) round, peeling one
round binds over the previous result, samples the challenge, runs `receiveChallenge`, and appends
the challenge to the transcript. -/
theorem runToRound_succ_challenge (j : Fin n)
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hDir : pSpec.dir j = .V_to_P) :
      prover.runToRound j.succ stmt wit = (do
        let ⟨transcript, state⟩ ← prover.runToRound j.castSucc stmt wit
        let challenge ← pSpec.getChallenge ⟨j, hDir⟩
        letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
        return ⟨transcript.concat challenge, newState⟩) := by
  rw [runToRound_succ, processRound_def]
  apply bind_congr
  rintro ⟨transcript, state⟩
  -- Collapse the tuple match, then resolve the direction match: the `V_to_P` branch is the honest
  -- challenge shape, the `P_to_V` branch is impossible by `hDir`.
  dsimp only
  split <;> rename_i hDir'
  · rfl
  · exact absurd (hDir.symm.trans hDir') (by decide)

/-- **Full-run peel.** `Prover.run` is `runToRound (Fin.last n)` followed by `output`. This exposes
the head so that the run can be peeled round-by-round (via `runToRound_succ` and friends) down to
the `output` step. -/
theorem run_eq_runToRound_last
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.run stmt wit = (do
        let ⟨transcript, state⟩ ← prover.runToRound (Fin.last n) stmt wit
        return ⟨transcript, ← prover.output state⟩) := rfl

end Prover

end Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

section Trivial

end Trivial

section OptionTLifts

variable {α : Type} {pSpec : ProtocolSpec 1}

/-- Coercing an `OracleComp` into `OptionT` agrees with the explicit `OptionT.lift`. -/
lemma oracleComp_toOptionT_eq_lift (mx : OracleComp oSpec α) :
    ((mx : OptionT (OracleComp oSpec) α)) = OptionT.lift mx :=
  OptionT.liftM_def mx

/-- Lifting `OptionT.lift mx` across an oracle-spec extension is the same as first lifting `mx`
to the larger oracle spec and then lifting into `OptionT`. -/
lemma liftM_optionT_lift_eq_monadLift_liftM (mx : OracleComp oSpec α) :
    (liftM (OptionT.lift mx : OptionT (OracleComp oSpec) α) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) =
      (monadLift (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) := by
  rw [liftM_OptionT_eq]
  change
    (simulateQ (fun t => (liftM (OracleSpec.query t) :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) _)) (OptionT.lift mx).run) =
      (monadLift (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α).run
  rw [show OptionT.lift mx = OptionT.mk (some <$> mx) by
    apply OptionT.ext
    exact (map_eq_pure_bind some mx).symm]
  rw [show (monadLift (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α).run =
      some <$> (monadLift (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) α) by
        exact OptionT.run_monadLift (m := OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (n := OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α)]
  rw [monadLift_eq_self]
  change simulateQ (fun t => (liftM (OracleSpec.query t) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
    (some <$> mx) = some <$> (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α)
  rw [simulateQ_map]
  rw [show simulateQ (fun t => (liftM (OracleSpec.query t) :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
      mx = liftComp mx (oSpec + [pSpec.Challenge]ₒ) by rfl]
  rw [liftComp_eq_liftM]

/-- Directly lifting an `OracleComp` into `OptionT` over an extended oracle spec agrees with
first lifting the computation into the larger oracle spec and then into `OptionT`. -/
lemma liftM_oracleComp_eq_monadLift_liftM (mx : OracleComp oSpec α) :
    (liftM mx : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) =
      (monadLift (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) := by
  change (liftM ((mx : OptionT (OracleComp oSpec) α)) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) = _
  rw [oracleComp_toOptionT_eq_lift]
  exact liftM_optionT_lift_eq_monadLift_liftM (pSpec := pSpec) mx

/-- Interpreting a lifted `OptionT` computation against an appended oracle implementation ignores
the right-hand implementation when the lifted computation never queries it. -/
lemma simulateQ_add_run_liftM_left
    {ι₂ : Type} {spec₂ : OracleSpec ι₂} {σ : Type}
    (impl₁ : QueryImpl oSpec (StateT σ ProbComp))
    (impl₂ : QueryImpl spec₂ (StateT σ ProbComp))
    (oa : OptionT (OracleComp oSpec) α) :
    simulateQ (impl₁ + impl₂) (OptionT.run (liftM oa)) = simulateQ impl₁ oa.run := by
  rw [liftM_OptionT_eq]
  change simulateQ (impl₁ + impl₂) (liftM oa.run : OracleComp (oSpec + spec₂) (Option α)) = _
  rw [show (liftM oa.run : OracleComp (oSpec + spec₂) (Option α)) =
      liftComp oa.run (oSpec + spec₂) by rw [liftComp_eq_liftM]]
  rw [QueryImpl.simulateQ_add_liftComp_left]

omit pSpec in
/-- Interpreting a computation lifted through `spec₁ + (spec₂ + spec₃)` and then across the
add-association `SubSpec` against an implementation on `(spec₁ + spec₂) + spec₃` ignores the
right-hand implementation when the source computation only queries `spec₁ + spec₂`. -/
lemma simulateQ_add_liftComp_add_assoc_left
    {ι₁ ι₂ ι₃ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec₃ : OracleSpec ι₃} {σ : Type}
    (impl₁₂ : QueryImpl (spec₁ + spec₂) (StateT σ ProbComp))
    (impl₃ : QueryImpl spec₃ (StateT σ ProbComp))
    (oa : OracleComp (spec₁ + spec₂) α) :
    simulateQ (impl₁₂ + impl₃)
        (OracleComp.liftComp
          (OracleComp.liftComp oa (spec₁ + (spec₂ + spec₃)))
          ((spec₁ + spec₂) + spec₃)) =
      simulateQ impl₁₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => rfl
  | query_bind t oa ih =>
      rcases t with t | t
      · simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query, simulateQ_bind,
          simulateQ_query]
        refine bind_congr ?_
        intro x
        exact ih x
      · simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query, simulateQ_bind,
          simulateQ_query]
        refine bind_congr ?_
        intro x
        exact ih x

#print axioms simulateQ_add_liftComp_add_assoc_left

end OptionTLifts

section SingleMessage

/-! Simplification lemmas for protocols with a single message -/

variable {pSpec : ProtocolSpec 1}

end SingleMessage

section Classes

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}
    {pSpec : ProtocolSpec 2}

end Classes
