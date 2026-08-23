/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRun

/-!
# Partial (phase-2) run-to-round seam factoring (issue #13 / #114 / #29)

Companion to `SeamDecompositionRun.lean`.  That file proves the **full** run-level seam factoring
`Prover.run_seam_factor` (`P.run = (fst P).run >>= (snd P).run`, concatenating transcripts) and the
**phase-1 partial** run-to-round seam factoring `Prover.merge_runToRound_castLE` (relating
`P.runToRound (castLE j)` to `(fst P)`'s own run for `j : Fin (m+1)`).

What was missing — and is supplied here — is the **phase-2 partial** run-to-round seam factoring: the
`natAdd` analogue of `merge_runToRound_castLE`.  At a phase-2 round index `Fin.natAdd m k`
(`0 < k.val ≤ n`), the appended prover's partial run `P.runToRound (natAdd m k)` factors as `(fst P)`'s
full run (the seam output `P₁.output`, threaded into `P₂.input`) followed by `(snd P)`'s **own** partial
run to round `k`, with the phase-1 transcript prefixed via `Transcript.appendRight`.

This is exactly the brick the **phase-2** leg of `appendRbrKnowledgeSoundnessPerRound`
(`AppendRbrKnowledgeStateFunction.lean`) needs to reduce the appended log-free knowledge game at a
phase-2 challenge index `inr i₂` to the inner per-round bound `hBound₂` of `V₂.rbrKnowledgeSoundness`,
applied at `i₂` to the phase-2 prover `Prover.snd P` started from the realized seam statement
`verify stmtIn tr.fst`.

The proof reuses the entire `Append.lean` right-block continuation machinery — the seam start
(`append_continueFromTo_seam_start_message_processRound`), the interior fold
(`append_continueFromTo_right_interior`, which already takes an arbitrary number of interior rounds),
and the range-split (`continueFromTo_trans`) — but stops at the **partial** target `⟨m + k.val, _⟩`
instead of `Fin.last (m + n)`.  It is then welded onto `P` via the proven run-merge
`Prover.merge_runToRound`.  All declarations are axiom-clean and `sorry`-free.
-/

open OracleComp ProtocolSpec OracleVerifier.Append

universe u

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

/-- **HEq congruence for `Functor.map` in `OracleComp`** (the `map`-shaped analogue of
`bind_heq_congr`).  HEq base computations (over equal element types) and pointwise-HEq map functions
give HEq images.  Proved by rewriting `<$>` as `bind ∘ pure` and reusing `bind_heq_congr`. -/
theorem map_heq_congr {ι : Type} {spec : OracleSpec ι} {α α' β β' : Type _}
    (hα : α = α') (hβ : β = β')
    {f : α → β} {f' : α' → β'} {ma : OracleComp spec α} {ma' : OracleComp spec α'}
    (hf : ∀ (a : α) (a' : α'), HEq a a' → HEq (f a) (f' a')) (hma : HEq ma ma') :
    HEq (f <$> ma) (f' <$> ma') := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact bind_heq_congr hα hβ hma (fun a a' ha => pure_heq_pure hβ (hf a a' ha))

/-- **`continueFromTo` start-index transport.**  Continuing from two propositionally-equal start rounds
is heterogeneously equal (the start carries the round-`k` partial result, here HEq across the index
equality).  Proved by `subst`. -/
theorem continueFromTo_heq_start {Si So Wi Wo : Type} {ν : ℕ} {pSpec : ProtocolSpec ν}
    {k₁ k₂ j : Fin (ν + 1)} (h : k₁ = k₂) (prover : Prover oSpec Si Wi So Wo pSpec)
    (s : Si) (w : Wi) (rk₁ : pSpec.Transcript k₁ × prover.PrvState k₁)
    (rk₂ : pSpec.Transcript k₂ × prover.PrvState k₂) (hrk : HEq rk₁ rk₂) :
    HEq (prover.continueFromTo s w k₁ j rk₁) (prover.continueFromTo s w k₂ j rk₂) := by
  subst h; rw [eq_of_heq hrk]

/-- **`runToRound` index transport.**  Running to two propositionally-equal round indices is
heterogeneously equal.  Proved by `subst`. -/
theorem runToRound_heq_index {Si So Wi Wo : Type} {ν : ℕ} {pSpec : ProtocolSpec ν}
    {i₁ i₂ : Fin (ν + 1)} (h : i₁ = i₂) (prover : Prover oSpec Si Wi So Wo pSpec)
    (s : Si) (w : Wi) :
    HEq (prover.runToRound i₁ s w) (prover.runToRound i₂ s w) := by subst h; rfl

/-- **`liftComp ∘ continueFromTo` start-index transport.**  The `liftComp`-lifted analogue of
`continueFromTo_heq_start`.  Proved by `subst`. -/
theorem liftComp_continueFromTo_heq_start {Si So Wi Wo : Type} {ν : ℕ} {pSpec : ProtocolSpec ν}
    {k₁ k₂ j : Fin (ν + 1)} (h : k₁ = k₂) {τ : Type} {superSpec : OracleSpec τ}
    [MonadLiftT (OracleQuery (oSpec + [pSpec.Challenge]ₒ)) (OracleQuery superSpec)]
    (prover : Prover oSpec Si Wi So Wo pSpec)
    (s : Si) (w : Wi) (rk₁ : pSpec.Transcript k₁ × prover.PrvState k₁)
    (rk₂ : pSpec.Transcript k₂ × prover.PrvState k₂) (hrk : HEq rk₁ rk₂) :
    HEq ((prover.continueFromTo s w k₁ j rk₁).liftComp superSpec)
      ((prover.continueFromTo s w k₂ j rk₂).liftComp superSpec) := by
  subst h; rw [eq_of_heq hrk]

/-- **Partial right-block run characterization (message seam).**  The append-of-restrictions
continuation over the right block from the seam round `⟨m⟩` to the **partial** phase-2 target
`⟨m + k.val⟩` (`0 < k.val ≤ n`) is, heterogeneously, `P₁`'s output threaded into `P₂`'s **own**
`continueFromTo`-to-round-`k`, transported into the appended transcript via `appendRight`.

This is the partial-target analogue of `append_continueFromTo_right_msg` (which targets
`Fin.last (m + n)`).  Assembles the seam-start
(`append_continueFromTo_seam_start_message_processRound`), the interior fold
(`append_continueFromTo_right_interior` with `j = k.val - 1` interior rounds), the range-split
(`continueFromTo_trans`), and the `1 + (k-1) = k` index gaps bridged via `continueFromTo_heq_target` /
`liftComp_continueFromTo_heq_target`. -/
theorem append_continueFromTo_right_msg_partial (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (k : Fin (n + 1)) (hk : 0 < (k : ℕ))
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 = Transcript.appendRight T₁
      (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))) :
    HEq (Prover.continueFromTo (P₁.append P₂) stmt wit (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1)) rSeam)
      ((liftM (P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctx =>
        ((fun p => (Transcript.appendRight T₁ p.1,
            cast (by
              have h1 : (k : Fin (n + 1)) = (⟨(k : ℕ) - 1, by omega⟩ : Fin n).succ := by
                ext; simp; omega
              have h2 : (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
                  = (Fin.natAdd (m + 1) (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).cast (by omega) := by
                ext; simp; omega
              rw [h2]
              exact (congrArg P₂.PrvState h1).trans
                (append_PrvState_natAdd_succ (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).symm
              : P₂.PrvState k = (P₁.append P₂).PrvState ⟨m + (k : ℕ), by omega⟩) p.2)) <$>
          liftComp (P₂.runToRound k ctx.1 ctx.2)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
              × (P₁.append P₂).PrvState (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))))) := by
  -- Split the right block at the seam-successor `⟨m+1⟩`: seam round, then interior `m+1 .. m+k`.
  rw [continueFromTo_trans (P₁.append P₂) stmt wit (⟨m, by omega⟩ : Fin (m + n)).castSucc
    (⟨m, by omega⟩ : Fin (m + n)).succ (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
    (by rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
    (by rw [Fin.le_def, Fin.val_succ]; simp only [Fin.val_mk]; omega) rSeam]
  -- The seam factor: `P₁.output >>= P₂.processRound 0` on the empty-`pSpec₂` seam prefix.
  rw [eq_of_heq (append_continueFromTo_seam_start_message_processRound
    (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit) hn hDir hDir₂ T₁ rSeam hT)]
  simp only [bind_assoc, pure_bind]
  refine bind_heq_congr rfl rfl HEq.rfl (fun ctx ctx' hc => ?_)
  obtain rfl := eq_of_heq hc
  obtain ⟨c1, c2⟩ := ctx
  -- `P₂.processRound 0 (pure (default, P₂.input ·)) = P₂.runToRound 1`.
  rw [processRound_zero_pure_eq_runToRound hn P₂ c1 c2]
  -- The RHS `P₂.runToRound k` factors at the seam-successor: `runToRound 1 >>= continueFromTo 1 k`.
  have hP2run : (P₂.runToRound k c1 c2 : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
      = P₂.runToRound (⟨0, hn⟩ : Fin n).succ c1 c2 >>=
          P₂.continueFromTo c1 c2 (⟨0, hn⟩ : Fin n).succ k :=
    runToRound_eq_bind_continueFromTo P₂ c1 c2 (⟨0, hn⟩ : Fin n).succ k
      (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_mk]; omega)
  rw [hP2run, OracleComp.liftComp_bind, ← bind_pure_comp, bind_assoc]
  -- Bind over the seam-round-1 partial run on both sides; reduce to the interior continuation.
  refine bind_heq_congr rfl rfl
    (by rw [← OracleComp.liftComp_eq_liftM]) (fun p p' hp => ?_)
  obtain rfl := eq_of_heq hp
  rcases Nat.lt_or_ge (k : ℕ) 2 with hlt | hge
  · -- k = 1 (incl. the `n = 1` boundary): no interior rounds; both sides `pure (bridge p)`.
    -- `subst` the concrete index `k = ⟨0,hn⟩.succ` (handles all `k`-dependent casts definitionally).
    have hkeq : (k : Fin (n + 1)) = (⟨0, hn⟩ : Fin n).succ := by ext; simp; omega
    subst hkeq
    have hLtgt : ((⟨m, by omega⟩ : Fin (m + n)).succ : Fin (m + n + 1))
        = (⟨m + ((⟨0, hn⟩ : Fin n).succ : ℕ), by omega⟩ : Fin (m + n + 1)) := by ext; simp
    -- LHS: `continueFromTo (⟨m⟩.succ) (⟨m+1⟩) = continueFromTo (⟨m⟩.succ) (⟨m⟩.succ) = pure rk`.
    refine HEq.trans (continueFromTo_heq_target hLtgt.symm (P₁.append P₂) stmt wit _) ?_
    rw [continueFromTo_self]
    -- RHS: `P₂.continueFromTo 0.succ 0.succ p = pure p`.
    rw [continueFromTo_self]
    apply heq_of_eq
    simp only [OracleComp.liftComp_pure, map_pure]
    refine congrArg pure (Prod.ext rfl (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)))
  · -- k ≥ 2 (so n ≥ 2): fold the `k-1` interior rounds via `append_continueFromTo_right_interior`.
    have eStart : ((⟨m, by omega⟩ : Fin (m + n)).succ : Fin (m + n + 1))
        = (Fin.natAdd m (⟨1, by omega⟩ : Fin n)).castSucc := by ext; simp
    have eTgt : (⟨m + ((1 : ℕ) + ((k : ℕ) - 1)), by omega⟩ : Fin (m + n + 1))
        = (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1)) := by ext; simp only [Fin.val_mk]; omega
    have eR : (⟨(1 : ℕ) + ((k : ℕ) - 1), by omega⟩ : Fin (n + 1)) = k := by
      ext; simp only [Fin.val_mk]; omega
    -- LHS: transport the start index `⟨m⟩.succ = (natAdd m ⟨1⟩).castSucc` (HEq, not `rw`).  The target
    -- start matches `hint`'s input shape `(appendRight T₁ p.1, cast (natAdd_castSucc).symm p.2)`.
    refine HEq.trans (continueFromTo_heq_start (j := (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1)))
      eStart (P₁.append P₂) stmt wit
      (Transcript.appendRight T₁ p.1, cast (append_PrvState_seam_succ hn).symm p.2)
      (Transcript.appendRight T₁ p.1,
        cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) (⟨1, by omega⟩ : Fin n)
          (by simp)).symm p.2)
      (prodMk_heq (by rw [eStart]) (by rw [eStart]) HEq.rfl
        ((cast_heq _ _).trans (cast_heq _ _).symm))) ?_
    refine HEq.trans (continueFromTo_heq_target eTgt.symm (P₁.append P₂) stmt wit
      (Transcript.appendRight T₁ p.1,
        cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) (⟨1, by omega⟩ : Fin n)
          (by simp)).symm p.2)) ?_
    have hint := append_continueFromTo_right_interior (P₁ := P₁) (P₂ := P₂)
      (stmt := stmt) (wit := wit) (stmt₂ := c1) (wit₂ := c2)
      T₁ (⟨1, by omega⟩ : Fin n) (by simp) ((k : ℕ) - 1)
      (by simp only [Fin.val_mk]; omega) p
    rw [bind_pure_comp] at hint
    refine HEq.trans hint ?_
    -- RHS reconciliation: align the `P₂.continueFromTo` target index `1+(k-1) = k` and start `1 = 0.succ`.
    have happ : ∀ {j₁ j₂ : Fin (n + 1)} (hj : j₁ = j₂) {u : pSpec₂.Transcript j₁}
        {u' : pSpec₂.Transcript j₂}, HEq u u' →
        HEq (Transcript.appendRight T₁ u) (Transcript.appendRight T₁ u') := by
      intro j₁ j₂ hj u u' hu; subst hj; rw [eq_of_heq hu]
    refine map_heq_congr (by rw [eR]) (by rw [eTgt]) (fun a a' ha => ?_)
      (HEq.trans (liftComp_continueFromTo_heq_target eR P₂ c1 c2 p)
        (liftComp_continueFromTo_heq_start
          (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          (show (⟨1, by omega⟩ : Fin n).castSucc = (⟨0, hn⟩ : Fin n).succ from by ext; simp)
          P₂ c1 c2 _ p HEq.rfl))
    obtain ⟨t, s⟩ := a
    obtain ⟨t', s'⟩ := a'
    obtain ⟨ht, hs⟩ := prod_heq_split (by rw [eR]) (by rw [eR]) ha
    refine prodMk_heq (by rw [eTgt]) (by rw [eTgt]) (happ eR ht)
      ((cast_heq _ _).trans (hs.trans (cast_heq _ _).symm))

end Prover

namespace Prover

variable {P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)}

/-- **Phase-2 partial run-to-round seam factoring (`natAdd` analogue of `merge_runToRound_castLE`).**
At a phase-2 round index `Fin.natAdd m k` (`0 < k.val ≤ n`), the appended prover's partial run
`P.runToRound (natAdd m k)` factors — heterogeneously — as `(fst P)`'s full run (the seam output,
threaded into `P₂.input`) followed by `(snd P)`'s **own** partial run to round `k`, with the realized
phase-1 transcript prefixed via `Transcript.appendRight`.

This is the phase-2 brick (the `natAdd` analogue of the phase-1 partial `merge_runToRound_castLE`) that
the phase-2 leg of `appendRbrKnowledgeSoundnessPerRound` needs.  Assembles the partial right-block
characterization `append_continueFromTo_right_msg_partial` (for the append of `fst`/`snd`), the seam
split (`runToRound_eq_bind_continueFromTo` at `k = ⟨m⟩`, `append_runToRound_seam`), and welds onto `P`
via the proven run-merge `merge_runToRound`.

The output is presented as: run `(fst P)` to completion (its run is `liftM`-ed), feed the seam output
through `P₂.input` (`= (snd P).input`), then `(snd P).runToRound k` from there, bridging the transcript
by `appendRight` of the realized phase-1 transcript onto the phase-2 partial transcript. -/
theorem snd_runToRound_natAdd_seam (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (k : Fin (n + 1)) (hk : 0 < (k : ℕ)) (stmt : Stmt₁) (wit : Wit₁) :
    HEq (P.runToRound (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1)) stmt wit)
      (do
        let ⟨transcript₁, ctxIn₂⟩ ← liftM ((Prover.fst P).run stmt wit)
        let r ← liftM ((Prover.snd P).runToRound k ctxIn₂.1 ctxIn₂.2)
        (pure (Transcript.appendRight transcript₁ r.1,
            cast (by
              have h1 : (k : Fin (n + 1)) = (⟨(k : ℕ) - 1, by omega⟩ : Fin n).succ := by
                ext; simp; omega
              have h2 : (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
                  = (Fin.natAdd (m + 1) (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).cast (by omega) := by
                ext; simp; omega
              rw [h2]
              exact (congrArg (Prover.snd P).PrvState h1).trans
                (append_PrvState_natAdd_succ (P₁ := Prover.fst P) (P₂ := Prover.snd P)
                  (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).symm
              : (Prover.snd P).PrvState k
                = ((Prover.fst P).append (Prover.snd P)).PrvState
                    (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))) r.2)
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
                × ((Prover.fst P).append (Prover.snd P)).PrvState
                    (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))))) := by
  -- Weld onto `P` via the run-merge, then work with the append-of-restrictions.
  refine HEq.trans (merge_runToRound P stmt wit (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))).symm ?_
  -- Seam-split the append-of-restrictions run at `k = ⟨m⟩`.
  rw [runToRound_eq_bind_continueFromTo ((Prover.fst P).append (Prover.snd P)) stmt wit
        (⟨m, by omega⟩ : Fin (m + n + 1)) (⟨m + (k : ℕ), by omega⟩ : Fin (m + n + 1))
        (by simp only [Fin.le_def, Fin.val_mk]; omega)]
  rw [show (⟨m, by omega⟩ : Fin (m + n + 1)) = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by
        ext; simp]
  -- The seam state: `runToRound ⟨m⟩` of the append is `fst`'s run-to-`last m`.
  have hidx : ((Fin.last m).castLE (by omega) : Fin (m + n + 1))
      = (⟨m, by omega⟩ : Fin (m + n)).castSucc := by ext; simp
  have hseam : HEq (((Prover.fst P).append (Prover.snd P)).runToRound
        (⟨m, by omega⟩ : Fin (m + n)).castSucc stmt wit)
      (liftM ((Prover.fst P).runToRound (Fin.last m) stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) :=
    HEq.trans
      (runToRound_heq_index hidx.symm ((Prover.fst P).append (Prover.snd P)) stmt wit)
      (append_runToRound_seam (P₁ := Prover.fst P) (P₂ := Prover.snd P) (stmt := stmt) (wit := wit))
  -- Rewrite the appended-seam continuation per realized seam state via the partial characterization
  -- (mirrors `appendRunRightResidual_holds_msg`).
  conv_lhs =>
    enter [2, rSeam]
    rw [eq_of_heq (append_continueFromTo_right_msg_partial (P₁ := Prover.fst P) (P₂ := Prover.snd P)
      (stmt := stmt) (wit := wit) hn hDir hDir₂ k hk
      (cast (append_Transcript_seam_castSucc hn) rSeam.1) rSeam
      (seam_transcript_appendRight hn rSeam.1))]
  -- Expand the target `liftM (fst.run) = liftM (runToRound (last m) >>= output)`, normalize lifts
  -- (directly on the `HEq` goal, since the seam-runToRound parts differ in type).
  simp only [run_eq_runToRound_last, liftM_bind, bind_assoc, liftM_pure, pure_bind,
    bind_map_left, Function.comp, OracleComp.liftComp_eq_liftM]
  -- Bind over the seam: appended-seam-runToRound ≍ `liftM (fst.runToRound last)` via `hseam`.
  refine bind_heq_congr
    (by rw [append_Transcript_seam_castSucc hn, append_PrvState_seam_castSucc hn]; rfl) rfl
    hseam (fun rSeam x hr => ?_)
  -- per-seam-state continuation equality (collapse the seam `cast`s à la `appendRunRightResidual_holds_msg`).
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_seam_castSucc hn)
    (append_PrvState_seam_castSucc hn) hr
  have hc2 : cast (append_PrvState_seam_castSucc hn) rSeam.2 = x.2 :=
    eq_of_heq ((cast_heq _ _).trans hs)
  have hc1 : cast (append_Transcript_seam_castSucc hn) rSeam.1 = x.1 :=
    eq_of_heq ((cast_heq _ _).trans ht)
  rw [hc2, hc1]
  apply heq_of_eq
  refine bind_congr (fun ctx => ?_)
  -- `bridge <$> liftM (snd.runToRound k ctx) = liftM (snd.runToRound k ctx) >>= pure ∘ bridge`.
  rw [bind_pure_comp]

end Prover

#print axioms Prover.append_continueFromTo_right_msg_partial
#print axioms Prover.snd_runToRound_natAdd_seam
