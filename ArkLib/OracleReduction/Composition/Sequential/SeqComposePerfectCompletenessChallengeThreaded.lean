/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.SeqComposePerfectCompletenessThreaded
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessChallenge
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeOracleCompleteness

/-!
# n-ary challenge-seam `seqCompose` perfect completeness

The `V_to_P`-leading analogue of `Reduction.seqCompose_perfectCompleteness_threaded`
(`SeqComposePerfectCompletenessThreaded.lean`): every component protocol is nonempty and
**challenge-leading** (its first round is `V_to_P`), so each induction seam is a challenge seam,
discharged by the proven binary keystone `Reduction.append_perfectCompleteness_challenge`
(`AppendPerfectCompletenessChallenge.lean`). The empty-tail base case is shared with the
message-seam version (`append_perfectCompleteness_empty_proof`).

This is the missing n-ary engine for **challenge-leading round chains** such as the FRI folding
phase (`FoldPhase.pSpec` is `[V_to_P, P_to_V]` for every round), whose composed perfect
completeness was previously stuck behind the message-leading-only threaded keystone.

Side conditions: the challenge keystone consumes the state-preservation/never-failing impl
conditions (`himplSP`/`himplNF`), the empty base case consumes `hImplSupp`; all three are
vacuous for `oSpec = []ₒ` consumers (no shared oracles).
-/

namespace ProtocolSpec

/-- **Append-validity of a `seqCompose` of `V_to_P`-leading components.** If every component
protocol is nonempty and its first round is a `V_to_P` challenge, then their `seqCompose` is
either empty (no components) or itself nonempty with a leading `V_to_P` challenge. Mirror of
`seqCompose_appendValid` with the direction flipped. -/
theorem seqCompose_appendValid_challenge {m : ℕ} {n : Fin m → ℕ}
    {pSpec : ∀ i, ProtocolSpec (n i)}
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .V_to_P) :
    Fin.vsum n = 0 ∨ ∃ h : 0 < Fin.vsum n, (seqCompose pSpec).dir ⟨0, h⟩ = .V_to_P := by
  cases m with
  | zero => left; rfl
  | succ k =>
    right
    have h0 := hValid 0
    obtain ⟨hpos0, hdir0⟩ := h0
    have hvsum_pos : 0 < Fin.vsum n := by
      rw [Fin.vsum_succ]
      omega
    refine ⟨hvsum_pos, ?_⟩
    rw [seqCompose_succ_eq_append]
    show (append (pSpec 0) (seqCompose fun i => pSpec (Fin.succ i))).dir ⟨0, hvsum_pos⟩ = .V_to_P
    rw [show (⟨0, hvsum_pos⟩ : Fin (n 0 + Fin.vsum fun i => n (Fin.succ i)))
          = (⟨0, hpos0⟩ : Fin (n 0)).castLE (by omega) from by ext; simp,
      Prover.append_dir_castLE]
    exact hdir0

end ProtocolSpec

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Empty-append challenge `OracleInterface` (local copy of the instance scoped to the
message-seam threaded file, which is not exported). -/
local instance instAppendEmptyChallengeOI' {k₁ : ℕ} {p₁ : ProtocolSpec k₁} :
    ∀ i, OracleInterface ((p₁ ++ₚ (!p[] : ProtocolSpec 0)).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

set_option maxHeartbeats 1000000 in
set_option linter.unusedFintypeInType false in
/-- **n-ary challenge-seam `seqCompose` perfect completeness, keystones inlined.** Every
component is nonempty and `V_to_P`-leading (`hValid`) and perfectly complete (`h`); with
per-round challenge finiteness/inhabitedness the seam instances are discharged locally, and the
binary challenge-seam append keystone is applied at each step (empty seam for the final
single-component step). -/
theorem seqCompose_perfectCompleteness_challenge_threaded {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Fintype ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Inhabited ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .V_to_P)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  induction m with
  | zero =>
    rw [seqCompose_zero]
    simpa using
      (Reduction.id_perfectCompleteness (init := init) (impl := impl) (rel := rel 0))
  | succ m ih =>
    change ((R 0).append
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))))
      |>.perfectCompleteness init impl (rel 0) (rel (Fin.succ (Fin.last m)))
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- Empty trailing seam (`m = 0`): same base case as the message-seam version.
      subst hm
      rw [Reduction.seqCompose_zero]
      haveI : (oSpec + [(pSpec 0).Challenge]ₒ).Fintype := by
        haveI := challengeOracle_fintype (pSpec 0); infer_instance
      haveI : (oSpec + [(pSpec 0).Challenge]ₒ).Inhabited := by
        haveI := challengeOracle_inhabited (pSpec 0); infer_instance
      haveI : [(!p[] : ProtocolSpec 0).Challenge]ₒ.Fintype := { fintype_B := fun t => t.1.1.elim0 }
      haveI : [(!p[] : ProtocolSpec 0).Challenge]ₒ.Inhabited :=
        { inhabited_B := fun t => t.1.1.elim0 }
      haveI : (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ).Fintype := inferInstance
      haveI : (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ).Inhabited := inferInstance
      haveI : ∀ j, Fintype ((!p[] : ProtocolSpec 0).Challenge j) := fun j => j.1.elim0
      haveI : ∀ j, Fintype ((pSpec 0 ++ₚ (!p[] : ProtocolSpec 0)).Challenge j) :=
        appendChallenge_fintype (pSpec 0) (!p[] : ProtocolSpec 0)
      haveI : ∀ j, Inhabited ((!p[] : ProtocolSpec 0).Challenge j) := fun j => j.1.elim0
      haveI : ∀ j, Inhabited ((pSpec 0 ++ₚ (!p[] : ProtocolSpec 0)).Challenge j) :=
        appendChallenge_inhabited (pSpec 0) (!p[] : ProtocolSpec 0)
      haveI : (oSpec + [((pSpec 0) ++ₚ (!p[] : ProtocolSpec 0)).Challenge]ₒ).Fintype := by
        haveI := challengeOracle_fintype (pSpec 0 ++ₚ (!p[] : ProtocolSpec 0)); infer_instance
      haveI : (oSpec + [((pSpec 0) ++ₚ (!p[] : ProtocolSpec 0)).Challenge]ₒ).Inhabited := by
        haveI := challengeOracle_inhabited (pSpec 0 ++ₚ (!p[] : ProtocolSpec 0)); infer_instance
      refine append_perfectCompleteness_empty_proof (R 0) Reduction.id (h 0) ?_ hInit hImplSupp
      exact Reduction.id_perfectCompleteness (init := init) (impl := impl) (rel := rel 1)
    · -- Challenge seam: the tail is nonempty and starts with a `V_to_P` challenge.
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      haveI : ∀ j, Fintype ((ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge j) :=
        seqComposeChallenge_fintype (fun i => pSpec (Fin.succ i))
      haveI : ∀ j, Inhabited
          ((ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge j) :=
        seqComposeChallenge_inhabited (fun i => pSpec (Fin.succ i))
      haveI : (oSpec + [(pSpec 0).Challenge]ₒ).Fintype := by
        haveI := challengeOracle_fintype (pSpec 0); infer_instance
      haveI : (oSpec + [(pSpec 0).Challenge]ₒ).Inhabited := by
        haveI := challengeOracle_inhabited (pSpec 0); infer_instance
      haveI :
          (oSpec + [(ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge]ₒ).Fintype :=
        seqComposeCombinedOracle_fintype oSpec (fun i => pSpec (Fin.succ i))
      haveI :
          (oSpec +
            [(ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge]ₒ).Inhabited :=
        seqComposeCombinedOracle_inhabited oSpec (fun i => pSpec (Fin.succ i))
      haveI :
          (oSpec + [((pSpec 0) ++ₚ
            (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).Challenge]ₒ).Fintype :=
        appendCombinedOracle_fintype oSpec (pSpec 0)
          (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))
      haveI :
          (oSpec + [((pSpec 0) ++ₚ
            (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).Challenge]ₒ).Inhabited :=
        appendCombinedOracle_inhabited oSpec (pSpec 0)
          (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))
      have hn : 0 < Fin.vsum (fun i => n (Fin.succ i)) := by
        rw [Fin.vsum_succ]; have := (hValid (Fin.succ 0)).1; omega
      obtain ⟨hpos, hdir⟩ :=
        (ProtocolSpec.seqCompose_appendValid_challenge (pSpec := fun i => pSpec (Fin.succ i))
          (fun i => hValid (Fin.succ i))).resolve_left (by omega)
      have hDir₂ : (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).dir ⟨0, hpos⟩
          = .V_to_P := hdir
      have hDir : ((pSpec 0) ++ₚ (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).dir
          (⟨n 0, by omega⟩ : Fin (n 0 + Fin.vsum (fun i => n (Fin.succ i)))) = .V_to_P := by
        rw [show (⟨n 0, by omega⟩ : Fin (n 0 + Fin.vsum (fun i => n (Fin.succ i))))
              = Fin.natAdd (n 0) ⟨0, hpos⟩ from by ext; simp]
        rw [Prover.append_dir_natAdd]; exact hDir₂
      refine append_perfectCompleteness_challenge (R 0)
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i)))
        (h 0) ?_ hpos hDir hDir₂ himplSP himplNF hInit
      exact ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))
        (fun i => rel (Fin.succ i)) (fun i => hValid (Fin.succ i)) (fun i => h (Fin.succ i))

end Reduction

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
set_option linter.unusedFintypeInType false in
/-- **n-ary challenge-seam `seqCompose` perfect completeness for oracle reductions.** Every
component is nonempty and `V_to_P`-leading (`hValid`) and perfectly complete (`h`); with
per-round challenge finiteness/inhabitedness the oracle-level `seqCompose` is perfectly
complete. Pure pass-through to `Reduction.seqCompose_perfectCompleteness_challenge_threaded`
via the structural `toReduction` bridge `seqCompose_toReduction` (exactly as the message-seam
`seqCompose_perfectCompleteness_threaded` in `SeqComposeOracleCompleteness.lean`). -/
theorem seqCompose_perfectCompleteness_challenge_threaded {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Fintype ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Inhabited ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (R i).verifier]
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .V_to_P)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt OStmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  change Reduction.perfectCompleteness init impl (rel 0) (rel (Fin.last m))
    (seqCompose Stmt OStmt Wit R).toReduction
  rw [seqCompose_toReduction Stmt OStmt Wit R]
  exact Reduction.seqCompose_perfectCompleteness_challenge_threaded
    (fun i => Stmt i × (∀ j, OStmt i j)) Wit
    (fun i => (R i).toReduction) rel hValid hInit hImplSupp himplSP himplNF h

end OracleReduction

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProtocolSpec.seqCompose_appendValid_challenge
#print axioms Reduction.seqCompose_perfectCompleteness_challenge_threaded
#print axioms OracleReduction.seqCompose_perfectCompleteness_challenge_threaded
