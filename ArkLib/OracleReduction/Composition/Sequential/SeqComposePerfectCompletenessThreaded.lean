/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessProof
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessEmpty
import ArkLib.OracleReduction.Composition.Sequential.ChallengeOracleFintype
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeMsgCompleteness

/-!
# n-ary message-seam `seqCompose` perfect completeness — keystones inlined (issue #114)

`Reduction.seqCompose_perfectCompleteness_of_append_msg` reduces the n-ary message-seam composition to
a binary `hAppend` keystone, but its `hAppend` hypothesis is ∀-quantified over arbitrary seams with
only `[∀ j, SampleableType (p.Challenge j)]`, whereas the proven binary keystones
(`append_perfectCompleteness_msg_proof`, `append_perfectCompleteness_empty_proof`) additionally
require `[(oSpec + [(p₁ ++ₚ p₂).Challenge]ₒ).Fintype]` / `.Inhabited` on each seam — which do **not**
synthesize from `SampleableType`. So that lemma cannot be discharged with the real keystones.

This module supplies `Reduction.seqCompose_perfectCompleteness_threaded`, which threads the per-round
finiteness/inhabitedness `[∀ i j, Fintype/Inhabited ((pSpec i).Challenge j)]` (true for every concrete
protocol — sum-check challenges are the field `R`) and **inlines** the keystone at each induction step:
the seam instances are constructed from `ChallengeOracleFintype` (`appendCombinedOracle_*`,
`seqComposeCombinedOracle_*`, `challengeOracle_*`), and the message/empty split is by `Nat.eq_zero_or_pos`
on the number of trailing components — so the empty-tail case is `seqCompose` over `Fin 0`, whose length
`Fin.vsum` is **definitionally** `0`.

Both branches are proven (axiom-clean): the multi-round **message-seam** step via
`append_perfectCompleteness_msg_proof`, and the degenerate **single-component** step (`m = 0`, the
tail `seqCompose` over `Fin 0` rewritten to `Reduction.id` whose protocol is the empty literal
`!p[]`) via `append_perfectCompleteness_empty_proof` + `Reduction.id_perfectCompleteness`.  The only
subtlety in the empty step is the empty-protocol-append challenge oracle, whose `OracleInterface`
(`instAppendEmptyChallengeOI`) and vacuous finiteness are introduced explicitly.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The challenge `OracleInterface` of an append with an **empty trailing protocol** `!p[]`.  The
generic `ProtocolSpec.challengeOracleInterface` provides this, but it is not picked up automatically
for the empty append (`!p[]` triggers competing empty-index instances), so it is exposed explicitly
here.  Scoped local to the empty-seam base case of `seqCompose_perfectCompleteness_threaded`. -/
local instance instAppendEmptyChallengeOI {k₁ : ℕ} {p₁ : ProtocolSpec k₁} :
    ∀ i, OracleInterface ((p₁ ++ₚ (!p[] : ProtocolSpec 0)).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

set_option maxHeartbeats 1000000 in
set_option linter.unusedFintypeInType false in
/-- **n-ary message-seam `seqCompose` perfect completeness, keystones inlined.** Every component is
nonempty and `P_to_V`-leading (`hValid`) and perfectly complete (`h`); with per-round challenge
finiteness/inhabitedness the seam instances are discharged locally, and the binary append keystone is
applied directly (message seam for a nonempty tail, empty seam for the final single-component step). -/
theorem seqCompose_perfectCompleteness_threaded {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Fintype ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Inhabited ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftM q : OracleComp oSpec β))
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
    · -- Empty trailing seam (`m = 0`): the tail `seqCompose` over `Fin 0` is `Reduction.id`, whose
      -- protocol is the empty literal `!p[] : ProtocolSpec 0`.  Rewrite the tail to `Reduction.id`,
      -- then apply the empty keystone with `Reduction.id_perfectCompleteness`.  The only subtlety is
      -- the empty-protocol-append seam instances `(oSpec + [(pSpec 0 ++ₚ !p[]).Challenge]ₒ).*`, which
      -- need the `(pSpec 0 ++ₚ !p[]).Challenge` `OracleInterface` introduced explicitly (the generic
      -- `challengeOracleInterface` does not get picked up automatically for the empty append) plus the
      -- vacuous finiteness of `!p[]`'s challenges, routed through `ChallengeOracleFintype`.
      subst hm
      rw [Reduction.seqCompose_zero]
      -- left phase `pSpec 0` (uses the generic `challengeOracleInterface`):
      haveI : (oSpec + [(pSpec 0).Challenge]ₒ).Fintype := by
        haveI := challengeOracle_fintype (pSpec 0); infer_instance
      haveI : (oSpec + [(pSpec 0).Challenge]ₒ).Inhabited := by
        haveI := challengeOracle_inhabited (pSpec 0); infer_instance
      -- right phase `!p[]`: the empty challenge oracle resolves its `OracleInterface` to
      -- `instElim0` (empty `Fin 0` index), so its `Fintype`/`Inhabited` are constructed directly
      -- (vacuously) rather than through `challengeOracle_fintype` (which would carry the generic
      -- `challengeOracleInterface`, a different instance):
      haveI : [(!p[] : ProtocolSpec 0).Challenge]ₒ.Fintype := { fintype_B := fun t => t.1.1.elim0 }
      haveI : [(!p[] : ProtocolSpec 0).Challenge]ₒ.Inhabited := { inhabited_B := fun t => t.1.1.elim0 }
      haveI : (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ).Fintype := inferInstance
      haveI : (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ).Inhabited := inferInstance
      -- combined seam `pSpec 0 ++ₚ !p[]` (`OracleInterface` from `instAppendEmptyChallengeOI`):
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
    · -- Message seam: the tail is nonempty and starts with a `P_to_V` message.
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      haveI : ∀ j, Fintype ((ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge j) :=
        seqComposeChallenge_fintype (fun i => pSpec (Fin.succ i))
      haveI : ∀ j, Inhabited ((ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge j) :=
        seqComposeChallenge_inhabited (fun i => pSpec (Fin.succ i))
      haveI : (oSpec + [(pSpec 0).Challenge]ₒ).Fintype := by
        haveI := challengeOracle_fintype (pSpec 0); infer_instance
      haveI : (oSpec + [(pSpec 0).Challenge]ₒ).Inhabited := by
        haveI := challengeOracle_inhabited (pSpec 0); infer_instance
      haveI : (oSpec + [(ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge]ₒ).Fintype :=
        seqComposeCombinedOracle_fintype oSpec (fun i => pSpec (Fin.succ i))
      haveI : (oSpec + [(ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge]ₒ).Inhabited :=
        seqComposeCombinedOracle_inhabited oSpec (fun i => pSpec (Fin.succ i))
      haveI :
          (oSpec + [((pSpec 0) ++ₚ (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).Challenge]ₒ).Fintype :=
        appendCombinedOracle_fintype oSpec (pSpec 0) (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))
      haveI :
          (oSpec + [((pSpec 0) ++ₚ (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).Challenge]ₒ).Inhabited :=
        appendCombinedOracle_inhabited oSpec (pSpec 0) (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))
      have hn : 0 < Fin.vsum (fun i => n (Fin.succ i)) := by
        rw [Fin.vsum_succ]; have := (hValid (Fin.succ 0)).1; omega
      obtain ⟨hpos, hdir⟩ :=
        (ProtocolSpec.seqCompose_appendValid (pSpec := fun i => pSpec (Fin.succ i))
          (fun i => hValid (Fin.succ i))).resolve_left (by omega)
      have hDir₂ : (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).dir ⟨0, hpos⟩ = .P_to_V := hdir
      have hDir : ((pSpec 0) ++ₚ (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).dir
          (⟨n 0, by omega⟩ : Fin (n 0 + Fin.vsum (fun i => n (Fin.succ i)))) = .P_to_V := by
        rw [show (⟨n 0, by omega⟩ : Fin (n 0 + Fin.vsum (fun i => n (Fin.succ i))))
              = Fin.natAdd (n 0) ⟨0, hpos⟩ from by ext; simp]
        rw [Prover.append_dir_natAdd]; exact hDir₂
      refine append_perfectCompleteness_msg_proof (R 0)
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i)))
        (h 0) ?_ hpos hDir hDir₂ hInit hImplSupp
      exact ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))
        (fun i => rel (Fin.succ i)) (fun i => hValid (Fin.succ i)) (fun i => h (Fin.succ i))

end Reduction
