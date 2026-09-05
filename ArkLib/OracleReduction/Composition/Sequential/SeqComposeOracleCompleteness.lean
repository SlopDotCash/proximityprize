/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendOracleAdapters
import ArkLib.OracleReduction.Composition.Sequential.SeqComposePerfectCompletenessThreaded

/-!
# n-ary message-seam `seqCompose` perfect completeness for **oracle** reductions (issue #29)

`Reduction.seqCompose_perfectCompleteness_threaded`
(`SeqComposePerfectCompletenessThreaded.lean`) is the fully-proven `Reduction`-level engine:
the `seqCompose` of `P_to_V`-leading, perfectly-complete component reductions is perfectly
complete. The ring-switching / BCS consumers compose **oracle** reductions
(`OracleReduction.seqCompose`), whose `seqCompose` definitionally unfolds (via
`OracleReduction.seqCompose_succ`/`seqCompose_zero`) into a tower of `OracleReduction.append`s and
`OracleReduction.id`.

`OracleReduction.perfectCompleteness oR` is *definitionally* `Reduction.perfectCompleteness
oR.toReduction`. So the only content needed to lift the engine to the oracle setting is the
structural bridge

  `(OracleReduction.seqCompose Stmt OStmt Wit R).toReduction
     = Reduction.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit (fun i => (R i).toReduction)`,

i.e. that the oracle `seqCompose`'s `Verifier` image is the `Reduction`-level `seqCompose` of the
component `Verifier` images. This file proves that bridge by induction (`seqCompose_toReduction`,
discharging each append seam with the already-proven `appendToReductionResidual_proof`), and then
the oracle-level n-ary keystone `OracleReduction.seqCompose_perfectCompleteness_threaded` is a pure
rewrite into the `Reduction`-level engine — no new probabilistic content, no `sorry`, no residual.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- **Structural `toReduction`/`seqCompose` bridge.** The `Reduction` image of a `seqCompose`d
oracle reduction is the `Reduction`-level `seqCompose` of the component `Reduction` images.

Proven by induction on `m`: the base case is `OracleReduction.id_toReduction` (the empty
`seqCompose` is `OracleReduction.id`, whose image is `Reduction.id`, the empty `Reduction`
`seqCompose`); the step unfolds both sides via `seqCompose_succ` to a binary `append` and uses
`appendToReductionResidual_proof` (`(R₁.append R₂).toReduction = R₁.toReduction.append
R₂.toReduction`) plus the inductive hypothesis. -/
theorem seqCompose_toReduction {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (R i).verifier] :
    (seqCompose Stmt OStmt Wit R).toReduction
      = Reduction.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit
          (fun i => (R i).toReduction) := by
  induction m with
  | zero =>
    rw [seqCompose_zero, Reduction.seqCompose_zero]
    exact OracleReduction.id_toReduction
  | succ m ih =>
    -- coherence of the (recursively-coherent) tail `seqCompose`, built from the per-leaf coherence
    -- `fun i => coh i.succ` (matching the tail's reindexed oracle interfaces).
    haveI hcohLeaf : ∀ i : Fin m, OracleVerifier.Append.AppendCoherent
        (Oₛ₁ := fun j => Oₛ (Fin.succ i).castSucc j) (Oₛ₂ := fun j => Oₛ (Fin.succ i).succ j)
        (Oₘ₁ := Oₘ (Fin.succ i)) (R (Fin.succ i)).verifier := fun i => coh i.succ
    haveI hcohTail : OracleVerifier.Append.AppendCoherent
        (seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (Wit ∘ Fin.succ)
          (fun i => R (Fin.succ i))
          (coh := hcohLeaf)).verifier :=
      seqCompose_verifier_appendCoherent (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
        (Wit ∘ Fin.succ) (fun i => R (Fin.succ i)) (coh := hcohLeaf)
    rw [seqCompose_succ, Reduction.seqCompose_succ]
    -- the head seam `(R 0).append tail` collapses by the verifier-fusion proof, then the tail by
    -- the inductive hypothesis. We chain the two equalities explicitly so the (defeq) coherence
    -- instance of the tail `seqCompose` need not match syntactically for `rw`.
    refine Eq.trans
      (appendToReductionResidual_proof (R 0)
        (seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (Wit ∘ Fin.succ)
          (fun i => R (Fin.succ i)) (coh := hcohLeaf))) ?_
    exact congrArg (Reduction.append (R 0).toReduction)
      (ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (Wit ∘ Fin.succ)
        (fun i => R (Fin.succ i)) (coh := hcohLeaf))

-- the `change`/`rw` through the `toReduction` bridge elaborates a large dependent statement.
set_option maxHeartbeats 1000000 in
set_option linter.unusedFintypeInType false in
/-- **n-ary message-seam `seqCompose` perfect completeness for oracle reductions (issue #29).**
Every component is nonempty and `P_to_V`-leading (`hValid`) and perfectly complete (`h`); with
per-round challenge finiteness/inhabitedness the oracle-level `seqCompose` is perfectly complete.

Pure pass-through to the proven `Reduction`-level engine
`Reduction.seqCompose_perfectCompleteness_threaded` via the structural `toReduction` bridge
`seqCompose_toReduction` (oracle perfect completeness is definitionally the `toReduction`'s perfect
completeness; the bridge rewrites the oracle `seqCompose`'s image to the `Reduction`-level
`seqCompose` of the component images). No residual, no `sorry`. -/
theorem seqCompose_perfectCompleteness_threaded {m : ℕ}
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
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt OStmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  -- oracle PC is definitionally the `toReduction`'s PC; rewrite the image by the structural bridge.
  change Reduction.perfectCompleteness init impl (rel 0) (rel (Fin.last m))
    (seqCompose Stmt OStmt Wit R).toReduction
  rw [seqCompose_toReduction Stmt OStmt Wit R]
  -- each component's oracle PC is definitionally its `toReduction`'s PC.
  exact Reduction.seqCompose_perfectCompleteness_threaded
    (fun i => Stmt i × (∀ j, OStmt i j)) Wit
    (fun i => (R i).toReduction) rel hValid hInit hImplSupp h

/-- **Explicit-instance form of `seqCompose_perfectCompleteness_threaded`.** Takes the per-round
challenge `SampleableType`/`Fintype`/`Inhabited` as *explicit* arguments `hSamp`/`hFin`/`hInh`
(rather than instance-implicit), the robust calling convention for concrete oracle protocols whose
per-round protocol is a literal `fun _ => p`: there instance search would otherwise fail to match the
`(fun _ => p) i` redex against an instance stated on the reduced `p`. A thin `@`-application of
`seqCompose_perfectCompleteness_threaded` feeding the three instance arguments positionally (so the
heavy `toReduction`-bridge elaboration runs only once, inside the delegate). Used by
`RingSwitching.SumcheckPhase.sumcheckLoopOracleReduction_perfectCompleteness`. -/
theorem seqCompose_pc_oracle_msg' {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (R i).verifier]
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (hSamp : ∀ i, ∀ j, SampleableType ((pSpec i).Challenge j))
    (hFin : ∀ i, ∀ j, Fintype ((pSpec i).Challenge j))
    (hInh : ∀ i, ∀ j, Inhabited ((pSpec i).Challenge j))
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt OStmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) :=
  @seqCompose_perfectCompleteness_threaded ι oSpec _ _ σ init impl m Stmt ιₛ OStmt Oₛ Wit n pSpec
    Oₘ hSamp hFin hInh R coh rel hValid hInit hImplSupp h

end OracleReduction
