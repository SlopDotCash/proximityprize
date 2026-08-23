/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.SecondSumcheckComplete
import ArkLib.ProofSystem.Spartan.TightFinalLeaf

/-!
# Enriched completeness of the target-carrying second sum-check lift (issue #329, B7 step 3)

The plain completeness transfer (`secondSumcheck_perfectCompleteness`) cannot *pin* the carried
terminal target inside its output relation: the generic `liftContext` completeness lens condition
(`Context.Lens.IsComplete.lift_complete`) only hands run-support membership of the *prover's*
output context (`Reduction.compatContext`), and no pass-through support characterization of the
`seqCompose` sum-check **prover** exists in-tree (this is the "honest frontier note" of
`FirstSumcheckWithTarget`).

This module dissolves that obstruction *without* the prover-side pass-through, by re-deriving the
`liftContext` completeness transfer with a **verifier-side** compatibility witness instead: the
completeness event already contains `prvStmtOut = stmtOut` (prover output statement = verifier
output statement), and the verifier output of any `Reduction.run` support point lies in the
support of `Verifier.run` on the produced transcript
(`Reduction.verifier_output_mem_support_of_run`, proven here by peeling the run's bind chain).
So the lens completeness condition may assume `Verifier.compatStatement` — and for the sum-check
verifier the oracle pass-through *is* in-tree
(`Sumcheck.Spec.mem_support_oracleVerifier_run_oStmt`), which pins the inner output oracle to the
honest second virtual polynomial `ℳ`.

Provides:
* `Reduction.verifier_output_mem_support_of_run` — the run-support peel (generic);
* `Reduction.liftContext_completeness_verifierCompat` /
  `OracleReduction.liftContext_completeness_verifierCompat` — the completeness transfer whose
  lens condition gets `Verifier.compatStatement` (generic, reusable);
* `secondSumcheckWithTargetRelIn` / `secondSumcheckWithTargetRelOut` — the honest carried
  completeness relations; the output relation **pins** the carried terminal
  `e₂ = eval r_y ℳ` in *exactly* the shape of `tightFinalRelOut`'s first conjunct;
* `secondSumcheckWithTarget_perfectCompleteness` (+ `_unconditional`) — the enriched perfect
  completeness of `secondSumcheckReductionWithTarget` between those relations;
* `secondSumcheckWithTargetRelOut_pins_e2` and `tightRelG_r1cs_subset_relIn` — the seam-facing
  containments for the step-(5) assembly.
-/

open OracleComp OracleSpec ProtocolSpec Function MvPolynomial
open scoped NNReal

/-! ## Generic part: verifier-side compatibility for `liftContext` completeness -/

section GenericVerifierCompat

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}

/-- **Run-support peel, verifier piece**: the verifier output of any complete `Reduction.run`
support point is in the support of `Verifier.run` on the produced transcript. The reverse
direction of `Reduction.mem_support_run_of_prover_verifier`. -/
theorem Reduction.verifier_output_mem_support_of_run
    {StmtIn WitIn StmtOut WitOut : Type}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    {x : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut}
    (h : some x ∈ support (OptionT.run (R.run stmt wit))) :
    x.2 ∈ support (R.verifier.run stmt x.1.1) := by
  unfold Reduction.run at h
  simp only [OptionT.run_bind, Option.elimM, bind_assoc] at h
  rw [mem_support_bind_iff] at h
  obtain ⟨pOpt, _hp, h⟩ := h
  cases pOpt with
  | none => simp at h
  | some pres =>
    simp only [Option.elim_some] at h
    rw [mem_support_bind_iff] at h
    obtain ⟨vOpt, hv, h⟩ := h
    cases vOpt with
    | none => simp at h
    | some vo =>
      cases vo with
      | none =>
        simp [Option.getM, Option.elimM] at h
      | some vout =>
        simp only [Option.elim_some, Option.getM_some, OptionT.run_bind, OptionT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Option.some_inj] at h
        subst h
        rw [OptionT.run_liftM_run, support_map,
          support_simulateQ_eq_OracleComp_of_superSpec _ _ (fun _ => rfl)] at hv
        obtain ⟨v', hv', hveq⟩ := hv
        obtain rfl : v' = some vout := by
          simpa using hveq
        exact (OptionT.mem_support_iff _ _).2 hv'

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

namespace Reduction

variable
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
  {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
  {R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec}
  {completenessError : ℝ≥0}
  {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}

set_option maxHeartbeats 1000000 in
/-- **`liftContext` completeness transfer with a verifier-side compatibility witness.**

Identical to `Reduction.liftContext_completeness` except that the lens condition `hLiftC` may
assume `Verifier.compatStatement` (the inner output statement is reachable by the *inner
verifier* on the projected input for some transcript) instead of the prover-side
`Reduction.compatContext`. This is strictly more usable when the verifier — but not the prover —
has an in-tree pass-through support characterization (e.g. the sum-check oracle verifier's
`mem_support_oracleVerifier_run_oStmt`).

The proof is the original one, with the compatibility witness re-derived from the completeness
event's `prvStmtOut = stmtOut` conjunct plus the run-support peel
`Reduction.verifier_output_mem_support_of_run`. -/
theorem liftContext_completeness_verifierCompat
    (hProj : ∀ stmtIn witIn, (stmtIn, witIn) ∈ outerRelIn →
      (lens.stmt.proj stmtIn, lens.wit.proj (stmtIn, witIn)) ∈ innerRelIn)
    (hLiftC : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
      R.verifier.compatStatement lens.stmt outerStmtIn innerStmtOut →
      (outerStmtIn, outerWitIn) ∈ outerRelIn →
      (innerStmtOut, innerWitOut) ∈ innerRelOut →
      (lens.stmt.lift outerStmtIn innerStmtOut,
        lens.wit.lift (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut)) ∈ outerRelOut)
    (h : R.completeness init impl innerRelIn innerRelOut completenessError) :
      (R.liftContext lens).completeness init impl outerRelIn outerRelOut completenessError := by
  unfold Reduction.completeness at h ⊢
  intro outerStmtIn outerWitIn hRelIn
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl
  let f :
      ((FullTranscript pSpec × InnerStmtOut × InnerWitOut) × InnerStmtOut) →
        ((FullTranscript pSpec × OuterStmtOut × OuterWitOut) × OuterStmtOut) :=
    fun x => ((x.1.1, lens.lift (outerStmtIn, outerWitIn) x.1.2), lens.stmt.lift outerStmtIn x.2)
  have hExecMap :
      OptionT.mk (do
        let __do_lift ← init
        (simulateQ pImpl (((R.liftContext lens).run outerStmtIn outerWitIn).run)).run'
          __do_lift) =
        f <$> OptionT.mk (do
          let __do_lift ← init
          (simulateQ pImpl
            ((R.run (lens.stmt.proj outerStmtIn)
              (lens.wit.proj (outerStmtIn, outerWitIn))).run)).run'
            __do_lift) := by
    rw [Reduction.liftContext_run]
    change OptionT.mk (do
        let __do_lift ← init
        (simulateQ pImpl
          ((f <$> R.run (lens.stmt.proj outerStmtIn)
            (lens.wit.proj (outerStmtIn, outerWitIn))).run)).run' __do_lift) =
      f <$> OptionT.mk (do
        let __do_lift ← init
        (simulateQ pImpl
          ((R.run (lens.stmt.proj outerStmtIn)
            (lens.wit.proj (outerStmtIn, outerWitIn))).run)).run' __do_lift)
    exact OptionT.mk_simulateQ_run'_map_stateful
      (impl := pImpl)
      (init := init)
      (f := f)
      (mx := R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn)))
  have hR :
      Pr[(fun x ↦
          match x with
          | ((_, prvStmtOut, witOut), stmtOut) =>
            (stmtOut, witOut) ∈ innerRelOut ∧ prvStmtOut = stmtOut) |
          OptionT.mk do
            let __do_lift ← init
            (simulateQ pImpl
              ((R.run (lens.stmt.proj outerStmtIn)
                (lens.wit.proj (outerStmtIn, outerWitIn))).run)).run' __do_lift] ≥
        1 - ↑completenessError := by
    simpa [pImpl] using
      h (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn))
        (hProj _ _ hRelIn)
  change
      Pr[(fun x ↦
          match x with
          | ((_, prvStmtOut, witOut), stmtOut) =>
            (stmtOut, witOut) ∈ outerRelOut ∧ prvStmtOut = stmtOut) |
          OptionT.mk do
            let __do_lift ← init
            (simulateQ pImpl (((R.liftContext lens).run outerStmtIn outerWitIn).run)).run'
              __do_lift] ≥ 1 - ↑completenessError
  rw [hExecMap]
  refine le_trans hR ?_
  rw [probEvent_map]
  apply probEvent_mono
  intro x hx
  simp [f]
  intro hInnerRelOut hEqStmt
  have hxRun :
      x ∈ support (R.run (lens.stmt.proj outerStmtIn)
        (lens.wit.proj (outerStmtIn, outerWitIn))) := by
    have hxSome :
        some x ∈ support (OptionT.run (OptionT.mk do
          let __do_lift ← init
          (simulateQ pImpl
            (R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn)))).run'
              __do_lift)) := by
      exact (OptionT.mem_support_iff _ _).1 hx
    change
      some x ∈ support (do
        let __do_lift ← init
        (simulateQ pImpl
          (R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn)))).run'
            __do_lift) at hxSome
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hxSome
    rcases hxSome with ⟨s, _hs, hState⟩
    exact OptionT.mem_support_run_simulateQ_run'_subset
      (impl := pImpl)
      (oa := R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn)))
      (s := s) hState
  refine ⟨?_, ?_⟩
  · have hVC : R.verifier.compatStatement lens.stmt outerStmtIn x.2 := by
      have hSome : some x ∈ support (OptionT.run (R.run (lens.stmt.proj outerStmtIn)
          (lens.wit.proj (outerStmtIn, outerWitIn)))) :=
        (OptionT.mem_support_iff _ _).1 hxRun
      exact ⟨x.1.1, R.verifier_output_mem_support_of_run _ _ hSome⟩
    have hLift := hLiftC outerStmtIn outerWitIn x.2 x.1.2.2 hVC hRelIn hInnerRelOut
    have hEqCtx : x.1.2 = (x.2, x.1.2.2) := by
      ext <;> simp [hEqStmt]
    change (lens.stmt.lift outerStmtIn x.2,
        lens.wit.toFunB (outerStmtIn, outerWitIn) (x.2, x.1.2.2)) ∈ outerRelOut at hLift
    have hWitEq :
        lens.wit.toFunB (outerStmtIn, outerWitIn) (x.2, x.1.2.2) =
          lens.wit.toFunB (outerStmtIn, outerWitIn) x.1.2 := by
      rw [← hEqCtx]
    rw [← hWitEq]
    exact hLift
  · exact congrArg (fun t => lens.stmt.lift outerStmtIn t) hEqStmt

end Reduction

namespace OracleReduction

variable
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  [∀ i, OracleInterface (pSpec.Message i)]
  {outerRelIn : Set ((OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn)}
  {outerRelOut : Set ((OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut)}
  {innerRelIn : Set ((InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn)}
  {innerRelOut : Set ((InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut)}
  {lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
  {stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec}
  {R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                          InnerStmtOut InnerOStmtOut InnerWitOut pSpec}
  {completenessError : ℝ≥0}

/-- Oracle-reduction wrapper of `Reduction.liftContext_completeness_verifierCompat`, mirroring
`OracleReduction.liftContext_completeness`. -/
theorem liftContext_completeness_verifierCompat
    (hStmt : stmtLens.toLens = lens.stmt)
    [coh : OracleVerifier.LiftContextCoherent stmtLens R.verifier]
    (hProj : ∀ stmtIn witIn, (stmtIn, witIn) ∈ outerRelIn →
      (lens.toContext.stmt.proj stmtIn, lens.toContext.wit.proj (stmtIn, witIn)) ∈ innerRelIn)
    (hLiftC : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
      R.toReduction.verifier.compatStatement lens.toContext.stmt outerStmtIn innerStmtOut →
      (outerStmtIn, outerWitIn) ∈ outerRelIn →
      (innerStmtOut, innerWitOut) ∈ innerRelOut →
      (lens.toContext.stmt.lift outerStmtIn innerStmtOut,
        lens.toContext.wit.lift (outerStmtIn, outerWitIn)
          (innerStmtOut, innerWitOut)) ∈ outerRelOut)
    (h : R.completeness init impl innerRelIn innerRelOut completenessError) :
      (R.liftContext lens stmtLens).completeness init impl outerRelIn outerRelOut
        completenessError := by
  unfold OracleReduction.completeness at h ⊢
  rw [OracleReduction.liftContext_toReduction_comm hStmt]
  exact Reduction.liftContext_completeness_verifierCompat hProj hLiftC h

/-- Perfect-completeness form of `liftContext_completeness_verifierCompat`. -/
theorem liftContext_perfectCompleteness_verifierCompat
    (hStmt : stmtLens.toLens = lens.stmt)
    [coh : OracleVerifier.LiftContextCoherent stmtLens R.verifier]
    (hProj : ∀ stmtIn witIn, (stmtIn, witIn) ∈ outerRelIn →
      (lens.toContext.stmt.proj stmtIn, lens.toContext.wit.proj (stmtIn, witIn)) ∈ innerRelIn)
    (hLiftC : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
      R.toReduction.verifier.compatStatement lens.toContext.stmt outerStmtIn innerStmtOut →
      (outerStmtIn, outerWitIn) ∈ outerRelIn →
      (innerStmtOut, innerWitOut) ∈ innerRelOut →
      (lens.toContext.stmt.lift outerStmtIn innerStmtOut,
        lens.toContext.wit.lift (outerStmtIn, outerWitIn)
          (innerStmtOut, innerWitOut)) ∈ outerRelOut)
    (h : R.perfectCompleteness init impl innerRelIn innerRelOut) :
      (R.liftContext lens stmtLens).perfectCompleteness init impl outerRelIn outerRelOut :=
  liftContext_completeness_verifierCompat hStmt hProj hLiftC h

end OracleReduction

end GenericVerifierCompat

/-! ## Spartan part: the enriched carried-second completeness -/

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- **Honest input relation of the enriched carried second sum-check phase**: the carried clone of
`secondSumcheckRelIn` over the `e₁`-carrying statement (the carried `e₁` is a pure passenger):
the R1CS instance is satisfied, and the prepended target `T` equals the honest
random-linear-combination of the bundled eval-claims. -/
def secondSumcheckWithTargetRelIn :
    Set (((R × Statement.AfterLinearCombinationWithTarget R pp) ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS (dropFirstTarget pp x.1.1.2).2.2.2
          (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
        ∧ x.1.1.1 = ∑ idx, (dropFirstTarget pp x.1.1.2).1 idx *
            evalClaimValue R pp (dropFirstTarget pp x.1.1.2).2
              (fun i => x.1.2 (.inr i)) idx }

/-- The carried input relation is the plain `secondSumcheckRelIn` read through
`dropFirstTarget`. -/
theorem secondSumcheckWithTargetRelIn_iff_plain
    (x : ((R × Statement.AfterLinearCombinationWithTarget R pp) ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :
    x ∈ secondSumcheckWithTargetRelIn pp ↔
      (((x.1.1.1, dropFirstTarget pp x.1.1.2), x.1.2), ()) ∈ secondSumcheckRelIn (R := R) pp :=
  Iff.rfl

/-- **Honest output relation of the enriched carried second sum-check phase.** Two conjuncts:
* R1CS satisfiability carried through (as in the plain `secondSumcheckRelOut`);
* **the carried terminal is pinned**: `e₂ = eval r_y ℳ`, in *exactly* the shape of
  `tightFinalRelOut`'s first conjunct (same projections), so the step-(5) assembly welds without
  adapters. -/
def secondSumcheckWithTargetRelOut :
    Set ((Statement.AfterSecondSumcheckWithTarget R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS (dropFirstTarget pp x.1.1.2).2.2.2
          (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
        ∧ x.1.1.1.1 = MvPolynomial.eval x.1.1.1.2
            (secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp x.1.1.2) x.1.2) }

/-- **The pinned conjunct, in `tightFinalRelOut` first-conjunct shape**: membership in the honest
enriched output relation pins the carried terminal `e₂ = eval r_y ℳ`. -/
theorem secondSumcheckWithTargetRelOut_pins_e2
    (x : (Statement.AfterSecondSumcheckWithTarget R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit)
    (hx : x ∈ secondSumcheckWithTargetRelOut pp) :
    x.1.1.1.1 = MvPolynomial.eval x.1.1.1.2
      (secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp x.1.1.2) x.1.2) :=
  hx.2

/-- **Seam-facing inclusion for the step-(5) weld**: the X-lane semantic relation `tightRelG`
(true-RLC target + binding) lands in the honest enriched input relation as soon as the R1CS
instance is satisfied (the completeness chain carries R1CS satisfiability alongside). -/
theorem tightRelG_r1cs_subset_relIn
    (x : (((R × Statement.AfterLinearCombinationWithTarget R pp) ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit))
    (hG : x ∈ Bricks.tightRelG (R := R) pp)
    (hR1CS : R1CS.relation R pp.toSizeR1CS (dropFirstTarget pp x.1.1.2).2.2.2
      (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))) :
    x ∈ secondSumcheckWithTargetRelIn pp :=
  ⟨hR1CS, hG.1⟩

section Completeness

variable [Inhabited R]

set_option maxHeartbeats 1000000 in
/-- **Enriched perfect completeness of the target-carrying second sum-check lift** (B7 step 3):
`secondSumcheckReductionWithTarget` is perfectly complete from the honest carried input relation
to the output relation **pinning** the carried terminal `e₂ = eval r_y ℳ`, given the inner
multi-round sum-check perfect completeness `h_inner`.

The transfer is `OracleReduction.liftContext_perfectCompleteness_verifierCompat`: the
verifier-side compatibility witness plus the oracle pass-through keystone
(`Sumcheck.Spec.mem_support_oracleVerifier_run_oStmt`) pin the inner output oracle to the honest
second virtual polynomial `ℳ`, so the inner terminal sum-check relation *is* the pinned
identity (`Bricks.relationRound_last_iff_deg`). -/
theorem secondSumcheckWithTarget_perfectCompleteness
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).perfectCompleteness
        init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))) :
    (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl
      (secondSumcheckWithTargetRelIn (R := R) pp)
      (secondSumcheckWithTargetRelOut (R := R) pp) := by
  haveI := secondSumcheckCoherentWithTarget (R := R) pp oSpec
  refine OracleReduction.liftContext_perfectCompleteness_verifierCompat
    (lens := secondSumcheckContextLensWithTarget pp)
    (stmtLens := secondSumcheckOracleLensWithTarget pp oSpec)
    (outerRelIn := secondSumcheckWithTargetRelIn (R := R) pp)
    (innerRelIn := Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
    (outerRelOut := secondSumcheckWithTargetRelOut (R := R) pp)
    (innerRelOut := Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
    rfl ?_ ?_ h_inner
  · -- `proj_complete`: with the carried target equal to the RLC, the projected round-0 instance
    -- satisfies `∑_cube ℳ = target`.
    rintro ⟨⟨T, stmt⟩, oStmt⟩ ⟨⟩ hRelIn
    obtain ⟨_hR1CS, ht⟩ := hRelIn
    -- Clean the (definitional) projections in the target-reconciliation equation.
    have ht' : T = ∑ idx, (dropFirstTarget pp stmt).1 idx *
        evalClaimValue R pp (dropFirstTarget pp stmt).2 (fun i => oStmt (.inr i)) idx := ht
    have hmem : (((⟨T, Fin.elim0⟩ : Sumcheck.Spec.StatementRound R pp.ℓ_n 0),
        fun _ => (⟨secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp stmt) oStmt,
          secondSCVP_mem_restrictDegree pp (dropFirstTarget pp stmt) oStmt⟩ :
          Sumcheck.Spec.OracleStatement R pp.ℓ_n 2 ())), ())
        ∈ Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) 0 := by
      rw [ht']
      exact Bricks.secondSC_relationRound_zero pp (dropFirstTarget pp stmt) oStmt
        ⟨secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp stmt) oStmt,
          secondSCVP_mem_restrictDegree pp (dropFirstTarget pp stmt) oStmt⟩
        rfl
    exact hmem
  · -- `lift_complete` with the verifier-side compat: pin the inner oracle to the honest `ℳ`,
    -- then the inner terminal relation is exactly the pinned identity.
    rintro ⟨⟨T, stmt⟩, oStmt⟩ ⟨⟩ ⟨⟨t_out, r_y⟩, innerO⟩ ⟨⟩ hVC hRelIn hRelOut
    obtain ⟨hR1CS, _ht⟩ := hRelIn
    -- The oracle-pinning keystone: the compatible inner oracle is the honest virtual polynomial.
    have hpin : innerO = ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj
        ((T, stmt), oStmt)).2 := by
      obtain ⟨tr, htr⟩ := hVC
      exact Sumcheck.Spec.mem_support_oracleVerifier_run_oStmt htr
    rw [hpin] at hRelOut
    have hEval : MvPolynomial.eval r_y
        (secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp stmt) oStmt) = t_out :=
      (Bricks.relationRound_last_iff_deg (R := R) t_out r_y _).mp hRelOut
    exact ⟨hR1CS, hEval.symm⟩

set_option linter.unusedFintypeInType false in
/-- **Enriched perfect completeness, UNCONDITIONAL** modulo only the honest execution-model data
facts `hInit`/`hImplSupp`: the inner completeness is discharged by the bridge-free
`Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional`. -/
theorem secondSumcheckWithTarget_perfectCompleteness_unconditional
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    [oSpec.Fintype] [oSpec.Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl
      (secondSumcheckWithTargetRelIn (R := R) pp)
      (secondSumcheckWithTargetRelOut (R := R) pp) :=
  secondSumcheckWithTarget_perfectCompleteness pp oSpec
    (Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional hInit hImplSupp)

end Completeness

end Spartan.Spec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Reduction.verifier_output_mem_support_of_run
#print axioms Reduction.liftContext_completeness_verifierCompat
#print axioms OracleReduction.liftContext_perfectCompleteness_verifierCompat
#print axioms Spartan.Spec.secondSumcheckWithTargetRelOut_pins_e2
#print axioms Spartan.Spec.tightRelG_r1cs_subset_relIn
#print axioms Spartan.Spec.secondSumcheckWithTarget_perfectCompleteness
#print axioms Spartan.Spec.secondSumcheckWithTarget_perfectCompleteness_unconditional
