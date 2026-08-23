/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-!

# Plonk Gate-Check Protocol

The Plonk gate-check is the first component of the Plonk PIOP: the prover sends the
wire assignment, the verifier checks all gate equations in the constraint system.

Modeled as a 1-round `Reduction` using ArkLib's OracleReduction framework. This
protocol forms the foundation for the full Plonk PIOP — composition with the
permutation argument (copy constraints) is handled separately in
`ArkLib.ProofSystem.Plonk.PermutationCheck`.

## Protocol structure

- **ProtocolSpec**: 1 round, P → V, message type `Fin numWires → 𝓡`
- **Statement**: `Plonk.ConstraintSystem 𝓡 numWires numGates`
- **Witness**: `Fin numWires → 𝓡` (wire assignment)
- **Input relation**: `cs.accepts w` (all gate equations satisfied)
- **Output**: `(cs, w)` pair (for composition with downstream reductions)

## References

* [Gabizon, A., Williamson, Z.J., and Ciobotaru, O., *Plonk: Permutations over lagrange-bases
    for oecumenical noninteractive arguments of knowledge*][GWZC19]

-/

noncomputable section

namespace Plonk

open OracleComp OracleSpec ProtocolSpec

section GateCheck

variable (𝓡 : Type) [CommRing 𝓡] (numWires numGates : ℕ)

@[reducible]
def gateCheckPSpec : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[Fin numWires → 𝓡]⟩

instance : ∀ i, VCVCompatible ((gateCheckPSpec 𝓡 numWires).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType ((gateCheckPSpec 𝓡 numWires).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance : ProverOnly (gateCheckPSpec 𝓡 numWires) where
  prover_first' := rfl

variable {𝓡} {numWires} {numGates}

@[inline, specialize]
def gateCheckProver :
    Prover []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates) (Fin numWires → 𝓡)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (gateCheckPSpec 𝓡 numWires) where
  PrvState
  | 0 => Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)
  | 1 => Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨cs, w⟩ => pure (w, ⟨cs, w⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨cs, w⟩ => pure (⟨cs, w⟩, ())

variable [DecidableEq 𝓡]

instance acceptsDecidable (cs : Plonk.ConstraintSystem 𝓡 numWires numGates) (w : Fin numWires → 𝓡) :
    Decidable (cs.accepts w) :=
  inferInstanceAs (Decidable (∀ i : Fin numGates, (cs i).eval w = 0))

@[inline, specialize]
def gateCheckVerifier :
    Verifier []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
      (gateCheckPSpec 𝓡 numWires) where
  verify := fun cs transcript => do
    let w : Fin numWires → 𝓡 := transcript 0
    guard (cs.accepts w)
    return ⟨cs, w⟩

theorem gateCheckVerifier_verify_eq
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (transcript : FullTranscript (gateCheckPSpec 𝓡 numWires)) :
    (gateCheckVerifier (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates)).verify
      cs transcript =
      if cs.accepts (transcript 0) then pure (cs, transcript 0) else failure := by
  by_cases h : cs.accepts (transcript 0) <;>
    simp [gateCheckVerifier, guard_eq, h]

theorem gateCheckVerifier_mem_support_iff
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (transcript : FullTranscript (gateCheckPSpec 𝓡 numWires))
    (out : Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :
    some out ∈ support
      ((gateCheckVerifier (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates)).verify
        cs transcript).run ↔
      cs.accepts (transcript 0) ∧ out = (cs, transcript 0) := by
  rw [gateCheckVerifier_verify_eq]
  by_cases h : cs.accepts (transcript 0) <;> simp [h]

@[inline, specialize]
def gateCheckReduction :
    Reduction []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates) (Fin numWires → 𝓡)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (gateCheckPSpec 𝓡 numWires) where
  prover := gateCheckProver
  verifier := gateCheckVerifier

@[reducible, simp]
def gateCheckRelIn :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :=
  { p | p.1.accepts p.2 }

@[reducible, simp]
def gateCheckRelOut :
    Set ((Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) × Unit) :=
  Prod.fst ⁻¹' gateCheckRelIn

@[reducible, simp]
def gateCheckLangIn :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates) :=
  { cs | ∃ w : Fin numWires → 𝓡, cs.accepts w }

@[reducible, simp]
def gateCheckLangOut :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :=
  { p | p.1.accepts p.2 }

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

set_option maxHeartbeats 1600000 in
open Classical in
theorem gateCheck_perfectCompleteness :
    (gateCheckReduction (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates)).perfectCompleteness
      init impl gateCheckRelIn gateCheckRelOut := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, Reduction.completenessFromRun,
    ENNReal.coe_zero, tsub_zero]
  intro cs w hIn
  simp only [gateCheckRelIn, Set.mem_setOf_eq] at hIn
  have hrun : (gateCheckReduction (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).run cs w =
      OptionT.mk (pure (some (⟨fun | ⟨0, _⟩ => w, (cs, w), ()⟩, (cs, w)))) := by
    simp only [Reduction.run, Verifier.run, Prover.run_of_prover_first,
      gateCheckReduction, gateCheckProver, gateCheckVerifier, guard, if_pos hIn, id,
      OracleComp.liftComp_pure, pure_bind, map_pure, bind_pure_comp, monadLift_pure,
      OptionT.run_pure, Option.getM]; rfl
  simp only [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    erw [simulateQ_pure]
    rw [StateT.run'_eq, StateT.run_pure]
    simp [map_pure, support_pure]
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    erw [simulateQ_pure] at hx
    rw [StateT.run'_eq, StateT.run_pure] at hx
    simp only [map_pure, support_pure, Set.mem_singleton_iff] at hx
    cases hx
    exact ⟨hIn, rfl⟩

/-- The gate-check verifier has zero-error round-by-round soundness for the language of
satisfiable gate systems. If the input constraint system has no accepting wire assignment, then a
full transcript whose verifier output is in `gateCheckLangOut` would itself provide one. -/
theorem gateCheckVerifier_rbrSoundness :
    (gateCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).rbrSoundness init impl
        gateCheckLangIn gateCheckLangOut 0 := by
  refine ⟨{
    toFun := fun _ cs _ => cs ∈ gateCheckLangIn
    toFun_empty := fun _ => Iff.rfl
    toFun_next := fun _ _ _ _ h _ => h
    toFun_full := fun cs tr hcs => ?_
  }, ?_⟩
  · rw [probEvent_eq_zero_iff]
    intro out hout houtLang
    rw [OptionT.mem_support_iff] at hout
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
    obtain ⟨s, _, hout⟩ := hout
    simp only [Verifier.run, gateCheckVerifier_verify_eq] at hout
    by_cases hAccept : cs.accepts (tr ⟨0, by simp⟩)
    · exact hcs ⟨tr ⟨0, by simp⟩, hAccept⟩
    · have hrun :
          (simulateQ impl
            ((gateCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
              (numGates := numGates)).run cs tr)).run' s =
            pure none := by
        simp only [Verifier.run, gateCheckVerifier_verify_eq]
        split_ifs with h
        · exact False.elim (hAccept (by simpa using h))
        change (simulateQ impl (pure none : OracleComp []ₒ
          (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
            (Fin numWires → 𝓡))))).run' s = pure none
        rw [simulateQ_pure]
        change Prod.fst <$> (pure none : StateT σ ProbComp
          (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
            (Fin numWires → 𝓡)))).run s = pure none
        rw [StateT.run_pure]
        simp [map_pure]
      simp only [Verifier.run, gateCheckVerifier_verify_eq] at hrun
      rw [hrun] at hout
      simp at hout
  · intro _ hNotIn _ _ _ _ ⟨⟨0, _⟩, hdir⟩
    exact absurd hdir (by simp)

/-- The gate-check verifier has ordinary zero-error soundness. A successful malicious execution
outside `gateCheckLangIn` would have to pass the verifier guard on the prover's single message,
which directly gives the missing satisfying wire assignment. -/
theorem gateCheckVerifier_soundness :
    (gateCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).soundness init impl
        gateCheckLangIn gateCheckLangOut 0 := by
  unfold Verifier.soundness
  intro WitIn WitOut witIn prover cs hcs
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, probEvent_eq_zero_iff]
  intro x hx hxLang
  apply hcs
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _hs, hx⟩ := hx
  rw [Reduction.run_of_prover_first] at hx
  simp only [StateT.run'_eq, OptionT.run_bind, Option.elimM, support_map, Set.mem_image] at hx
  obtain ⟨⟨runOpt, s'⟩, hx, hrunOpt⟩ := hx
  simp only at hrunOpt
  rw [simulateQ_bind] at hx
  rw [StateT.run_bind] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨⟨sendOpt, s1⟩, hsend, hx⟩ := hx
  cases sendOpt with
  | none =>
      simp only [Option.elim_none] at hx
      rw [simulateQ_pure, StateT.run_pure] at hx
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rw [hx.1] at hrunOpt
      simp at hrunOpt
  | some sendState =>
      simp only [Option.elim_some] at hx
      rw [simulateQ_bind] at hx
      rw [StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨⟨outOpt, s2⟩, hout, hx⟩ := hx
      cases outOpt with
      | none =>
          simp only [Option.elim_none] at hx
          rw [simulateQ_pure, StateT.run_pure] at hx
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rw [hx.1] at hrunOpt
          simp at hrunOpt
      | some outState =>
          simp only [Option.elim_some] at hx
          simp only [gateCheckVerifier_verify_eq] at hx
          by_cases hAccept : cs.accepts sendState.1
          · exact ⟨sendState.1, hAccept⟩
          · rw [if_neg hAccept] at hx
            let Result :=
              Option (((gateCheckPSpec 𝓡 numWires).FullTranscript ×
                (Plonk.ConstraintSystem 𝓡 numWires numGates ×
                  (Fin numWires → 𝓡)) × WitOut) ×
                Plonk.ConstraintSystem 𝓡 numWires numGates ×
                  (Fin numWires → 𝓡))
            change (runOpt, s') ∈ support
              (((simulateQ
                (impl.addLift (challengeQueryImpl (pSpec := gateCheckPSpec 𝓡 numWires)))
                (pure none : OracleComp _ Result) :
                  StateT σ ProbComp Result).run s2)) at hx
            rw [simulateQ_pure, StateT.run_pure] at hx
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rw [hx.1] at hrunOpt
            simp at hrunOpt

/-- The gate-check verifier has zero-error round-by-round knowledge soundness: the single
prover message is the wire assignment, and the verifier guard ensures it satisfies the gate
constraints whenever the verifier can output a related statement. -/
theorem gateCheckVerifier_rbrKnowledgeSoundness :
    (gateCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).rbrKnowledgeSoundness init impl gateCheckRelIn gateCheckRelOut 0 := by
  refine ⟨fun _ => Fin numWires → 𝓡, {
    eqIn := rfl
    extractMid := fun ⟨0, _⟩ _stmt _tr witMid => witMid
    extractOut := fun _stmt tr _ => tr ⟨0, by omega⟩
  }, {
    toFun := fun _ stmt _tr wit => (stmt, wit) ∈ gateCheckRelIn
    toFun_empty := fun _ _ => by simp
    toFun_next := fun ⟨0, _⟩ _ _stmt _tr _msg _witMid h => h
    toFun_full := fun stmt tr _witOut hpr => by
      rw [gt_iff_lt, probEvent_pos_iff] at hpr
      obtain ⟨_x, hx, _hrel⟩ := hpr
      rw [OptionT.mem_support_iff] at hx
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
      obtain ⟨s, _, hx⟩ := hx
      by_cases hAccept : stmt.accepts (tr ⟨0, by simp⟩)
      · simpa [gateCheckRelIn] using hAccept
      · exfalso
        have hrun :
            (simulateQ impl
              ((gateCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
                (numGates := numGates)).run stmt tr)).run' s =
              pure none := by
          simp only [Verifier.run, gateCheckVerifier_verify_eq]
          split_ifs with h
          · exact False.elim (hAccept (by simpa using h))
          change (simulateQ impl (pure none : OracleComp []ₒ
            (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
              (Fin numWires → 𝓡))))).run' s = pure none
          rw [simulateQ_pure]
          change Prod.fst <$> (pure none : StateT σ ProbComp
            (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
              (Fin numWires → 𝓡)))).run s = pure none
          rw [StateT.run_pure]
          simp [map_pure]
        rw [hrun] at hx
        simp at hx
  }, ?_⟩
  intro _stmtIn _witIn _prover ⟨⟨0, _⟩, hdir⟩
  exact absurd hdir (by simp)

#print axioms Plonk.gateCheckVerifier_verify_eq
#print axioms Plonk.gateCheckVerifier_mem_support_iff
#print axioms Plonk.gateCheck_perfectCompleteness
#print axioms Plonk.gateCheckVerifier_rbrSoundness
#print axioms Plonk.gateCheckVerifier_soundness
#print axioms Plonk.gateCheckVerifier_rbrKnowledgeSoundness

end GateCheck

end Plonk

end
