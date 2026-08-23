/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-!

# Plonk Permutation Check Protocol

The permutation check verifies that copy constraints are satisfied: the extended
wire assignment is constant on orbits of the permutation induced by the constraint system.

Modeled as a 1-round `Reduction` using ArkLib's OracleReduction framework, parallel
to the gate-check protocol in `ArkLib.ProofSystem.Plonk.Basic`.

## Protocol structure

- **ProtocolSpec**: 1 round, P → V, message type `Fin (3 * numGates) → 𝓡`
- **Statement**: `Plonk.ConstraintSystem 𝓡 numWires numGates`
- **Witness**: `Fin (3 * numGates) → 𝓡` (extended wire assignment)
- **Input relation**: `CopyConstraintsSatisfied f (cs.perm)`
- **Output**: `(cs, f)` pair

## References

* [Gabizon, A., Williamson, Z.J., and Ciobotaru, O., *Plonk: Permutations over lagrange-bases
    for oecumenical noninteractive arguments of knowledge*][GWZC19]

-/

noncomputable section

namespace Plonk

open OracleComp OracleSpec ProtocolSpec

section Extend

variable (𝓡 : Type) [CommRing 𝓡] (numWires numGates : ℕ)

/-- Maps a position in `Fin (3 * numGates)` to the wire index it references.
Position `(k, g)` via `finProdFinEquiv` references wire `a`/`b`/`c` of gate `g`. -/
def wireOfPosition (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (j : Fin (3 * numGates)) : Fin numWires :=
  let p := finProdFinEquiv.symm j
  if p.1 = 0 then (cs p.2).a
  else if p.1 = 1 then (cs p.2).b
  else (cs p.2).c

/-- Extends a wire assignment to the full position domain using the constraint system's
wire routing: position `j` gets value `w (wireOfPosition cs j)`. -/
def extendWireAssignment (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (w : Fin numWires → 𝓡) : Fin (3 * numGates) → 𝓡 :=
  w ∘ wireOfPosition 𝓡 numWires numGates cs

end Extend

section PermutationCheck

variable (𝓡 : Type) [CommRing 𝓡] (numWires numGates : ℕ)

@[reducible]
def permCheckPSpec : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[Fin (3 * numGates) → 𝓡]⟩

instance : ∀ i, VCVCompatible ((permCheckPSpec 𝓡 numGates).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType ((permCheckPSpec 𝓡 numGates).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance : ProverOnly (permCheckPSpec 𝓡 numGates) where
  prover_first' := rfl

variable {𝓡} {numWires} {numGates}

@[inline, specialize]
def permCheckProver :
    Prover []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates) (Fin (3 * numGates) → 𝓡)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)) Unit
      (permCheckPSpec 𝓡 numGates) where
  PrvState
  | 0 => Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)
  | 1 => Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨cs, f⟩ => pure (f, ⟨cs, f⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨cs, f⟩ => pure (⟨cs, f⟩, ())

variable [DecidableEq 𝓡]

instance copyConstraintsDecidable (f : Fin (3 * numGates) → 𝓡)
    (σ : Equiv.Perm (Fin (3 * numGates))) :
    Decidable (CopyConstraintsSatisfied f σ) :=
  inferInstanceAs (Decidable (∀ i, f (σ i) = f i))

@[inline, specialize]
def permCheckVerifier :
    Verifier []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡))
      (permCheckPSpec 𝓡 numGates) where
  verify := fun cs transcript => do
    let f : Fin (3 * numGates) → 𝓡 := transcript 0
    guard (CopyConstraintsSatisfied f cs.perm)
    return ⟨cs, f⟩

omit [CommRing 𝓡] in
theorem permCheckVerifier_verify_eq
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (transcript : FullTranscript (permCheckPSpec 𝓡 numGates)) :
    (permCheckVerifier (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates)).verify
      cs transcript =
      if CopyConstraintsSatisfied (transcript 0) cs.perm then pure (cs, transcript 0)
      else failure := by
  by_cases h : CopyConstraintsSatisfied (transcript 0) cs.perm <;>
    simp [permCheckVerifier, guard_eq, h]

omit [CommRing 𝓡] in
theorem permCheckVerifier_mem_support_iff
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (transcript : FullTranscript (permCheckPSpec 𝓡 numGates))
    (out : Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)) :
    some out ∈ support
      ((permCheckVerifier (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates)).verify
        cs transcript).run ↔
      CopyConstraintsSatisfied (transcript 0) cs.perm ∧ out = (cs, transcript 0) := by
  rw [permCheckVerifier_verify_eq]
  by_cases h : CopyConstraintsSatisfied (transcript 0) cs.perm <;> simp [h]

@[inline, specialize]
def permCheckReduction :
    Reduction []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates) (Fin (3 * numGates) → 𝓡)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)) Unit
      (permCheckPSpec 𝓡 numGates) where
  prover := permCheckProver
  verifier := permCheckVerifier

@[reducible, simp]
def permCheckRelIn :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)) :=
  { p | CopyConstraintsSatisfied p.2 p.1.perm }

@[reducible, simp]
def permCheckRelOut :
    Set ((Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)) × Unit) :=
  Prod.fst ⁻¹' permCheckRelIn

@[reducible, simp]
def permCheckLangIn :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates) :=
  { cs | ∃ f : Fin (3 * numGates) → 𝓡, CopyConstraintsSatisfied f cs.perm }

@[reducible, simp]
def permCheckLangOut :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin (3 * numGates) → 𝓡)) :=
  { p | CopyConstraintsSatisfied p.2 p.1.perm }

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

set_option maxHeartbeats 1600000 in
omit [CommRing 𝓡] in
open Classical in
theorem permCheck_perfectCompleteness :
    (permCheckReduction (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates)).perfectCompleteness
      init impl permCheckRelIn permCheckRelOut := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro cs f hIn
  simp only [permCheckRelIn, Set.mem_setOf_eq] at hIn
  have hrun : (permCheckReduction (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).run cs f =
      OptionT.mk (pure (some (⟨fun | ⟨0, _⟩ => f, (cs, f), ()⟩, (cs, f)))) := by
    simp only [Reduction.run, Verifier.run, Prover.run_of_prover_first,
      permCheckReduction, permCheckProver, permCheckVerifier, guard, if_pos hIn, id,
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

omit [CommRing 𝓡] in
/-- The permutation-check verifier has zero-error round-by-round soundness for the language of
constraint systems with a copy-constraint-satisfying extended assignment. If the input statement is
outside this language, an accepting verifier output would itself provide the missing assignment. -/
theorem permCheckVerifier_rbrSoundness :
    (permCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).rbrSoundness init impl
        permCheckLangIn permCheckLangOut 0 := by
  refine ⟨{
    toFun := fun _ cs _ => cs ∈ permCheckLangIn
    toFun_empty := fun _ => Iff.rfl
    toFun_next := fun _ _ _ _ h _ => h
    toFun_full := fun cs tr hcs => ?_
  }, ?_⟩
  · rw [probEvent_eq_zero_iff]
    intro out hout houtLang
    rw [OptionT.mem_support_iff] at hout
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
    obtain ⟨s, _, hout⟩ := hout
    simp only [Verifier.run, permCheckVerifier_verify_eq] at hout
    by_cases hAccept : CopyConstraintsSatisfied (tr ⟨0, by simp⟩) cs.perm
    · exact hcs ⟨tr ⟨0, by simp⟩, hAccept⟩
    · have hrun :
          (simulateQ impl
            ((permCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
              (numGates := numGates)).run cs tr)).run' s =
            pure none := by
        simp only [Verifier.run, permCheckVerifier_verify_eq]
        split_ifs with h
        · exact False.elim (hAccept (by simpa using h))
        change (simulateQ impl (pure none : OracleComp []ₒ
          (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
            (Fin (3 * numGates) → 𝓡))))).run' s = pure none
        rw [simulateQ_pure]
        change Prod.fst <$> (pure none : StateT σ ProbComp
          (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
            (Fin (3 * numGates) → 𝓡)))).run s = pure none
        rw [StateT.run_pure]
        simp [map_pure]
      simp only [Verifier.run, permCheckVerifier_verify_eq] at hrun
      rw [hrun] at hout
      simp at hout
  · intro _ hNotIn _ _ _ _ ⟨⟨0, _⟩, hdir⟩
    exact absurd hdir (by simp)

omit [CommRing 𝓡] in
/-- The permutation-check verifier has ordinary zero-error soundness. A successful malicious
execution outside `permCheckLangIn` must pass the copy-constraint guard on the prover's single
message, which directly gives the missing satisfying extended assignment. -/
theorem permCheckVerifier_soundness :
    (permCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).soundness init impl
        permCheckLangIn permCheckLangOut 0 := by
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
          simp only [permCheckVerifier_verify_eq] at hx
          by_cases hAccept : CopyConstraintsSatisfied sendState.1 cs.perm
          · exact ⟨sendState.1, hAccept⟩
          · rw [if_neg hAccept] at hx
            let Result :=
              Option (((permCheckPSpec 𝓡 numGates).FullTranscript ×
                (Plonk.ConstraintSystem 𝓡 numWires numGates ×
                  (Fin (3 * numGates) → 𝓡)) × WitOut) ×
                Plonk.ConstraintSystem 𝓡 numWires numGates ×
                  (Fin (3 * numGates) → 𝓡))
            change (runOpt, s') ∈ support
              (((simulateQ
                (impl.addLift (challengeQueryImpl (pSpec := permCheckPSpec 𝓡 numGates)))
                (pure none : OracleComp _ Result) :
                  StateT σ ProbComp Result).run s2)) at hx
            rw [simulateQ_pure, StateT.run_pure] at hx
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rw [hx.1] at hrunOpt
            simp at hrunOpt

omit [CommRing 𝓡] in
/-- The permutation-check verifier has zero-error round-by-round knowledge soundness: the single
prover message is the extended wire assignment, and the verifier guard ensures it satisfies the
copy constraints whenever the verifier can output a related statement. -/
lemma permCheckVerifier_rbrKnowledgeSoundness :
    (permCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).rbrKnowledgeSoundness init impl permCheckRelIn permCheckRelOut 0 := by
  refine ⟨fun _ => Fin (3 * numGates) → 𝓡, {
    eqIn := rfl
    extractMid := fun ⟨0, _⟩ _stmt _tr witMid => witMid
    extractOut := fun _stmt tr _ => tr ⟨0, by omega⟩
  }, {
    toFun := fun _ stmt _tr wit => (stmt, wit) ∈ permCheckRelIn
    toFun_empty := fun _ _ => by simp
    toFun_next := fun ⟨0, _⟩ _ _stmt _tr _msg _witMid h => h
    toFun_full := fun stmt tr _witOut hpr => by
      rw [gt_iff_lt, probEvent_pos_iff] at hpr
      obtain ⟨_x, hx, _hrel⟩ := hpr
      rw [OptionT.mem_support_iff] at hx
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
      obtain ⟨s, _, hx⟩ := hx
      by_cases hAccept : CopyConstraintsSatisfied (tr ⟨0, by simp⟩) stmt.perm
      · simpa [permCheckRelIn] using hAccept
      · exfalso
        have hrun :
            (simulateQ impl
              ((permCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
                (numGates := numGates)).run stmt tr)).run' s =
              pure none := by
          simp only [Verifier.run, permCheckVerifier_verify_eq]
          split_ifs with h
          · exact False.elim (hAccept (by simpa using h))
          change (simulateQ impl (pure none : OracleComp []ₒ
            (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
              (Fin (3 * numGates) → 𝓡))))).run' s = pure none
          rw [simulateQ_pure]
          change Prod.fst <$> (pure none : StateT σ ProbComp
            (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
              (Fin (3 * numGates) → 𝓡)))).run s = pure none
          rw [StateT.run_pure]
          simp [map_pure]
        rw [hrun] at hx
        simp at hx
  }, ?_⟩
  intro _stmtIn _witIn _prover ⟨⟨0, _⟩, hdir⟩
  exact absurd hdir (by simp)

#print axioms Plonk.permCheckVerifier_verify_eq
#print axioms Plonk.permCheckVerifier_mem_support_iff
#print axioms Plonk.permCheck_perfectCompleteness
#print axioms Plonk.permCheckVerifier_rbrSoundness
#print axioms Plonk.permCheckVerifier_soundness
#print axioms Plonk.permCheckVerifier_rbrKnowledgeSoundness

end PermutationCheck

end Plonk

end
