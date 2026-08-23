/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Plonk.Basic
import ArkLib.ProofSystem.Plonk.PermutationCheck
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Plonk Check Composition

This file packages the existing Plonk gate check with a post-gate permutation check.

The second phase consumes the gate-check output `(cs, w)`, sends the extended wire assignment
computed from `w`, and verifies both that the sent extended assignment is pointwise the extension
of `w` and that it satisfies the copy-constraint permutation.
-/

noncomputable section

namespace Plonk

open OracleComp OracleSpec ProtocolSpec

section Composition

variable (𝓡 : Type) [CommRing 𝓡] [DecidableEq 𝓡] (numWires numGates : ℕ)

/-- The extended assignment message agrees pointwise with the extension of the gate witness. -/
@[reducible]
def ExtendedWireAssignmentMatches
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (w : Fin numWires → 𝓡) (f : Fin (3 * numGates) → 𝓡) : Prop :=
  ∀ j, f j =
    extendWireAssignment (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates) cs w j

/-- Permutation phase specialized to the statement produced by the gate check. -/
@[reducible]
def permCheckAfterGateProver :
    Prover []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (permCheckPSpec 𝓡 numGates) where
  PrvState
  | 0 => Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)
  | 1 => Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)
  input := fun ⟨stmt, _⟩ => stmt
  sendMessage := fun | ⟨0, _⟩ => fun ⟨cs, w⟩ =>
    pure <|
      (extendWireAssignment (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates) cs w,
        ⟨cs, w⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun stmt => pure (stmt, ())

/-- Verifier for the post-gate permutation phase. -/
@[reducible]
def permCheckAfterGateVerifier :
    Verifier []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
      (permCheckPSpec 𝓡 numGates) where
  verify := fun ⟨cs, w⟩ transcript =>
    let f : Fin (3 * numGates) → 𝓡 := transcript 0
    if ExtendedWireAssignmentMatches 𝓡 numWires numGates cs w f ∧
      CopyConstraintsSatisfied f cs.perm then
      pure ⟨cs, w⟩
    else
      failure

omit [CommRing 𝓡] in
theorem permCheckAfterGateVerifier_verify_eq
    (stmt : Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
    (transcript : FullTranscript (permCheckPSpec 𝓡 numGates)) :
    (permCheckAfterGateVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).verify stmt transcript =
      if ExtendedWireAssignmentMatches 𝓡 numWires numGates stmt.1 stmt.2 (transcript 0) ∧
          CopyConstraintsSatisfied (transcript 0) stmt.1.perm then
        pure stmt
      else
        failure := by
  rcases stmt with ⟨cs, w⟩
  rfl

omit [CommRing 𝓡] in
theorem permCheckAfterGateVerifier_mem_support_iff
    (stmt : Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
    (transcript : FullTranscript (permCheckPSpec 𝓡 numGates))
    (out : Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :
    some out ∈ support
      ((permCheckAfterGateVerifier (𝓡 := 𝓡) (numWires := numWires)
        (numGates := numGates)).verify stmt transcript).run ↔
      ExtendedWireAssignmentMatches 𝓡 numWires numGates stmt.1 stmt.2 (transcript 0) ∧
        CopyConstraintsSatisfied (transcript 0) stmt.1.perm ∧ out = stmt := by
  rw [permCheckAfterGateVerifier_verify_eq]
  by_cases hMatch :
      ExtendedWireAssignmentMatches 𝓡 numWires numGates stmt.1 stmt.2 (transcript 0)
  · by_cases hCopy : CopyConstraintsSatisfied (transcript 0) stmt.1.perm
    · rw [if_pos ⟨hMatch, hCopy⟩]
      constructor
      · intro hout
        exact ⟨hMatch, hCopy, by simpa using hout⟩
      · intro h
        simp [h.2.2]
    · rw [if_neg (by intro h; exact hCopy h.2)]
      simp [hCopy]
  · rw [if_neg (by intro h; exact hMatch h.1)]
    simp [hMatch]

/-- Reduction for the post-gate permutation phase. -/
@[reducible]
def permCheckAfterGateReduction :
    Reduction []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (permCheckPSpec 𝓡 numGates) where
  prover := permCheckAfterGateProver 𝓡 numWires numGates
  verifier := permCheckAfterGateVerifier 𝓡 numWires numGates

/-- Two-message Plonk check protocol: gate assignment, then extended permutation assignment. -/
@[reducible]
def plonkCheckPSpec : ProtocolSpec 2 :=
  gateCheckPSpec 𝓡 numWires ++ₚ permCheckPSpec 𝓡 numGates

omit [CommRing 𝓡] [DecidableEq 𝓡] in
private theorem plonkCheckPSpec_challengeIdx_false
    (i : (plonkCheckPSpec 𝓡 numWires numGates).ChallengeIdx) : False := by
  rcases i with ⟨i, hdir⟩
  have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  rcases hi with hi | hi
  · have : i = ⟨0, by omega⟩ := by ext; exact hi
    rw [this] at hdir
    simp [Fin.vappend_eq_append] at hdir
  · have : i = ⟨1, by omega⟩ := by ext; exact hi
    rw [this] at hdir
    change Fin.append
        (fun i : Fin 1 => match i with | 0 => Direction.P_to_V)
        (fun i : Fin 1 => match i with | 0 => Direction.P_to_V)
        (Fin.natAdd 1 (0 : Fin 1)) = Direction.V_to_P at hdir
    rw [Fin.append_right] at hdir
    simp at hdir

instance : ∀ i, VCVCompatible ((plonkCheckPSpec 𝓡 numWires numGates).Challenge i) :=
  fun i => False.elim (plonkCheckPSpec_challengeIdx_false 𝓡 numWires numGates i)

instance : ∀ i, SampleableType ((plonkCheckPSpec 𝓡 numWires numGates).Challenge i) :=
  fun i => False.elim (plonkCheckPSpec_challengeIdx_false 𝓡 numWires numGates i)

@[reducible]
def plonkCheckProver :
    Prover []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates) (Fin numWires → 𝓡)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (plonkCheckPSpec 𝓡 numWires numGates) :=
  Prover.append
    (gateCheckProver (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates))
    (permCheckAfterGateProver 𝓡 numWires numGates)

@[reducible]
def plonkCheckVerifier :
    Verifier []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
      (plonkCheckPSpec 𝓡 numWires numGates) :=
  Verifier.append
    (gateCheckVerifier (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates))
    (permCheckAfterGateVerifier 𝓡 numWires numGates)

theorem plonkCheckVerifier_verify_eq
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (transcript : FullTranscript (plonkCheckPSpec 𝓡 numWires numGates)) :
    (plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).verify cs transcript =
      let w : Fin numWires → 𝓡 := transcript.fst ⟨0, by simp⟩
      let f : Fin (3 * numGates) → 𝓡 := transcript.snd ⟨0, by simp⟩
      if cs.accepts w ∧
          ExtendedWireAssignmentMatches 𝓡 numWires numGates cs w f ∧
            CopyConstraintsSatisfied f cs.perm then
        pure (cs, w)
      else
        failure := by
  simp only [plonkCheckVerifier, Verifier.append, gateCheckVerifier, guard_eq]
  by_cases hGate : cs.accepts (transcript.fst 0)
  · by_cases hPerm :
        ExtendedWireAssignmentMatches 𝓡 numWires numGates cs (transcript.fst 0)
          (transcript.snd 0) ∧
          CopyConstraintsSatisfied (transcript.snd 0) cs.perm
    · simp [hGate, hPerm]
    · simp [hGate, hPerm]
  · simp [hGate]

theorem plonkCheckVerifier_mem_support_iff
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (transcript : FullTranscript (plonkCheckPSpec 𝓡 numWires numGates))
    (out : Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :
    some out ∈ support
      ((plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
        (numGates := numGates)).verify cs transcript).run ↔
      let w : Fin numWires → 𝓡 := transcript.fst ⟨0, by simp⟩
      let f : Fin (3 * numGates) → 𝓡 := transcript.snd ⟨0, by simp⟩
      cs.accepts w ∧
        ExtendedWireAssignmentMatches 𝓡 numWires numGates cs w f ∧
          CopyConstraintsSatisfied f cs.perm ∧ out = (cs, w) := by
  rw [plonkCheckVerifier_verify_eq]
  let w : Fin numWires → 𝓡 := transcript.fst ⟨0, by simp⟩
  let f : Fin (3 * numGates) → 𝓡 := transcript.snd ⟨0, by simp⟩
  by_cases hAccept :
      cs.accepts w ∧ ExtendedWireAssignmentMatches 𝓡 numWires numGates cs w f ∧
        CopyConstraintsSatisfied f cs.perm
  · rw [if_pos hAccept]
    constructor
    · intro hout
      exact ⟨hAccept.1, hAccept.2.1, hAccept.2.2, by simpa using hout⟩
    · intro h
      simp [h.2.2.2]
  · rw [if_neg hAccept]
    constructor
    · simp
    · intro h
      exact False.elim (hAccept ⟨h.1, h.2.1, h.2.2.1⟩)

@[reducible]
def plonkCheckReduction :
    Reduction []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates) (Fin numWires → 𝓡)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (plonkCheckPSpec 𝓡 numWires numGates) where
  prover := plonkCheckProver 𝓡 numWires numGates
  verifier := plonkCheckVerifier 𝓡 numWires numGates

theorem plonkCheckReduction_eq_append :
    plonkCheckReduction 𝓡 numWires numGates =
      Reduction.append
        (gateCheckReduction (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates))
        (permCheckAfterGateReduction 𝓡 numWires numGates) := rfl

@[reducible, simp]
def plonkCheckRel :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :=
  { p | p.1.accepts p.2 ∧
      CopyConstraintsSatisfied
        (extendWireAssignment (𝓡 := 𝓡) (numWires := numWires)
          (numGates := numGates) p.1 p.2) p.1.perm }

@[reducible, simp]
def plonkCheckRelIn :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :=
  plonkCheckRel 𝓡 numWires numGates

@[reducible, simp]
def plonkCheckRelOut :
    Set ((Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) × Unit) :=
  Prod.fst ⁻¹' plonkCheckRel 𝓡 numWires numGates

@[reducible, simp]
def plonkCheckLangIn :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates) :=
  { cs | ∃ w : Fin numWires → 𝓡, (cs, w) ∈ plonkCheckRel 𝓡 numWires numGates }

@[reducible, simp]
def plonkCheckLangOut :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :=
  plonkCheckRel 𝓡 numWires numGates

theorem plonkCheckVerifier_mem_support_relations
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (transcript : FullTranscript (plonkCheckPSpec 𝓡 numWires numGates))
    (out : Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
    (hout : some out ∈ support
      ((plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
        (numGates := numGates)).verify cs transcript).run) :
    (cs, transcript.fst ⟨0, by simp⟩) ∈ plonkCheckRelIn 𝓡 numWires numGates ∧
      (out, ()) ∈ plonkCheckRelOut 𝓡 numWires numGates ∧
        out = (cs, transcript.fst ⟨0, by simp⟩) := by
  rw [plonkCheckVerifier_mem_support_iff] at hout
  let w : Fin numWires → 𝓡 := transcript.fst ⟨0, by simp⟩
  let f : Fin (3 * numGates) → 𝓡 := transcript.snd ⟨0, by simp⟩
  have hRel : (cs, w) ∈ plonkCheckRel 𝓡 numWires numGates := by
    change cs.accepts w ∧
      CopyConstraintsSatisfied
        (extendWireAssignment (𝓡 := 𝓡) (numWires := numWires)
          (numGates := numGates) cs w) cs.perm
    refine ⟨hout.1, ?_⟩
    intro i
    rw [← hout.2.1 (cs.perm i), ← hout.2.1 i]
    exact hout.2.2.1 i
  refine ⟨?_, ?_, ?_⟩
  · simpa [w]
  · rw [hout.2.2.2]
    simpa [plonkCheckRelOut, w] using hRel
  · simpa [w] using hout.2.2.2

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The post-gate permutation verifier has zero-error round-by-round soundness for the full
gate-and-copy language on its `(cs, w)` statement. The verifier returns only the input statement,
so any accepted output in `plonkCheckLangOut` immediately puts the input statement in the same
language. -/
theorem permCheckAfterGateVerifier_rbrSoundness :
    (permCheckAfterGateVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).rbrSoundness init impl
        (plonkCheckLangOut 𝓡 numWires numGates)
        (plonkCheckLangOut 𝓡 numWires numGates) 0 := by
  refine ⟨{
    toFun := fun _ stmt _ => stmt ∈ plonkCheckLangOut 𝓡 numWires numGates
    toFun_empty := fun _ => Iff.rfl
    toFun_next := fun _ _ _ _ h _ => h
    toFun_full := fun stmt tr hstmt => by
      rcases stmt with ⟨cs, w⟩
      rw [probEvent_eq_zero_iff]
      intro out hout houtLang
      rw [OptionT.mem_support_iff] at hout
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
      obtain ⟨s, _, hout⟩ := hout
      by_cases hAccept :
          ExtendedWireAssignmentMatches 𝓡 numWires numGates cs w (tr ⟨0, by simp⟩) ∧
            CopyConstraintsSatisfied (tr ⟨0, by simp⟩) cs.perm
      · have hrun :
            (simulateQ impl
              ((permCheckAfterGateVerifier (𝓡 := 𝓡) (numWires := numWires)
                (numGates := numGates)).run (cs, w) tr)).run' s =
              pure (some (cs, w)) := by
          simp only [Verifier.run]
          split_ifs with h
          · change (simulateQ impl (pure (some (cs, w)) : OracleComp []ₒ
                (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
                  (Fin numWires → 𝓡))))).run' s =
              pure (some (cs, w))
            rw [simulateQ_pure]
            change Prod.fst <$> (pure (some (cs, w)) : StateT σ ProbComp
              (Option (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)))).run s =
              pure (some (cs, w))
            rw [StateT.run_pure]
            simp [map_pure]
          · exact False.elim (h (by simpa using hAccept))
        rw [hrun] at hout
        simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hout
        subst out
        exact hstmt houtLang
      · have hrun :
            (simulateQ impl
              ((permCheckAfterGateVerifier (𝓡 := 𝓡) (numWires := numWires)
                (numGates := numGates)).run (cs, w) tr)).run' s =
              pure none := by
          simp only [Verifier.run]
          split_ifs with h
          · exact False.elim (hAccept (by simpa using h))
          · change (simulateQ impl (pure none : OracleComp []ₒ
                (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
                  (Fin numWires → 𝓡))))).run' s =
              pure none
            rw [simulateQ_pure]
            change Prod.fst <$> (pure none : StateT σ ProbComp
              (Option (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)))).run s =
              pure none
            rw [StateT.run_pure]
            simp [map_pure]
        rw [hrun] at hout
        simp at hout
  }, ?_⟩
  intro _ _ _ _ _ _ ⟨⟨0, _⟩, hdir⟩
  exact absurd hdir (by simp)

/-- The composed two-message Plonk verifier has zero-error round-by-round soundness for the
gate-and-copy satisfiability language. Since both rounds are prover-message rounds, the RBR
challenge condition is empty; a successful full transcript directly exposes the satisfying gate
witness. -/
theorem plonkCheckVerifier_rbrSoundness :
    (plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).rbrSoundness init impl
        (plonkCheckLangIn 𝓡 numWires numGates)
        (plonkCheckLangOut 𝓡 numWires numGates) 0 := by
  refine ⟨{
    toFun := fun _ cs _ => cs ∈ plonkCheckLangIn 𝓡 numWires numGates
    toFun_empty := fun _ => Iff.rfl
    toFun_next := fun _ _ _ _ h _ => h
    toFun_full := fun cs tr hcs => ?_
  }, ?_⟩
  · rw [probEvent_eq_zero_iff]
    intro out hout houtLang
    rw [OptionT.mem_support_iff] at hout
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
    obtain ⟨s, _, hout⟩ := hout
    let w : Fin numWires → 𝓡 := tr.fst ⟨0, by simp⟩
    let f : Fin (3 * numGates) → 𝓡 := tr.snd ⟨0, by simp⟩
    by_cases hAccept :
        cs.accepts w ∧ ExtendedWireAssignmentMatches 𝓡 numWires numGates cs w f ∧
          CopyConstraintsSatisfied f cs.perm
    · have hrun :
          (simulateQ impl
            ((plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
              (numGates := numGates)).run cs tr)).run' s =
            pure (some (cs, w)) := by
        simp only [Verifier.run, plonkCheckVerifier_verify_eq]
        split_ifs with h
        · change (simulateQ impl (pure (some (cs, w)) : OracleComp []ₒ
              (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
                (Fin numWires → 𝓡))))).run' s =
            pure (some (cs, w))
          rw [simulateQ_pure]
          change Prod.fst <$> (pure (some (cs, w)) : StateT σ ProbComp
            (Option (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)))).run s =
            pure (some (cs, w))
          rw [StateT.run_pure]
          simp [map_pure]
        · exact False.elim (h (by simpa using hAccept))
      rw [hrun] at hout
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hout
      subst out
      exact hcs ⟨w, houtLang⟩
    · have hrun :
          (simulateQ impl
            ((plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
              (numGates := numGates)).run cs tr)).run' s =
            pure none := by
        simp only [Verifier.run, plonkCheckVerifier_verify_eq]
        split_ifs with h
        · exact False.elim (hAccept (by simpa using h))
        · change (simulateQ impl (pure none : OracleComp []ₒ
              (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
                (Fin numWires → 𝓡))))).run' s =
            pure none
          rw [simulateQ_pure]
          change Prod.fst <$> (pure none : StateT σ ProbComp
            (Option (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)))).run s =
            pure none
          rw [StateT.run_pure]
          simp [map_pure]
      rw [hrun] at hout
      simp at hout
  · intro _ _ _ _ _ _ i
    exact False.elim (plonkCheckPSpec_challengeIdx_false 𝓡 numWires numGates i)

/-- The composed two-message Plonk verifier has ordinary zero-error soundness. Any successful
malicious execution outside `plonkCheckLangIn` must pass the composed verifier guard, and the
first prover message then directly supplies the missing satisfying gate-and-copy witness. -/
theorem plonkCheckVerifier_soundness :
    (plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).soundness init impl
        (plonkCheckLangIn 𝓡 numWires numGates)
        (plonkCheckLangOut 𝓡 numWires numGates) 0 := by
  unfold Verifier.soundness
  intro WitIn WitOut witIn prover cs hcs
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, probEvent_eq_zero_iff]
  intro x hx _hxLang
  rcases x with ⟨⟨tr, _prvOut, _witOut⟩, out⟩
  apply hcs
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _hs, hx⟩ := hx
  unfold Reduction.run at hx
  simp only [StateT.run'_eq, OptionT.run_bind, Option.elimM, support_map, Set.mem_image] at hx
  obtain ⟨⟨runOpt, s'⟩, hx, hrunOpt⟩ := hx
  simp only at hrunOpt
  rw [simulateQ_bind] at hx
  rw [StateT.run_bind] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨⟨proverOpt, s1⟩, hprover, hx⟩ := hx
  cases proverOpt with
  | none =>
      simp only [Option.elim_none] at hx
      rw [simulateQ_pure, StateT.run_pure] at hx
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rw [hx.1] at hrunOpt
      simp at hrunOpt
  | some proverResult =>
      simp only [Option.elim_some] at hx
      rw [simulateQ_bind] at hx
      rw [StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨⟨verifierOpt, s2⟩, hverifier, hx⟩ := hx
      cases verifierOpt with
      | none =>
          simp only [Option.elim_none] at hx
          rw [simulateQ_pure, StateT.run_pure] at hx
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rw [hx.1] at hrunOpt
          simp at hrunOpt
      | some verifierResult =>
          simp only [Option.elim_some] at hx
          let w : Fin numWires → 𝓡 := proverResult.1.fst ⟨0, by simp⟩
          let f : Fin (3 * numGates) → 𝓡 := proverResult.1.snd ⟨0, by simp⟩
          by_cases hAccept :
              cs.accepts w ∧ ExtendedWireAssignmentMatches 𝓡 numWires numGates cs w f ∧
                CopyConstraintsSatisfied f cs.perm
          · refine ⟨w, hAccept.1, ?_⟩
            intro i
            rw [← hAccept.2.1 (cs.perm i), ← hAccept.2.1 i]
            exact hAccept.2.2 i
          · simp only [Verifier.run, plonkCheckVerifier_verify_eq] at hverifier
            rw [if_neg hAccept] at hverifier
            rw [OptionT.run_failure] at hverifier
            rw [liftM_pure] at hverifier
            rw [OptionT.run_pure] at hverifier
            rw [simulateQ_pure] at hverifier
            rw [StateT.run_pure] at hverifier
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq]
              at hverifier
            rw [hverifier.1] at hx
            simp only [Option.getM_none, OptionT.run_failure] at hx
            simp only [pure_bind, Option.elim_none] at hx
            rw [simulateQ_pure, StateT.run_pure] at hx
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rw [hx.1] at hrunOpt
            simp at hrunOpt

/-- The composed two-message Plonk verifier has ordinary zero-error straightline knowledge
soundness. The extractor is deterministic: it reads the input witness from the first prover message
of the full transcript. Any supported accepting run then forces the verifier output to be exactly
`(cs, transcript.fst 0)`, so output-relation validity cannot coexist with extractor failure. -/
theorem plonkCheckVerifier_knowledgeSoundness :
    (plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).knowledgeSoundness init impl
        (plonkCheckRelIn 𝓡 numWires numGates)
        (plonkCheckRelOut 𝓡 numWires numGates) 0 := by
  unfold Verifier.knowledgeSoundness
  refine ⟨fun _stmt _witOut tr _proveLog _verifyLog => pure (tr.fst ⟨0, by simp⟩),
    fun stmtIn witIn prover => ?_⟩
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, probEvent_eq_zero_iff]
  intro x hx hbad
  rcases x with ⟨cs, extracted, stmtOut, witOut⟩
  simp only at hbad
  apply hbad.1
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _hs, hx⟩ := hx
  simp only [StateT.run'_eq, OptionT.run_bind, Option.elimM, support_map, Set.mem_image] at hx
  obtain ⟨⟨execOpt, s'⟩, hx, hexecOpt⟩ := hx
  simp only at hexecOpt
  rw [simulateQ_bind] at hx
  rw [StateT.run_bind] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨⟨runLogOpt, s1⟩, hrunLog, hx⟩ := hx
  cases runLogOpt with
  | none =>
      simp only [Option.elim_none] at hx
      rw [simulateQ_pure, StateT.run_pure] at hx
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rw [hx.1] at hexecOpt
      simp at hexecOpt
  | some runLog =>
      simp only [Option.elim_some] at hx
      rw [simulateQ_bind] at hx
      rw [StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨⟨extractOpt, s2⟩, hextract, hx⟩ := hx
      rw [liftM_pure] at hextract
      rw [OptionT.run_pure] at hextract
      rw [simulateQ_pure, StateT.run_pure] at hextract
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hextract
      rw [hextract.1, hextract.2] at hx
      simp only [Option.elim_some] at hx
      rw [OptionT.run_pure] at hx
      rw [simulateQ_pure, StateT.run_pure] at hx
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rw [hx.1] at hexecOpt
      simp only [Option.some.injEq] at hexecOpt
      have hstmt : stmtIn = cs := congrArg Prod.fst hexecOpt
      have hextracted : runLog.1.1.1.fst ⟨0, by simp⟩ = extracted :=
        congrArg (fun y => y.2.1) hexecOpt
      rw [← hstmt, ← hextracted]
      have hrunSupport :
          (some runLog.1, s1) ∈ support
            ((simulateQ (impl.addLift challengeQueryImpl)
              (((Reduction.mk prover
                (plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
                  (numGates := numGates))).run stmtIn witIn).run) :
                StateT σ ProbComp _).run s) := by
        have hdiscard := Reduction.runWithLog_discard_logs_eq_run
          (reduction := Reduction.mk prover
            (plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
              (numGates := numGates)))
          (stmt := stmtIn) (wit := witIn)
        have heq := congrArg OptionT.run hdiscard
        simp only [OptionT.run_map] at heq
        have hmap :
            (some runLog.1, s1) ∈ support
              ((((Option.map Prod.fst) <$>
                simulateQ (impl.addLift challengeQueryImpl)
                  ((Reduction.runWithLog stmtIn witIn
                    (Reduction.mk prover
                      (plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
                        (numGates := numGates)))).run)) :
                  StateT σ ProbComp _).run s) := by
          rw [StateT.run_map, support_map, Set.mem_image]
          exact ⟨(some runLog, s1), hrunLog, rfl⟩
        rw [← simulateQ_map, heq] at hmap
        exact hmap
      unfold Reduction.run at hrunSupport
      simp only [OptionT.run_bind, Option.elimM] at hrunSupport
      rw [simulateQ_bind] at hrunSupport
      rw [StateT.run_bind] at hrunSupport
      rw [mem_support_bind_iff] at hrunSupport
      obtain ⟨⟨proverOpt, sp⟩, _hprover, hrunSupport⟩ := hrunSupport
      cases proverOpt with
      | none =>
          simp only [Option.elim_none] at hrunSupport
          rw [simulateQ_pure, StateT.run_pure] at hrunSupport
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq]
            at hrunSupport
          exact False.elim hrunSupport.1
      | some proverResult =>
          simp only [Option.elim_some] at hrunSupport
          rw [simulateQ_bind] at hrunSupport
          rw [StateT.run_bind] at hrunSupport
          rw [mem_support_bind_iff] at hrunSupport
          obtain ⟨⟨verifierOpt, sv⟩, hverifier, hrunSupport⟩ := hrunSupport
          cases verifierOpt with
          | none =>
              simp only [Option.elim_none] at hrunSupport
              rw [simulateQ_pure, StateT.run_pure] at hrunSupport
              simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq]
                at hrunSupport
              exact False.elim hrunSupport.1
          | some verifierResult =>
              simp only [Option.elim_some] at hrunSupport
              cases verifierResult with
              | none =>
                  simp only [Option.getM_none, OptionT.run_failure, pure_bind, Option.elim_none]
                    at hrunSupport
                  rw [simulateQ_pure, StateT.run_pure] at hrunSupport
                  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq]
                    at hrunSupport
                  exact False.elim hrunSupport.1
              | some verifierOut =>
                  simp only [Option.getM_some, OptionT.run_pure, pure_bind, Option.elim_some]
                    at hrunSupport
                  rw [simulateQ_pure, StateT.run_pure] at hrunSupport
                  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
                    Option.some.injEq] at hrunSupport
                  have htr : runLog.1.1.1 = proverResult.1 := by
                    exact congrArg (fun y => y.1.1) hrunSupport.1
                  rw [htr]
                  let w : Fin numWires → 𝓡 := proverResult.1.fst ⟨0, by simp⟩
                  let f : Fin (3 * numGates) → 𝓡 := proverResult.1.snd ⟨0, by simp⟩
                  by_cases hAccept :
                      stmtIn.accepts w ∧
                        ExtendedWireAssignmentMatches 𝓡 numWires numGates stmtIn w f ∧
                          CopyConstraintsSatisfied f stmtIn.perm
                  · refine ⟨hAccept.1, ?_⟩
                    intro i
                    rw [← hAccept.2.1 (stmtIn.perm i), ← hAccept.2.1 i]
                    exact hAccept.2.2 i
                  · simp only [Verifier.run, plonkCheckVerifier_verify_eq] at hverifier
                    rw [if_neg hAccept] at hverifier
                    rw [OptionT.run_failure] at hverifier
                    rw [liftM_pure] at hverifier
                    rw [OptionT.run_pure] at hverifier
                    rw [simulateQ_pure] at hverifier
                    rw [StateT.run_pure] at hverifier
                    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
                      at hverifier
                    exact False.elim (by simpa using hverifier.1)

/-- The composed two-message Plonk verifier has zero-error round-by-round knowledge soundness. The
round-by-round extractor keeps the gate witness as the intermediate witness and reads the final
input witness from the first prover message of the full transcript. -/
theorem plonkCheckVerifier_rbrKnowledgeSoundness :
    (plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).rbrKnowledgeSoundness init impl
        (plonkCheckRelIn 𝓡 numWires numGates)
        (plonkCheckRelOut 𝓡 numWires numGates) 0 := by
  refine ⟨fun _ => Fin numWires → 𝓡, {
    eqIn := rfl
    extractMid := fun _ _ _ witMid => witMid
    extractOut := fun _stmt tr _ => tr.fst ⟨0, by simp⟩
  }, {
    toFun := fun _ stmt _tr wit => (stmt, wit) ∈ plonkCheckRelIn 𝓡 numWires numGates
    toFun_empty := fun _ _ => by simp
    toFun_next := fun _ _ _ _ _ _ h => h
    toFun_full := fun cs tr _witOut hpr => by
      rw [gt_iff_lt, probEvent_pos_iff] at hpr
      obtain ⟨_out, hout, _houtRel⟩ := hpr
      rw [OptionT.mem_support_iff] at hout
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
      obtain ⟨s, _, hout⟩ := hout
      let w : Fin numWires → 𝓡 := tr.fst ⟨0, by simp⟩
      let f : Fin (3 * numGates) → 𝓡 := tr.snd ⟨0, by simp⟩
      by_cases hAccept :
          cs.accepts w ∧ ExtendedWireAssignmentMatches 𝓡 numWires numGates cs w f ∧
            CopyConstraintsSatisfied f cs.perm
      · change (cs, w) ∈ plonkCheckRelIn 𝓡 numWires numGates
        refine ⟨hAccept.1, ?_⟩
        intro i
        rw [← hAccept.2.1 (cs.perm i), ← hAccept.2.1 i]
        exact hAccept.2.2 i
      · exfalso
        have hrun :
            (simulateQ impl
              ((plonkCheckVerifier (𝓡 := 𝓡) (numWires := numWires)
                (numGates := numGates)).run cs tr)).run' s =
              pure none := by
          simp only [Verifier.run, plonkCheckVerifier_verify_eq]
          split_ifs with h
          · exact False.elim (hAccept (by simpa using h))
          · change (simulateQ impl (pure none : OracleComp []ₒ
                (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
                  (Fin numWires → 𝓡))))).run' s =
              pure none
            rw [simulateQ_pure]
            change Prod.fst <$> (pure none : StateT σ ProbComp
              (Option (Plonk.ConstraintSystem 𝓡 numWires numGates ×
                (Fin numWires → 𝓡)))).run s =
              pure none
            rw [StateT.run_pure]
            simp [map_pure]
        rw [hrun] at hout
        simp at hout
  }, ?_⟩
  intro _stmtIn _witIn _prover i
  exact False.elim (plonkCheckPSpec_challengeIdx_false 𝓡 numWires numGates i)

#print axioms Plonk.plonkCheckVerifier_verify_eq
#print axioms Plonk.plonkCheckVerifier_mem_support_iff
#print axioms Plonk.plonkCheckVerifier_mem_support_relations
#print axioms Plonk.permCheckAfterGateVerifier_verify_eq
#print axioms Plonk.permCheckAfterGateVerifier_mem_support_iff
#print axioms Plonk.plonkCheckReduction_eq_append
#print axioms Plonk.plonkCheckRel
#print axioms Plonk.plonkCheckLangIn
#print axioms Plonk.plonkCheckLangOut
#print axioms Plonk.permCheckAfterGateVerifier_rbrSoundness
#print axioms Plonk.plonkCheckVerifier_rbrSoundness
#print axioms Plonk.plonkCheckVerifier_soundness
#print axioms Plonk.plonkCheckVerifier_knowledgeSoundness
#print axioms Plonk.plonkCheckVerifier_rbrKnowledgeSoundness

end Composition

end Plonk

end
