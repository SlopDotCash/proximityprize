/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.BCS.Basic

/-!
  # BCS compiler-frontier characterization bricks (#62)

  `ArkLib/OracleReduction/BCS/Basic.lean` defines `BCSCompilerFrontierSatisfied` (the seven-conjunct
  checklist that must be discharged before `BCSCompiledPhases.toReduction` becomes a genuine compiler
  theorem), `BCSPhaseRealizationFrontier` (its first two conjuncts), and individual field projectors.
  It also provides `.intro` (assemble from the phase frontier plus the five security fields) and the
  `.phase` projector.

  This module closes the round-trip on that interface: it characterizes the full checklist as exactly
  `BCSPhaseRealizationFrontier phases ∧ <the five security fields>` (the `iff`), and supplies the
  missing `.security` half-projector together with a phase+security recombination lemma. With the
  `iff` in hand, a downstream consumer can move between the packaged checklist and its component
  bricks by a single rewrite, rather than re-deriving the seven-way conjunction shape each time.

  These are pure logical equivalences over the existing frontier definitions; they construct no
  phase, prove no preservation theorem, and discharge no security obligation.
-/

namespace OracleReduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

variable {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}

variable {StmtIn StmtOut WitIn WitOut : Type}

variable {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}

/-- **The five security-side obligations of a ready BCS compiler frontier**, packaged as one
conjunction. This is the security counterpart of `BCSPhaseRealizationFrontier` (which packages the
two phase-realization obligations). -/
def BCSSecurityFrontierTargets
    (frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases) : Prop :=
  frontier.commitment_correctness_available ∧
  frontier.commitment_binding_or_extractability_available ∧
  frontier.completeness_preservation_target ∧
  frontier.soundness_preservation_target ∧
  frontier.knowledge_soundness_preservation_target

/-- **Characterization of the full BCS compiler-frontier checklist** as the conjunction of the
phase-realization frontier and the five security targets. -/
theorem BCSCompilerFrontierSatisfied_iff :
    BCSCompilerFrontierSatisfied phases frontier ↔
      BCSPhaseRealizationFrontier phases ∧ BCSSecurityFrontierTargets frontier := by
  unfold BCSCompilerFrontierSatisfied BCSPhaseRealizationFrontier BCSSecurityFrontierTargets
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The same characterization for the compatibility name `BCSCompilerFrontierReady`. -/
theorem BCSCompilerFrontierReady_iff :
    BCSCompilerFrontierReady phases frontier ↔
      BCSPhaseRealizationFrontier phases ∧ BCSSecurityFrontierTargets frontier :=
  BCSCompilerFrontierSatisfied_iff

-- NOTE: `BCSCompilerFrontierReady.security` is now provided by `BCS/Basic.lean`
-- (af7ade8e8, returning the definitionally identical `BCSSecurityFrontierSatisfied`),
-- which made the copy here a duplicate declaration. We keep only the `Targets`-typed
-- variant under a distinct name for consumers of the packaged-conjunction interface.

/-- **Project the five security targets** from a ready BCS compiler frontier. The security
counterpart of `BCSCompilerFrontierReady.phase`, stated via `BCSSecurityFrontierTargets`. -/
theorem BCSCompilerFrontierReady.securityTargets
    (h : BCSCompilerFrontierReady phases frontier) :
    BCSSecurityFrontierTargets frontier :=
  (BCSCompilerFrontierReady_iff.mp h).2

/-- **Recombine** a phase-realization frontier and the packaged security targets into a ready
checklist. The packaged-conjunction companion to `BCSCompilerFrontierReady.intro`. -/
theorem BCSCompilerFrontierReady.ofParts
    (hPhase : BCSPhaseRealizationFrontier phases)
    (hSecurity : BCSSecurityFrontierTargets frontier) :
    BCSCompilerFrontierReady phases frontier :=
  BCSCompilerFrontierReady_iff.mpr ⟨hPhase, hSecurity⟩

/-- Assemble the packaged security targets from the five independent bricks. -/
theorem BCSSecurityFrontierTargets.intro
    (hCorrect : frontier.commitment_correctness_available)
    (hBindingOrExtract : frontier.commitment_binding_or_extractability_available)
    (hComplete : frontier.completeness_preservation_target)
    (hSound : frontier.soundness_preservation_target)
    (hKS : frontier.knowledge_soundness_preservation_target) :
    BCSSecurityFrontierTargets frontier :=
  ⟨hCorrect, hBindingOrExtract, hComplete, hSound, hKS⟩

/-- Project commitment correctness from the packaged security targets. -/
theorem BCSSecurityFrontierTargets.commitment_correctness_available
    (h : BCSSecurityFrontierTargets frontier) :
    frontier.commitment_correctness_available :=
  h.1

/-- Project commitment binding/extractability from the packaged security targets. -/
theorem BCSSecurityFrontierTargets.commitment_binding_or_extractability_available
    (h : BCSSecurityFrontierTargets frontier) :
    frontier.commitment_binding_or_extractability_available :=
  h.2.1

/-- Project the completeness-preservation target from the packaged security targets. -/
theorem BCSSecurityFrontierTargets.completeness_preservation_target
    (h : BCSSecurityFrontierTargets frontier) :
    frontier.completeness_preservation_target :=
  h.2.2.1

/-- Project the soundness-preservation target from the packaged security targets. -/
theorem BCSSecurityFrontierTargets.soundness_preservation_target
    (h : BCSSecurityFrontierTargets frontier) :
    frontier.soundness_preservation_target :=
  h.2.2.2.1

/-- Project the knowledge-soundness-preservation target from the packaged security targets. -/
theorem BCSSecurityFrontierTargets.knowledge_soundness_preservation_target
    (h : BCSSecurityFrontierTargets frontier) :
    frontier.knowledge_soundness_preservation_target :=
  h.2.2.2.2

#print axioms BCSSecurityFrontierTargets
#print axioms BCSCompilerFrontierSatisfied_iff
#print axioms BCSCompilerFrontierReady_iff
#print axioms BCSCompilerFrontierReady.security
#print axioms BCSCompilerFrontierReady.securityTargets
#print axioms BCSCompilerFrontierReady.ofParts
#print axioms BCSSecurityFrontierTargets.intro
#print axioms BCSSecurityFrontierTargets.commitment_correctness_available
#print axioms BCSSecurityFrontierTargets.commitment_binding_or_extractability_available
#print axioms BCSSecurityFrontierTargets.completeness_preservation_target
#print axioms BCSSecurityFrontierTargets.soundness_preservation_target
#print axioms BCSSecurityFrontierTargets.knowledge_soundness_preservation_target

end OracleReduction
