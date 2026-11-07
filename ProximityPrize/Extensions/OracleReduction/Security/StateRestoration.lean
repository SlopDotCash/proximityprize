/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Security.StateRestoration

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.Security.Basic

/-!
  # State-Restoration Security Definitions

  This file defines state-restoration security notions for (oracle) reductions.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type}

namespace Prover

end Prover

namespace OracleProver

end OracleProver

namespace Extractor

end Extractor

variable {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
  (impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))

namespace Verifier

namespace StateRestoration

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration soundness is monotone in the allowed soundness error. -/
theorem soundness.mono_error
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srSoundnessError₁ srSoundnessError₂ : ENNReal}
    (hSound : soundness init impl langIn langOut verifier srSoundnessError₁)
    (hle : srSoundnessError₁ ≤ srSoundnessError₂) :
    soundness init impl langIn langOut verifier srSoundnessError₂ := by
  intro srProver
  exact le_trans (hSound srProver) hle

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration soundness is monotone under enlarging the honest input language and shrinking
the accepting output language. -/
theorem soundness.mono_languages
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srSoundnessError : ENNReal}
    (hSound : soundness init impl langIn langOut verifier srSoundnessError)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut) :
    soundness init impl langIn' langOut' verifier srSoundnessError := by
  intro srProver
  refine le_trans ?_ (hSound srProver)
  exact prEvent_mono _ _ _ fun event hevent => by
    rcases event with ⟨stmtIn, stmtOut?⟩
    cases stmtOut? with
    | none => exact False.elim hevent
    | some stmtOut =>
        exact ⟨hOut hevent.1, fun hmem => hevent.2 (hIn hmem)⟩

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration soundness can simultaneously transport languages and relax the target
soundness error. -/
theorem soundness.mono_languages_error
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srSoundnessError₁ srSoundnessError₂ : ENNReal}
    (hSound : soundness init impl langIn langOut verifier srSoundnessError₁)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut)
    (hle : srSoundnessError₁ ≤ srSoundnessError₂) :
    soundness init impl langIn' langOut' verifier srSoundnessError₂ := by
  intro srProver
  refine le_trans ?_ (le_trans (hSound srProver) hle)
  exact prEvent_mono _ _ _ fun event hevent => by
    rcases event with ⟨stmtIn, stmtOut?⟩
    cases stmtOut? with
    | none => exact False.elim hevent
    | some stmtOut =>
        exact ⟨hOut hevent.1, fun hmem => hevent.2 (hIn hmem)⟩

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration knowledge soundness is monotone in the allowed knowledge-soundness error. -/
theorem knowledgeSoundness.mono_error
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srKnowledgeSoundnessError₁ srKnowledgeSoundnessError₂ : ENNReal}
    (hSound : knowledgeSoundness init impl relIn relOut verifier srKnowledgeSoundnessError₁)
    (hle : srKnowledgeSoundnessError₁ ≤ srKnowledgeSoundnessError₂) :
    knowledgeSoundness init impl relIn relOut verifier srKnowledgeSoundnessError₂ := by
  obtain ⟨srExtractor, hSound⟩ := hSound
  exact ⟨srExtractor, fun srProver => le_trans (hSound srProver) hle⟩

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration knowledge soundness is monotone under enlarging the valid input relation and
shrinking the valid output relation. -/
theorem knowledgeSoundness.mono_relations
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srKnowledgeSoundnessError : ENNReal}
    (hSound : knowledgeSoundness init impl relIn relOut verifier srKnowledgeSoundnessError)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut) :
    knowledgeSoundness init impl relIn' relOut' verifier srKnowledgeSoundnessError := by
  obtain ⟨srExtractor, hSound⟩ := hSound
  refine ⟨srExtractor, fun srProver => ?_⟩
  refine le_trans ?_ (hSound srProver)
  exact prEvent_mono _ _ _ fun event hevent => by
    rcases event with ⟨stmtIn, extractedWitIn?, stmtOut?, witOut⟩
    cases stmtOut? with
    | none => exact False.elim hevent
    | some stmtOut =>
        exact ⟨fun witIn hmem hValid => hevent.1 witIn hmem (hIn hValid),
          hOut hevent.2⟩

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration knowledge soundness can simultaneously transport relations and relax the
target knowledge-soundness error. -/
theorem knowledgeSoundness.mono_relations_error
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srKnowledgeSoundnessError₁ srKnowledgeSoundnessError₂ : ENNReal}
    (hSound : knowledgeSoundness init impl relIn relOut verifier srKnowledgeSoundnessError₁)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut)
    (hle : srKnowledgeSoundnessError₁ ≤ srKnowledgeSoundnessError₂) :
    knowledgeSoundness init impl relIn' relOut' verifier srKnowledgeSoundnessError₂ := by
  obtain ⟨srExtractor, hSound⟩ := hSound
  refine ⟨srExtractor, fun srProver => ?_⟩
  refine le_trans ?_ (le_trans (hSound srProver) hle)
  exact prEvent_mono _ _ _ fun event hevent => by
    rcases event with ⟨stmtIn, extractedWitIn?, stmtOut?, witOut⟩
    cases stmtOut? with
    | none => exact False.elim hevent
    | some stmtOut =>
        exact ⟨fun witIn hmem hValid => hevent.1 witIn hmem (hIn hValid),
          hOut hevent.2⟩

#print axioms soundness.mono_error
#print axioms soundness.mono_languages
#print axioms soundness.mono_languages_error
#print axioms knowledgeSoundness.mono_error
#print axioms knowledgeSoundness.mono_relations
#print axioms knowledgeSoundness.mono_relations_error

end StateRestoration

end Verifier

namespace OracleVerifier



end OracleVerifier

end
