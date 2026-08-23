/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FriComplete
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-!
# FRI: Composed-Reduction Perfect Completeness (Brick C/D, issue #117)

This module assembles the per-round perfect-completeness facts for the FRI phases into perfect
completeness of the *composed* FRI reduction (`Fri.Spec.reduction`), using the proven
sequential-composition keystones.

The composed FRI reduction is
```
reduction      = OracleReduction.append reductionFold (QueryRound.queryOracleReduction …)
reductionFold  = OracleReduction.append (OracleReduction.seqCompose … foldOracleReduction)
                                        finalFoldOracleReduction
```

* **Brick C** (this file) is the binary `append`-composition step:
  `reduction_perfectCompleteness_of_phases` derives the composed reduction's perfect completeness
  from (i) perfect completeness of the folding phase (`reductionFold`) and (ii) of the query phase
  (`queryOracleReduction`). The seam between the two phases is the query round's leading `V_to_P`
  challenge, so the proof is the **proven** challenge-seam keystone
  `Reduction.append_perfectCompleteness_challenge`, transported to the oracle level by the
  **proven** verifier-fusion bridge `OracleReduction.appendToReductionResidual_proof`.
  The shared-oracle side conditions (`himplSP`/`himplNF`) are vacuous for `oSpec = []ₒ`
  (no shared oracles), so the only genuine extra hypothesis is `hInit : NeverFail init`
  (required by the keystone; completeness is false without it when `init` can fail).
  **No residual hypothesis remains in this composition step.**

* **Brick D** is the headline statement `reduction_perfectCompleteness`
  (`Fri/Spec/Completeness.lean`), packaging Brick C as the composed FRI reduction
  perfect-completeness theorem; the still-open content is exactly the per-phase facts
  (`foldPhase`/`queryRound` residuals), never the composition.
-/

namespace Fri

open OracleSpec OracleComp ProtocolSpec NNReal Domain
open scoped NNReal

namespace Spec

namespace Completeness

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ}
variable {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-! **Brick C — binary append composition of the FRI phases (fully proven).**

The composed FRI reduction `Fri.Spec.reduction` is `append reductionFold queryOracleReduction`.
Given:
* `hInit` : the ambient initialization never fails (standard keystone hypothesis);
* `hFold` : perfect completeness of the folding phase `reductionFold` (folding rounds + final round),
  from the chained input relation `relIn` to the intermediate relation `relMid`;
* `hQuery` : perfect completeness of the query phase `queryOracleReduction`, from `relMid` to
  `relOut` (note `QueryRound.{input,output}Relation` are *equal* — the query round preserves the
  final-fold relation — so `relMid = relOut` in the intended FRI instantiation);
* the `AppendCoherent` coherence for `reductionFold.verifier` (the standard composition side
  condition, synthesized from the per-round leaf coherence instances proven in
  `Fri/Spec/SingleRound.lean`);

the **proven** challenge-seam keystone `Reduction.append_perfectCompleteness_challenge` (the seam
round is the query round's leading `V_to_P` challenge), combined with the **proven** verifier-fusion
bridge `OracleReduction.appendToReductionResidual_proof`, yields perfect completeness of the
composed reduction. The `himplSP`/`himplNF` side conditions are vacuous since `oSpec = []ₒ` has an
empty query domain. -/
omit [SampleableType F] in
set_option maxHeartbeats 4000000 in
theorem reduction_perfectCompleteness_of_phases
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (l : ℕ)
    (hInit : NeverFail init)
    [hFoldChallenge : ∀ i, SampleableType
      ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i)]
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    {relMid relOut : Set ((FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
      Witness F s d (Fin.last (k + 1)))}
    {relIn : Set ((Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω (0 : Fin (k + 1)) j) ×
      Witness F s d (0 : Fin (k + 2)))}
    [OracleVerifier.Append.AppendCoherent (reductionFold k s d (ω := ω)).verifier]
    (hFold : OracleReduction.perfectCompleteness init impl relIn relMid
      (reductionFold k s d (ω := ω)))
    (hQuery : OracleReduction.perfectCompleteness init impl relMid relOut
      (QueryRound.queryOracleReduction.{0} (k := k) s d dom_size_cond l)) :
    letI : ∀ i, SampleableType
        (((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F) ++ₚ
          QueryRound.pSpec l (ω := ω)).Challenge i) :=
      @ProtocolSpec.instSampleableTypeChallengeAppend _ _ _ _ hFoldChallenge hQueryChallenge
    OracleReduction.perfectCompleteness init impl relIn relOut
      ((reductionFold k s d (ω := ω)).append
        (QueryRound.queryOracleReduction.{0} (k := k) s d dom_size_cond l)) := by
  haveI : (([]ₒ : OracleSpec PEmpty)).Inhabited := { inhabited_B := fun i => nomatch i }
  haveI : (([]ₒ : OracleSpec PEmpty)).Fintype := { fintype_B := fun i => nomatch i }
  -- The seam round (global index `m = |pSpecFold| + 2`, i.e. the first query-round message)
  -- is a `V_to_P` challenge.
  have hDirSeam : ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F)
        ++ₚ QueryRound.pSpec l (ω := ω)).dir
      (⟨Fin.vsum (fun _ : Fin k => 2) + 2, by omega⟩
        : Fin ((Fin.vsum (fun _ : Fin k => 2) + 2) + 1)) = .V_to_P := by
    have h0 : (⟨Fin.vsum (fun _ : Fin k => 2) + 2, by omega⟩
          : Fin ((Fin.vsum (fun _ : Fin k => 2) + 2) + 1))
        = Fin.natAdd (Fin.vsum (fun _ : Fin k => 2) + 2) ⟨0, by omega⟩ := by
      ext; simp
    rw [h0, Prover.append_dir_natAdd]
    rfl
  unfold OracleReduction.perfectCompleteness
  -- Verifier-fusion bridge: `toReduction` commutes with `append` (proven unconditionally).
  have hb : ((reductionFold k s d (ω := ω)).append
        (QueryRound.queryOracleReduction.{0} (k := k) s d dom_size_cond l)).toReduction
      = (reductionFold k s d (ω := ω)).toReduction.append
        (QueryRound.queryOracleReduction.{0} (k := k) s d dom_size_cond l).toReduction :=
    OracleReduction.appendToReductionResidual_proof (reductionFold k s d (ω := ω))
      (QueryRound.queryOracleReduction.{0} (k := k) s d dom_size_cond l)
  rw [hb]
  exact Reduction.append_perfectCompleteness_challenge
    (reductionFold k s d (ω := ω)).toReduction
    (QueryRound.queryOracleReduction.{0} (k := k) s d dom_size_cond l).toReduction
    hFold hQuery Nat.one_pos hDirSeam rfl
    (fun t => isEmptyElim t) (fun t => isEmptyElim t) hInit

#print axioms reduction_perfectCompleteness_of_phases

end Completeness

end Spec

end Fri
