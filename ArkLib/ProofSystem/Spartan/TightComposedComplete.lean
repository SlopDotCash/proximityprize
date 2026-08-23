/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedCompletenessFinal
import ArkLib.ProofSystem.Spartan.TightComposedFull
import ArkLib.ProofSystem.Spartan.TightMidCompleteness
import ArkLib.ProofSystem.Spartan.TightSecondCompleteness
import ArkLib.ProofSystem.Spartan.FinalCheckTightComplete

/-!
# Perfect completeness of the full tight composed Spartan chain (issue #329, B7 step 5)

The completeness mirror of `composedTightFull_rbrKnowledgeSoundness`
(`TightComposedFull.lean`): the eight-phase tight composition `composedPIOPTightFull_Rc` is
**perfectly complete** from the honest Spartan input relation `spartanRelIn` to the tight final
relation `tightFinalRelOut` (both terminal identities, quantifier-free). Together with the KS
apex, this closes #329's acceptance criteria in both directions.

## The honest tight relation chain (the B7 spec)

* `relA = spartanRelIn` — R1CS satisfiability with the witness in the witness slot;
* `relB = firstMessageRelOut` — R1CS satisfiability with the witness moved into the appended
  oracle slot (`SendSingleWitness` pushforward);
* `relC = firstSumcheckWithTargetRelIn` — R1CS satisfiability after the τ-challenge
  (definitionally `firstSumcheckRelInBF`; the carried chain shares the input relation);
* `relD = firstSumcheckWithTargetRelOutEnriched` — R1CS pass-through **∧ the direct first
  terminal identity `e₁ = eval r_x F̂`** (`TightFirstCompleteness.lean`);
* `relE = tightSendEvalClaimRelOut` — `relD` read back through the claim-oracle split, **∧ the
  bundled-claim honesty `.inl 0 = evalClaimValue` ∧ the first-terminal binding identity**
  (`TightMidCompleteness.lean`);
* `relF = tightLinearCombinationRelOut` — the challenge-stripped pushforward of `relE` (the RLC
  round records the sampled challenge, honest data unchanged);
* `relG = tightRelG = secondSumcheckWithTargetRbrRelIn ∩ bindingAtSecondIn` — the prepended
  target is the *true* RLC `T = ∑ r·v^true` ∧ binding (the honest adapter emits `∑ r·v^sent`,
  and the carried honesty conjunct turns sent into true; seam set-equality
  `tightRelG_eq_conjoined_relIn`, `TightSeamBridge.lean`);
* `relH = secondSumcheckWithTargetRelOutEnriched ∩ bindingAtSecondOut` — **the direct second
  terminal identity `e₂ = eval r_y ℳ`** ∧ the binding, transported through the carried second
  sum-check (`TightSecondCompleteness.lean` + the binding pass-through strengthening proved
  here via `Reduction.perfectCompleteness_strengthen_support`);
* `relI = tightFinalRelOut` — conjunct-for-conjunct the same as `relH` (the zero-round tight
  terminal check forwards the pair unchanged, `FinalCheckTightComplete.lean`).

## Structure

Mirrors the seven-seam fold of `composedPIOP_Rc_perfectCompleteness_of_leaves`
(`ComposedCompleteness.lean`) at the carried reductions: the protocol specs are *identical*
(carried statements change no round structure), so the three append-completeness keystones
(message / challenge / empty) apply at the same seam directions; the private direction facts
are mirrored here once more (as in `TightComposedFull.lean`).

Main results:
* `secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` — the `h₇` leaf: the enriched
  carried-second completeness conjoined with the binding pass-through;
* `composedPIOPTightFull_perfectCompleteness_of_leaves` — the relation-generic fold;
* `composedTightFull_perfectCompleteness` — **the apex**: unconditional perfect completeness
  from `spartanRelIn` to `tightFinalRelOut`, with only the standard honest-implementation side
  conditions.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 512
set_option linter.unusedSectionVars false

open Sumcheck.Spec.SingleRound (appendChalFintype appendChalInhab chalBaseFintypeP
  chalBaseFintypeV chalBaseFintypeE chalBaseInhabP chalBaseInhabV chalBaseInhabE)

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] [VCVCompatible R] (pp : PublicParams)

/-- Universe-pinned local alias of the carried RLC-target adapter (mirror of the KS-side
`prependRLCTargetWTKS`). -/
private abbrev prependRLCTargetWTC {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction.{0, 0} oSpec
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  prependRLCTargetWithTarget pp oSpec

private instance {ι : Type} (oSpec : OracleSpec ι) :
    OracleVerifier.Append.AppendCoherent (prependRLCTargetWTC (R := R) pp oSpec).verifier :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent
    (prependRLCTargetWithTargetVerifier (R := R) pp oSpec))

/-- Universe-pinned local alias of the tight terminal check. -/
private abbrev finalCheckTightC {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction.{0, 0} oSpec
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  finalCheckTight pp oSpec

/-! ### Direction facts (private mirrors, pSpec-identical to the original chain) -/

private theorem vsum_two_posC {ℓ : ℕ} (h : 0 < ℓ) : 0 < Fin.vsum (fun _ : Fin ℓ => 2) := by
  rcases ℓ with - | k
  · omega
  · rw [Fin.vsum_succ]; omega

private theorem sumcheckPSpec_dir_zeroC (deg n : ℕ)
    (h : 0 < Fin.vsum (fun _ : Fin n => 2)) :
    (Sumcheck.Spec.pSpec R deg n).dir ⟨0, h⟩ = .P_to_V := by
  rcases ProtocolSpec.seqCompose_appendValid
      (pSpec := fun _ : Fin n => Sumcheck.Spec.SingleRound.pSpec R deg)
      (fun _ => ⟨by norm_num, rfl⟩) with hzero | ⟨h', hdir⟩
  · omega
  · exact hdir

private theorem sfx6_dir_zeroC (hn : 0 < pp.ℓ_n)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) :
    (sfx6 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_posC hn
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zeroC 2 pp.ℓ_n hv

private theorem sfx5_dir_zeroC (hn : 0 < pp.ℓ_n)
    (h : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) :
    (sfx5 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have h6 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0 := by
    have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_posC hn
    omega
  rw [show (⟨0, h⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))
      = Fin.natAdd 0 (⟨0, h6⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx6_dir_zeroC pp hn h6

private theorem sfx4_dir_zeroC
    (h : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

private theorem sfx4_dir_seamC (hn : 0 < pp.ℓ_n)
    (h : 1 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h5 : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.natAdd 1 (⟨0, h5⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx5_dir_zeroC pp hn h5

private theorem sfx3_dir_zeroC
    (h : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  rw [show (⟨0, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

private theorem sfx3_dir_seamC
    (h : 1 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h4 : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.natAdd 1 (⟨0, h4⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx4_dir_zeroC pp h4

private theorem sfx2_dir_zeroC (hm : 0 < pp.ℓ_m)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) :
    (sfx2 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) := vsum_two_posC hm
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zeroC 3 pp.ℓ_m hv

private theorem sfx2_dir_seamC
    (h : Fin.vsum (fun _ : Fin pp.ℓ_m => 2) < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) :
    (sfx2 (R := R) pp).dir ⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ = .P_to_V := by
  have h3 : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) := by omega
  rw [show (⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))
      = Fin.natAdd (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))
          (⟨0, h3⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx3_dir_zeroC pp h3

private theorem sfx1_dir_zeroC
    (h : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

private theorem sfx1_dir_seamC (hm : 0 < pp.ℓ_m)
    (h : 1 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h2 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.natAdd 1 (⟨0, h2⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx2_dir_zeroC pp hm h2

private theorem composedPSpec_dir_seamC
    (h : 1 < 1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))) :
    (composedPSpec (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h1 : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))))
      = Fin.natAdd 1 (⟨0, h1⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx1_dir_zeroC pp h1

/-! ### The seam-adapted completeness leaves -/

section Leaves

variable {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Leaf `h₂` at the tight chain's endpoints**: the `firstChallenge` phase is perfectly
complete from `firstMessageRelOut` into `firstSumcheckWithTargetRelIn`. The carried chain shares
the input relation of the first sum-check with the target-dropping one (identical `setOf`
bodies, `firstSumcheckRelInBF = firstSumcheckWithTargetRelIn`), so this is the proven
`firstChallenge_perfectCompleteness_consumer` re-pointed across the definitional seam. -/
theorem firstChallenge_perfectCompleteness_consumerTight [oSpec.Fintype] [oSpec.Inhabited] :
    (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl
      (firstMessageRelOut (R := R) pp) (firstSumcheckWithTargetRelIn (R := R) pp) := by
  have h := firstChallenge_perfectCompleteness_consumer (R := R) pp oSpec
    (init := init) (impl := impl)
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness at h ⊢
  exact Reduction.completeness_relOut_mono init impl
    (fun x hx => hx :
      firstSumcheckRelInBF (R := R) pp ⊆ firstSumcheckWithTargetRelIn (R := R) pp) h

set_option linter.unusedFintypeInType false in
/-- **Leaf `h₇` (tight chain): the binding strengthening of the carried second sum-check
completeness.** The enriched completeness (`secondSumcheckWithTarget_perfectCompleteness_enriched`,
pinning `e₂ = eval r_y ℳ`) conjoined with the first-terminal binding identity as a pass-through
invariant, at the same honest hypotheses — the completeness mirror of the conjoined rbr-KS leaf
`secondSumcheckWithTarget_conjoined_rbrKnowledgeSoundness`.

The pass-through fact holds on the *whole run support*
(`Reduction.perfectCompleteness_strengthen_support`): the lifted verifier is
failing-deterministic with verdict `(v? (proj s) tr).map (lift s)`
(`sumcheckFull_toVerifier_isFailingDet` + `Verifier.liftContext_failingDet`), and the lift
forwards the passenger statement and the oracles untouched, so `bindingAtSecondIn` rides
through to `bindingAtSecondOut`. -/
theorem secondSumcheckWithTarget_perfectCompleteness_enrichedBinding
    [oSpec.Fintype] [oSpec.Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl
      ((secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
        ∩ {x | x.1 ∈ bindingAtSecondIn (R := R) pp})
      ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp}) := by
  have h := secondSumcheckWithTarget_perfectCompleteness_enriched (R := R) pp oSpec
    (init := init) (impl := impl) hInit hImplSupp
  unfold OracleReduction.perfectCompleteness at h ⊢
  refine Reduction.perfectCompleteness_strengthen_support h Set.inter_subset_left ?_
  rintro stmtIn witIn ⟨_, hBind⟩ ⟨⟨td, prv⟩, vOut⟩ hsupp hRel _
  refine ⟨hRel, ?_⟩
  -- Run-support decomposition: the verifier output is in the verifier's own run support.
  have hv : some vOut ∈ support (OptionT.run
      ((secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier.toVerifier.run
        stmtIn td)) :=
    Reduction.mem_support_verifier_run_of_mem_support_run _ stmtIn witIn hsupp
  -- Failing-determinism: the lifted verifier's verdict is `(v? (proj s) tr).map (lift s)`.
  obtain ⟨v?, hvdet⟩ := sumcheckFull_toVerifier_isFailingDet
    (R := R) (oSpec := oSpec) 2 (boolEmbedding R) pp.ℓ_n
  have hcomm := (secondSumcheckCoherentWithTarget (R := R) pp oSpec).toVerifier_comm
  have hVeq : (secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun s tr => OptionT.mk (pure ((v?
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj s) tr).map
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.lift s)))⟩ := by
    refine hcomm.trans ?_
    exact Verifier.liftContext_failingDet
      (secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens _ v? hvdet
  rw [hVeq] at hv
  simp only [Verifier.run, OptionT.run_mk, support_pure, Set.mem_singleton_iff] at hv
  -- Extract the inner output and the lift shape; the lift forwards the passenger data.
  rcases hverd : (v? ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj
      stmtIn) td) with _ | so
  · rw [hverd] at hv
    simp at hv
  · rw [hverd] at hv
    simp only [Option.map_some, Option.some.injEq] at hv
    obtain ⟨⟨T, stmt⟩, oStmt⟩ := stmtIn
    obtain ⟨⟨t', r_y⟩, innerO⟩ := so
    rw [hv]
    exact hBind

/-- **Leaf `h₈` at the tight chain's endpoints**: the tight terminal check carries the conjoined
`(e₂-direct ∧ binding)` relation into `tightFinalRelOut`. Instance of the pred-generic
pass-through completeness (`finalCheckTight_perfectCompleteness_any`) with the output relation
relaxed conjunct-for-conjunct. -/
theorem finalCheckTight_perfectCompleteness_tightOut :
    (finalCheckTightC pp oSpec).perfectCompleteness init impl
      ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
      (tightFinalRelOut (R := R) pp) := by
  have h := finalCheckTight_perfectCompleteness_any (R := R) pp oSpec
    (init := init) (impl := impl)
    ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
      ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
  unfold OracleReduction.perfectCompleteness at h ⊢
  exact Reduction.completeness_relOut_mono init impl
    (fun x hx => ⟨hx.1, hx.2⟩) h

end Leaves

/-! ### The seven-seam completeness fold at the carried reductions -/

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relA : Set ((Statement R pp × ∀ i, OracleStatement R pp i) × Witness R pp)}
  {relB : Set ((Statement.AfterFirstMessage R pp ×
    ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit)}
  {relC : Set ((Statement.AfterFirstChallenge R pp ×
    ∀ i, OracleStatement.AfterFirstChallenge R pp i) × Unit)}
  {relD : Set ((Statement.AfterFirstSumcheckWithTarget R pp ×
    ∀ i, OracleStatement.AfterFirstSumcheck R pp i) × Unit)}
  {relE : Set ((Statement.AfterSendEvalClaimWithTarget R pp ×
    ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit)}
  {relF : Set ((Statement.AfterLinearCombinationWithTarget R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relG : Set (((R × Statement.AfterLinearCombinationWithTarget R pp) ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relH : Set ((Statement.AfterSecondSumcheckWithTarget R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relI : Set ((Statement.AfterSecondSumcheckWithTarget R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}

/-- Seam 7 (`secondSumcheckWithTarget ▷ finalCheckTight`, empty trailing seam). -/
private theorem tightCStep8
    (h₇ : (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relG relH)
    (h₈ : (finalCheckTightC pp oSpec).perfectCompleteness init impl relH relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((secondSumcheckReductionWithTarget pp oSpec).append
      (finalCheckTightC pp oSpec)).perfectCompleteness init impl relG relI := by
  haveI : ∀ j, Fintype ((Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Challenge j) := sumcheckChalF 2 pp.ℓ_n
  haveI : ∀ j, Inhabited ((Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Challenge j) := sumcheckChalI 2 pp.ℓ_n
  haveI : ∀ j, Fintype ((sfx6 (R := R) pp).Challenge j) := c6F pp
  haveI : ∀ j, Inhabited ((sfx6 (R := R) pp).Challenge j) := c6I pp
  haveI := ProtocolSpec.challengeOracle_fintype (Sumcheck.Spec.pSpec R 2 pp.ℓ_n)
  haveI := ProtocolSpec.challengeOracle_inhabited (Sumcheck.Spec.pSpec R 2 pp.ℓ_n)
  haveI := ProtocolSpec.challengeOracle_fintype
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_n ++ₚ (!p[] : ProtocolSpec 0))
  haveI := ProtocolSpec.challengeOracle_inhabited
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_n ++ₚ (!p[] : ProtocolSpec 0))
  haveI := ProtocolSpec.challengeOracle_fintype (!p[] : ProtocolSpec 0)
  haveI := ProtocolSpec.challengeOracle_inhabited (!p[] : ProtocolSpec 0)
  exact OracleReduction.append_perfectCompleteness_keystone_empty_114
    (secondSumcheckReductionWithTarget pp oSpec) (finalCheckTightC pp oSpec) h₇ h₈
    hInit hImplSupp

/-- Seam 6 (`prependRLCTargetWithTarget ▷ …`, message seam through the 0-round left adapter). -/
private theorem tightCStep7 (hn : 0 < pp.ℓ_n)
    (h₆ : (prependRLCTargetWTC pp oSpec).perfectCompleteness init impl relF relG)
    (hRest : ((secondSumcheckReductionWithTarget pp oSpec).append
      (finalCheckTightC pp oSpec)).perfectCompleteness init impl relG relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((prependRLCTargetWTC pp oSpec).append ((secondSumcheckReductionWithTarget pp oSpec).append
      (finalCheckTightC pp oSpec))).perfectCompleteness init impl relF relI := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_posC hn
  haveI : ∀ j, Fintype ((sfx6 (R := R) pp).Challenge j) := c6F pp
  haveI : ∀ j, Inhabited ((sfx6 (R := R) pp).Challenge j) := c6I pp
  haveI : ∀ j, Fintype ((sfx5 (R := R) pp).Challenge j) := c5F pp
  haveI : ∀ j, Inhabited ((sfx5 (R := R) pp).Challenge j) := c5I pp
  haveI := ProtocolSpec.challengeOracle_fintype (sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype ((!p[] : ProtocolSpec 0) ++ₚ sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited ((!p[] : ProtocolSpec 0) ++ₚ sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype (!p[] : ProtocolSpec 0)
  haveI := ProtocolSpec.challengeOracle_inhabited (!p[] : ProtocolSpec 0)
  exact OracleReduction.append_perfectCompleteness_keystone
    (prependRLCTargetWTC pp oSpec)
    ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTightC pp oSpec))
    h₆ hRest (by omega) (sfx5_dir_zeroC pp hn (by omega)) (sfx6_dir_zeroC pp hn (by omega))
    hInit hImplSupp

/-- Seam 5 (`linearCombinationWithTarget ▷ …`, message seam: the right block opens with the
carried second sum-check's leading message through the 0-round adapter). -/
private theorem tightCStep6 (hn : 0 < pp.ℓ_n)
    (h₅ : (linearCombinationWithTarget pp oSpec).perfectCompleteness init impl relE relF)
    (hRest : ((prependRLCTargetWTC pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append
        (finalCheckTightC pp oSpec))).perfectCompleteness init impl relF relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTC pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append
        (finalCheckTightC pp oSpec)))).perfectCompleteness init impl relE relI := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_posC hn
  haveI : ∀ j, Fintype ((sfx5 (R := R) pp).Challenge j) := c5F pp
  haveI : ∀ j, Inhabited ((sfx5 (R := R) pp).Challenge j) := c5I pp
  haveI : ∀ j, Fintype ((sfx4 (R := R) pp).Challenge j) := c4F pp
  haveI : ∀ j, Inhabited ((sfx4 (R := R) pp).Challenge j) := c4I pp
  haveI : ∀ j, Fintype
      ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseFintypeV
  haveI : ∀ j, Inhabited
      ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseInhabV
  haveI := ProtocolSpec.challengeOracle_fintype (sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) ++ₚ sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited
    ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) ++ₚ sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1)
  haveI := ProtocolSpec.challengeOracle_inhabited
    (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1)
  exact OracleReduction.append_perfectCompleteness_keystone
    (linearCombinationWithTarget pp oSpec)
    ((prependRLCTargetWTC pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTightC pp oSpec)))
    h₅ hRest (by omega) (sfx4_dir_seamC pp hn (by omega)) (sfx5_dir_zeroC pp hn (by omega))
    hInit hImplSupp

/-- Seam 4 (`sendEvalClaimWithTarget ▷ …`, **challenge** seam: the right block opens with the
carried linear-combination `V_to_P` challenge). -/
private theorem tightCStep5
    (h₄ : (sendEvalClaimWithTarget pp oSpec).perfectCompleteness init impl relD relE)
    (hRest : ((linearCombinationWithTarget pp oSpec).append
      ((prependRLCTargetWTC pp oSpec).append ((secondSumcheckReductionWithTarget pp oSpec).append
        (finalCheckTightC pp oSpec)))).perfectCompleteness init impl relE relI)
    (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTC pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append
          (finalCheckTightC pp oSpec))))).perfectCompleteness init impl relD relI := by
  exact OracleReduction.append_perfectCompleteness_keystone_challenge_114
    (sendEvalClaimWithTarget pp oSpec)
    ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTC pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTightC pp oSpec))))
    h₄ hRest (by omega) (sfx3_dir_seamC pp (by omega)) (sfx4_dir_zeroC pp (by omega))
    hInit himplSP himplNF

/-- Seam 3 (`firstSumcheckWithTarget ▷ …`, message seam: the right block opens with the bundled
eval-claim `P_to_V` message). -/
private theorem tightCStep4
    (h₃ : (firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relC relD)
    (hRest : ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTC pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append
          (finalCheckTightC pp oSpec))))).perfectCompleteness init impl relD relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTC pp oSpec).append
          ((secondSumcheckReductionWithTarget pp oSpec).append
            (finalCheckTightC pp oSpec)))))).perfectCompleteness init impl relC relI := by
  haveI : ∀ j, Fintype ((Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Challenge j) := sumcheckChalF 3 pp.ℓ_m
  haveI : ∀ j, Inhabited ((Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Challenge j) := sumcheckChalI 3 pp.ℓ_m
  haveI : ∀ j, Fintype ((sfx3 (R := R) pp).Challenge j) := c3F pp
  haveI : ∀ j, Inhabited ((sfx3 (R := R) pp).Challenge j) := c3I pp
  haveI : ∀ j, Fintype ((sfx2 (R := R) pp).Challenge j) := c2F pp
  haveI : ∀ j, Inhabited ((sfx2 (R := R) pp).Challenge j) := c2I pp
  haveI := ProtocolSpec.challengeOracle_fintype (Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
  haveI := ProtocolSpec.challengeOracle_inhabited (Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
  haveI := ProtocolSpec.challengeOracle_fintype (sfx3 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx3 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    (Sumcheck.Spec.pSpec R 3 pp.ℓ_m ++ₚ sfx3 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited
    (Sumcheck.Spec.pSpec R 3 pp.ℓ_m ++ₚ sfx3 (R := R) pp)
  exact OracleReduction.append_perfectCompleteness_keystone
    (firstSumcheckReductionWithTarget pp oSpec)
    ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTC pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTightC pp oSpec)))))
    h₃ hRest (by omega) (sfx2_dir_seamC pp (by omega)) (sfx3_dir_zeroC pp (by omega))
    hInit hImplSupp

/-- Seam 2 (`firstChallenge ▷ …`, message seam: the right block opens with the carried first
sum-check's leading `P_to_V` polynomial message). -/
private theorem tightCStep3 (hm : 0 < pp.ℓ_m)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl relB relC)
    (hRest : ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTC pp oSpec).append
          ((secondSumcheckReductionWithTarget pp oSpec).append
            (finalCheckTightC pp oSpec)))))).perfectCompleteness init impl relC relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((oracleReduction.firstChallenge R pp oSpec).append
      ((firstSumcheckReductionWithTarget pp oSpec).append
        ((sendEvalClaimWithTarget pp oSpec).append
          ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTC pp oSpec).append
            ((secondSumcheckReductionWithTarget pp oSpec).append
              (finalCheckTightC pp oSpec))))))).perfectCompleteness init impl relB relI := by
  haveI : ∀ j, Fintype ((sfx2 (R := R) pp).Challenge j) := c2F pp
  haveI : ∀ j, Inhabited ((sfx2 (R := R) pp).Challenge j) := c2I pp
  haveI : ∀ j, Fintype ((sfx1 (R := R) pp).Challenge j) := c1F pp
  haveI : ∀ j, Inhabited ((sfx1 (R := R) pp).Challenge j) := c1I pp
  haveI : ∀ j, Fintype
      ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseFintypeV
  haveI : ∀ j, Inhabited
      ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseInhabV
  haveI := ProtocolSpec.challengeOracle_fintype (sfx2 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx2 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1)
  haveI := ProtocolSpec.challengeOracle_inhabited
    (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1)
  haveI := ProtocolSpec.challengeOracle_fintype
    ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) ++ₚ sfx2 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited
    ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) ++ₚ sfx2 (R := R) pp)
  exact OracleReduction.append_perfectCompleteness_keystone
    (oracleReduction.firstChallenge R pp oSpec)
    ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTC pp oSpec).append
          ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTightC pp oSpec))))))
    h₂ hRest (by omega) (sfx1_dir_seamC pp hm (by omega)) (sfx2_dir_zeroC pp hm (by omega))
    hInit hImplSupp

/-- **The relation-generic eight-phase tight completeness fold** (issue #329, B7 step 5).
Seam 1 (`firstMessage ▷ …`) is a **challenge** seam, closed by the challenge-seam keystone;
the other six seams are handled inside the `tightCStep*` lemmas (message / challenge / empty
keystones as dictated by each right block's opening direction — identical seam directions to
the target-dropping chain, since the protocol specs coincide). -/
theorem composedPIOPTightFull_perfectCompleteness_of_leaves
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (h₁ : (oracleReduction.firstMessage R pp oSpec).perfectCompleteness init impl relA relB)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl relB relC)
    (h₃ : (firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relC relD)
    (h₄ : (sendEvalClaimWithTarget pp oSpec).perfectCompleteness init impl relD relE)
    (h₅ : (linearCombinationWithTarget pp oSpec).perfectCompleteness init impl relE relF)
    (h₆ : (prependRLCTargetWTC pp oSpec).perfectCompleteness init impl relF relG)
    (h₇ : (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relG relH)
    (h₈ : (finalCheckTightC pp oSpec).perfectCompleteness init impl relH relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    (composedPIOPTightFull_Rc (R := R) pp oSpec).perfectCompleteness init impl relA relI := by
  have hS8 := tightCStep8 pp oSpec h₇ h₈ hInit hImplSupp
  have hS7 := tightCStep7 pp oSpec hn h₆ hS8 hInit hImplSupp
  have hS6 := tightCStep6 pp oSpec hn h₅ hS7 hInit hImplSupp
  have hS5 := tightCStep5 pp oSpec h₄ hS6 hInit himplSP himplNF
  have hS4 := tightCStep4 pp oSpec h₃ hS5 hInit hImplSupp
  have hS3 := tightCStep3 pp oSpec hm h₂ hS4 hInit hImplSupp
  exact OracleReduction.append_perfectCompleteness_keystone_challenge_114
    (oracleReduction.firstMessage R pp oSpec)
    ((oracleReduction.firstChallenge R pp oSpec).append
      ((firstSumcheckReductionWithTarget pp oSpec).append
        ((sendEvalClaimWithTarget pp oSpec).append
          ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTC pp oSpec).append
            ((secondSumcheckReductionWithTarget pp oSpec).append
              (finalCheckTightC pp oSpec)))))))
    h₁ hS3 (by omega) (composedPSpec_dir_seamC pp (by omega)) (sfx1_dir_zeroC pp (by omega))
    hInit himplSP himplNF

/-! ### THE APEX -/

/-- **THE TIGHT COMPOSED SPARTAN PERFECT COMPLETENESS (issue #329, B7 step 5).** The full
eight-phase tight composition `composedPIOPTightFull_Rc` is perfectly complete from the honest
Spartan input relation `spartanRelIn` to the tight final relation `tightFinalRelOut` (both
terminal identities, quantifier-free). Together with the KS apex
`composedTightFull_rbrKnowledgeSoundness` (`TightComposedFull.lean`), this closes #329's
acceptance criteria in both directions. Only the standard honest-implementation side
conditions remain as inputs (exactly those of `composedCompletenessStatement_proven`). -/
theorem composedTightFull_perfectCompleteness
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    (composedPIOPTightFull_Rc (R := R) pp oSpec).perfectCompleteness init impl
      (spartanRelIn R pp) (tightFinalRelOut (R := R) pp) :=
  composedPIOPTightFull_perfectCompleteness_of_leaves.{0, 0} pp oSpec hm hn
    (SendSingleWitness.oracleReduction_completeness (oSpec := oSpec)
      (Statement := Statement R pp) (OStatement := OracleStatement R pp)
      (Witness := Witness R pp) (init := init) (impl := impl)
      (oRelIn := spartanRelIn R pp) hInit)
    (firstChallenge_perfectCompleteness_consumerTight.{0} pp oSpec)
    (firstSumcheckWithTarget_perfectCompleteness_enriched pp oSpec hInit hImplSupp)
    (sendEvalClaimWithTarget_perfectCompleteness_tight pp oSpec)
    (linearCombinationWithTarget_perfectCompleteness_tight.{0} pp oSpec)
    (prependRLCTargetWithTarget_perfectCompleteness_tight pp oSpec)
    (secondSumcheckWithTarget_perfectCompleteness_enrichedBinding pp oSpec hInit hImplSupp)
    (finalCheckTight_perfectCompleteness_tightOut pp oSpec)
    hInit hImplSupp himplSP himplNF

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.firstChallenge_perfectCompleteness_consumerTight
#print axioms Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding
#print axioms Spartan.Spec.Bricks.finalCheckTight_perfectCompleteness_tightOut
#print axioms Spartan.Spec.Bricks.composedPIOPTightFull_perfectCompleteness_of_leaves
#print axioms Spartan.Spec.Bricks.composedTightFull_perfectCompleteness
