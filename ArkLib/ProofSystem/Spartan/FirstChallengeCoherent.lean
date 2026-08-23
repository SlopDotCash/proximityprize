/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckZeroEval
import ArkLib.OracleReduction.LiftContext.Coherence

/-!
# `LiftContextCoherent` for the Spartan `firstChallenge` lift (issue #114, design note #433)

The Spartan first sum-check is obtained by lifting the generic `RandomQuery` oracle reduction onto
the *virtual* zero-check polynomial `𝒢` via `firstChallengeOracleLens`. Transferring the proven
`RandomQuery` completeness through that `liftContext` requires the framework coherence side condition
`OracleVerifier.LiftContextCoherent` (design note #433): the lens' virtual-oracle reconstruction
`simOStmt` must, under the honest oracle, agree with the inner verifier's honest oracle answers.

`firstChallenge_liftContextCoherent` discharges that obligation. It is assembled from the generic
builder `liftContextCoherent_of`, whose three inputs are:

* `hproj` — the non-oracle projection is `Unit`, so trivially `rfl`;
* `hfaith` — the oracle-semantics core: `simulateQ_simOracle2_liftComp` strips the prover-message
  summand the lens never touches, reducing each inner query to the single-family honest oracle, and
  then for the `𝒢` oracle the keystone faithfulness `zeroCheckEval_simOracle` says the
  reconstruction equals `eval pt 𝒢`, while the zero oracle answers `eval pt 0 = 0`;
* `hlift` — the output-side routing of `firstChallengeOracleLens` (`embedOStmt = inl`, the output
  oracle family is the unchanged input family) matches the inner verifier's (`embed = inl`)
  definitionally, so `rfl`.

This is the first-phase analogue of the second sum-check's faithfulness core
(`secondSCEvalPure_simOracle0`); together they cover both `liftContext` coherences of the Spartan
PIOP first/second sum-checks.
-/

open OracleComp OracleSpec OracleInterface MvPolynomial OracleVerifier.LiftContext

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]
    (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι) [SampleableType R]

/-- **`LiftContextCoherent` for the Spartan `firstChallenge` lift.** The virtual-oracle
reconstruction `firstChallengeOracleLens.simOStmt` is coherent with the inner `RandomQuery`
verifier's honest oracle answers — the #433 framework obligation for transferring `RandomQuery`
completeness through the first sum-check `liftContext`. -/
@[reducible] noncomputable def firstChallenge_liftContextCoherent :
    OracleVerifier.LiftContextCoherent (firstChallengeOracleLens R pp oSpec)
      (RandomQuery.oracleReduction oSpec (MvPolynomial (Fin pp.ℓ_m) R)).verifier :=
  liftContextCoherent_of (firstChallengeOracleLens R pp oSpec)
    (RandomQuery.oracleReduction oSpec (MvPolynomial (Fin pp.ℓ_m) R)).verifier
    -- hproj: the non-oracle projection is `Unit`
    (fun _ _ => rfl)
    -- hfaith: strip the message summand, then the keystone faithfulness / zero-oracle answer
    (by
      intro os oos transcript q
      rw [simulateQ_simOracle2_liftComp]
      obtain ⟨j, pt⟩ := q
      fin_cases j
      · show simulateQ (simOracle oSpec oos) (zeroCheckEvalFromOracles R pp oSpec os pt) = _
        rw [zeroCheckEval_simOracle]
        rfl
      · show simulateQ (simOracle oSpec oos) (pure (0 : R)) = _
        rw [simulateQ_pure]
        show (pure (0 : R) : OracleComp oSpec R)
          = pure (MvPolynomial.eval pt (0 : MvPolynomial (Fin pp.ℓ_m) R))
        rw [map_zero])
    -- hlift: the output-side routing matches definitionally
    (by intro _ _ _ _; rfl)

end Spartan.Spec
