/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
import ArkLib.OracleReduction.LiftContext.Coherence
import ArkLib.OracleReduction.SimOracleFoldlM

/-!
# `LiftContextCoherent` for the single-round Simple sum-check lens (`hPerRound`'s `coh`, issue #13)

`Sumcheck.Spec.SingleRound.perRound_of` (`SingleRoundBridge.lean`, the `G-perRound` keystone)
reduces the whole multi-round `oracleReduction.toReduction = reduction` bridge to two named per-round
residuals: the simple-level base bridge `hSimpleBridge`, and the per-round **routing coherence**

  `coh : ∀ i, OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
                (Simple.oracleReduction R deg D oSpec).verifier`.                              (★)

**This file discharges the structural part of `(★)` and isolates its one genuinely-deep residual.**
We build the per-round `LiftContextCoherent` instance via the generic framework builder
`liftContextCoherent_of` (`Coherence.lean`), mirroring the proven LogUp instance
`Logup.logupSumcheck_liftContextCoherent` (`SumcheckLiftCoherent.lean`) and the Spartan
`Spartan.Spec.firstChallenge_liftContextCoherent` (`FirstChallengeCoherent.lean`).

`liftContextCoherent_of` assembles three obligations:

* `hproj` — the non-oracle projection: `(sumcheckOracleLens.toLens.proj (os, oos)).1` is the round
  `target`, which is `sumcheckOracleLens.projStmt os = os.target`, so `rfl`;
* `hlift` — the output-side routing: the single output oracle is the unchanged input oracle
  (`sumcheckOracleLens.embedOStmt = Function.Embedding.inl`, `hEqOStmt = rfl`), matching the inner
  `Simple.oracleVerifier`'s `embed = .inl`, so `Prod.ext rfl …` collapses by `rfl`;
* `hfaith` — the genuinely hard per-inner-query **faithfulness**: under the honest outer oracles, the
  lens' virtual-oracle reconstruction `sumcheckOracleLens.simOStmt ⟨(), pt⟩` (a `|D|^(n-1)`-fold
  `foldlM` of evaluation queries to the *outer* multivariate polynomial at `sumPoint`) simulates to
  the honest *inner* round-polynomial oracle answer `(roundPoly).eval pt`.

## What is structural (proven here, unconditionally)

`simulateQ_simOracle_query_sumcheck` — a single honest outer-oracle evaluation query simulates to the
genuine point evaluation `(oos ()).1.eval pt` (`simulateQ_spec_query`).

`simOStmt_run_simOracle` — the whole `simOStmt ⟨(), pt⟩` reconstruction, run at the outer input
statement and simulated under the honest outer oracle, collapses to the deterministic `pure` of the
fold value `∑ y ∈ (univ.map D)^ᶠ(n-1), (oos ()).1.eval (sumPoint i pt os y)`. Proven via the generic
fold-collapse brick `simulateQ_simOracle_foldlM` (each step is deterministic under the honest
oracle).

## The one genuinely-deep residual (named hypothesis)

The remaining content — that this `|D|^(n-1)`-fold summation of the outer multivariate polynomial
equals the round univariate polynomial evaluated at `pt` (i.e. the `oStmtLens.toFunA` round-poly
shape) — is the sum-check round-polynomial identity. It is carried as the explicit named hypothesis

* `hRoundFaithful` — the fold value equals `((sumcheckOracleLens.toLens.proj (os, oos)).2 ()).1.eval
  pt`.

This is the direct analogue of LogUp's `logupSumcheckPolynomial_finalEval` and Spartan's
`zeroCheckEval_simOracle` closed-form identities. No `sorry`/`admit`. The main definition
`simpleRound_liftContextCoherent` is the per-round `LiftContextCoherent` instance **conditional on
exactly that one named residual**, and `coh_of` packages the `∀ i`-form consumed by
`SingleRound.perRound_of`.
-/

open OracleComp OracleSpec OracleInterface ProtocolSpec Finset
open OracleVerifier.LiftContext

set_option linter.unusedSectionVars false

namespace Sumcheck.Spec.SingleRound

noncomputable section

variable {R : Type} [CommSemiring R] {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [DecidableEq R] [SampleableType R]

/-- A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`. -/
private theorem foldl_add_eq_sum {S : Type} [AddCommMonoid S] {β : Type} (g : β → S) :
    ∀ (l : List β) (acc : S),
      l.foldl (fun a y => a + g y) acc = acc + (l.map g).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons y ys ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]; abel

/-- **Atomic single-query reduction.** Simulating one honest outer multivariate-oracle evaluation
query (at a full `Fin n → R` point) under the single-family honest oracle returns the genuine point
evaluation `(oos ()).1.eval pt`. Proven via `simulateQ_spec_query`. -/
theorem simulateQ_simOracle_query_sumcheck
    (oos : ∀ i, OracleStatement R n deg i) (pt : Fin n → R) :
    simulateQ (simOracle oSpec oos)
        (OracleComp.lift (OracleSpec.query
            (show [OracleStatement R n deg]ₒ.Domain from ⟨(), pt⟩)) :
          OracleComp (oSpec + [OracleStatement R n deg]ₒ) R)
      = pure ((oos ()).1.eval pt) := by
  erw [simulateQ_spec_query]
  rfl

/-- **`simOStmt` reconstruction collapses deterministically.** Under the honest outer oracles, the
lens' virtual-oracle reconstruction `sumcheckOracleLens.simOStmt ⟨(), pt⟩`, run at the outer input
statement `os` and simulated under the honest outer oracle, equals the `pure` of the
`|D|^(n-1)`-fold summation of the outer multivariate polynomial at `sumPoint`. The genuine evaluation
is deterministic, so no probabilistic content remains. -/
theorem simOStmt_run_simOracle (i : Fin n)
    (os : StatementRound R n i.castSucc) (oos : ∀ i, OracleStatement R n deg i) (pt : R) :
    simulateQ (simOracle oSpec oos)
        (((sumcheckOracleLens R n deg D oSpec i).simOStmt
          (show [Simple.OStmtIn R deg]ₒ.Domain from ⟨(), pt⟩)).run os)
      = pure ((((univ.map D) ^ᶠ (n - 1 - i)).toList).foldl
          (fun (acc : R) y => acc + (oos ()).1.eval (sumPoint R n i pt os y))
          (0 : R)) := by
  have hstep : ∀ (acc : R) (y : Fin (n - 1 - i) → R),
      simulateQ (simOracle oSpec oos)
          (do
            let resp ← (OracleComp.lift <| OracleSpec.query
              (spec := [OracleStatement R n deg]ₒ)
              (show [OracleStatement R n deg]ₒ.Domain from ⟨(), sumPoint R n i pt os y⟩) :
              OracleComp (oSpec + [OracleStatement R n deg]ₒ) R)
            pure (acc + resp))
        = pure (acc + (oos ()).1.eval (sumPoint R n i pt os y)) := by
    intro acc y
    rw [simulateQ_bind, simulateQ_simOracle_query_sumcheck, pure_bind, simulateQ_pure]
  show simulateQ (simOracle oSpec oos)
      ((((univ.map D) ^ᶠ (n - 1 - i)).toList).foldlM
        (fun (acc : R) y =>
          (do
            let resp ← (OracleComp.lift <| OracleSpec.query
              (spec := [OracleStatement R n deg]ₒ)
              (show [OracleStatement R n deg]ₒ.Domain from ⟨(), sumPoint R n i pt os y⟩) :
              OracleComp (oSpec + [OracleStatement R n deg]ₒ) R)
            pure (acc + resp)))
        (0 : R))
    = _
  rw [simulateQ_simOracle_foldlM oos _
    (fun (acc : R) y => acc + (oos ()).1.eval (sumPoint R n i pt os y)) _ _ hstep]

/-- **`LiftContextCoherent` for the single-round Simple sum-check lens (issue #13, design note
#433).** The virtual-oracle reconstruction `sumcheckOracleLens.simOStmt` is coherent with the inner
`Simple.oracleVerifier`'s honest oracle answers, so the proven generic single-round `Sumcheck.Spec`
`toReduction = reduction` bridge transfers through `oracleReduction = (Simple.oracleReduction).liftContext`.

* `hproj` — the non-oracle projection is the round `target`, so `rfl`;
* `hfaith` — strip the prover-message summand (`simulateQ_simOracle2_liftComp`), collapse the
  reconstruction (`simOStmt_run_simOracle`), then apply the named round-polynomial faithfulness
  `hRoundFaithful`;
* `hlift` — the single output oracle is the unchanged input oracle, so `rfl`.

The one genuinely-deep residual `hRoundFaithful` — that the `|D|^(n-1)`-fold summation of the outer
multivariate polynomial equals the round univariate polynomial evaluated at `pt` — is carried as the
explicit named hypothesis (no `sorry`). -/
@[reducible] def simpleRound_liftContextCoherent (i : Fin n)
    (hRoundFaithful : ∀ (os : StatementRound R n i.castSucc)
        (oos : ∀ i, OracleStatement R n deg i) (pt : R),
      (((univ.map D) ^ᶠ (n - 1 - i)).toList).foldl
          (fun (acc : R) y => acc + (oos ()).1.eval (sumPoint R n i pt os y)) (0 : R)
        = OracleInterface.answer
            (((sumcheckOracleLens R n deg D oSpec i).toLens.proj (os, oos)).2 ()) pt) :
    OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier :=
  liftContextCoherent_of (sumcheckOracleLens R n deg D oSpec i)
    (Simple.oracleReduction R deg D oSpec).verifier
    -- hproj: the non-oracle projection is the round `target`
    (fun _ _ => rfl)
    -- hfaith: strip the message summand, collapse the reconstruction, apply round faithfulness
    (fun os oos transcript q => by
      obtain ⟨⟨⟩, pt⟩ := q
      rw [simulateQ_simOracle2_liftComp, simOStmt_run_simOracle]
      show pure _ = simOracle2 oSpec ((sumcheckOracleLens R n deg D oSpec i).toLens.proj (os, oos)).2
        transcript.messages (Sum.inr (Sum.inl ⟨(), pt⟩))
      rw [hRoundFaithful os oos pt]
      rfl)
    -- hlift: the output-side routing matches definitionally
    (fun _ _ _ _ => rfl)

/-- **The `∀ i`-form `coh`, modulo the one named residual.**

This is the shape consumed by `Sumcheck.Spec.SingleRound.perRound_of` (`SingleRoundBridge.lean`).
The structural plumbing is fully discharged; the input is exactly the per-round round-polynomial
faithfulness `hRoundFaithful`. -/
@[reducible] def coh_of
    (hRoundFaithful : ∀ (i : Fin n) (os : StatementRound R n i.castSucc)
        (oos : ∀ i, OracleStatement R n deg i) (pt : R),
      (((univ.map D) ^ᶠ (n - 1 - i)).toList).foldl
          (fun (acc : R) y => acc + (oos ()).1.eval (sumPoint R n i pt os y)) (0 : R)
        = OracleInterface.answer
            (((sumcheckOracleLens R n deg D oSpec i).toLens.proj (os, oos)).2 ()) pt) :
    ∀ i, OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier :=
  fun i => simpleRound_liftContextCoherent i (hRoundFaithful i)

end

end Sumcheck.Spec.SingleRound

#print axioms Sumcheck.Spec.SingleRound.simulateQ_simOracle_query_sumcheck
#print axioms Sumcheck.Spec.SingleRound.simOStmt_run_simOracle
#print axioms Sumcheck.Spec.SingleRound.simpleRound_liftContextCoherent
#print axioms Sumcheck.Spec.SingleRound.coh_of
