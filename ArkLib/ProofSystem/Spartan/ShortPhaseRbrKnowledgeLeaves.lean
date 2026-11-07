/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ProximityPrize.Compatibility.SpartanSendEvalClaim
import ProximityPrize.Compatibility.SpartanLinearCombination
import ProximityPrize.Compatibility.SpartanFirstChallenge
import ProximityPrize.Compatibility.SumcheckKnowledge
import ArkLib.ProofSystem.Spartan.RbrKnowledgeWiring
import ArkLib.ProofSystem.Spartan.FirstSumcheckRelComplete
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

import ProximityPrize.Compatibility.PureKnowledge

/-!

Canonical-message integration: the degree-2/degree-3 round knowledge bounds remain explicit
hypotheses of the `_of_sumcheck_rounds` constructions below. Former unconditional zero-flip
completion claims are retired; exact names, commands and added obligations are recorded in
`scripts/integration/sumcheck-message-semantics-retirements.json`.

# Short-phase RBR knowledge-soundness leaves for the composed Spartan PIOP (#114)

This module proves the five non-sum-check phase bounds and assembles the in-tree Spartan
PIOP's end-to-end bound. The assembly retains explicit degree-two and degree-three knowledge
bounds for the actual canonical sum-check messages; it does not discharge those obligations.

The relation chain (`relB`/`relE`/`relF` were free in the wiring layer; here they are pinned):

* `relB := SendSingleWitness.toORelOut (spartanRelIn)` — R1CS satisfiability of the witness
  oracle sent in the first message;
* `relE := sendEvalClaimRbrRelE` — the first sum-check's transported output relation, read
  back through `sendEvalClaim`'s oracle pass-through;
* `relF := prependRLCTargetRbrRelF` — the pullback of the second sum-check's honest input
  relation along the deterministic RLC-target computation.

The five leaves:

* `h₁` (`firstMessage`): the in-tree `SendSingleWitness` perfect rbr-KS (error `0`);
* `h₂` (`firstChallenge`): **the Schwartz–Zippel leaf.** If the sent witness does not satisfy
  the R1CS instance, the zero-check polynomial `𝒢` is nonzero, so the sampled `τ` makes the
  projected round-`0` sum-check claim `∑_cube ℱ_τ = 0` (equivalently `𝒢(τ) = 0`) hold with
  probability at most `ℓ_m / |R|` (`MvPolynomial.schwartz_zippel_sum_degreeOf` with the
  per-variable degree bound `degreeOf j 𝒢 ≤ 1`). Error `ℓ_m / |R|`.
* `h₄` (`sendEvalClaim`): pure message-round transport (error `0`);
* `h₅` (`linearCombination`): **error `1` — honestly.** With the no-claim relation chain the
  doom of the first sum-check cannot propagate into `secondSumcheckRbrRelIn`: a prover that
  sends the *true* evaluation claims `(v_A, v_B, v_C)` makes the RLC target genuinely equal the
  second sum-check's cube sum for *every* challenge `r`, regardless of whether the first
  sum-check's terminal identity held. Since `relF` is forced (up to inclusion) to be the
  pullback of the pinned `secondSumcheckRbrRelIn` by the `prependRLCTarget` seam, the
  false-to-true flip probability at this round is unbounded, and the only honest per-round
  error is `1`. Binding the evaluation claims requires the target-carrying (`WithClaim`)
  protocol line, whose terminal semantic relation retains the cross-phase identity. Canonical
  `CheckClaim` itself passes statements through and does not execute a rejecting predicate;
  that relation-carrying line is tracked separately.
* `h₆` (`prependRLCTarget`): zero-round pullback transport (error `0`).

The three generic pure-verifier rbr-KS combinators (zero-round, single-message-round and
single-challenge-round) are shared by `ProximityPrize.Compatibility.PureKnowledge`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

/-! Generic pure-verifier combinators are imported from `Compatibility.PureKnowledge`. -/



/-! ## The Spartan short-phase leaves -/

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-! ### The pinned relation chain -/

/-- `relB`: R1CS satisfiability of the witness oracle sent in the first message. This is exactly
`SendSingleWitness.toORelOut (spartanRelIn R pp)`, the output relation of the in-tree
`SendSingleWitness` perfect rbr-KS leaf. -/
@[reducible]
def firstMessageRbrRelB :
    Set ((Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit) :=
  SendSingleWitness.toORelOut (spartanRelIn R pp)

/-- `relE`: the first sum-check's transported output relation, recovered through
`sendEvalClaim`'s statement/oracle pass-through (the scalar evaluation-claim family is
unconstrained). -/
@[reducible]
def sendEvalClaimRbrRelE :
    Set ((Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit) :=
  { x | ((x.1.1, fun j => x.1.2 (.inr j)), ()) ∈
      Spartan.Spec.firstSumcheckRbrRelOut (R := R) pp oSpec }

/-- `relF`: the pullback of the second sum-check's honest input relation along the deterministic
RLC-target computation performed by `prependRLCTarget`. -/
@[reducible]
def prependRLCTargetRbrRelF :
    Set ((Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit) :=
  { x | (((∑ idx, x.1.1.1 idx * (show R from x.1.2 (.inl idx)), x.1.1), x.1.2), ()) ∈
      Spartan.Spec.secondSumcheckRbrRelIn (R := R) pp oSpec }

/-! ### Closed-form compiled verifiers for the pure phases -/

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] in
/-- The compiled `firstChallenge` verifier, in closed form: it returns the sampled challenge
paired with the input statement and passes every oracle through. -/
theorem firstChallenge_toVerifier_closed :
    (oracleReduction.completedFirstChallenge R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure ((fun p (c : FirstChallenge R pp) => ((c, p.1), p.2)) p
          (tr.challenges ⟨0, rfl⟩))⟩ := by
  rw [OracleVerifier.toVerifier_eq_pure_of_collapse
    (oracleReduction.completedFirstChallenge R pp oSpec).verifier
    (fun p tr => (tr.challenges ⟨0, rfl⟩, p.1))
    (fun _ _ _ => by
      simp only [oracleReduction.completedFirstChallenge, firstChallengeVerifier]
      exact simulateQ_pure _ _)]
  rfl

/-- The closed-form output map of the compiled `sendEvalClaim` verifier: forward the statement,
route each scalar claim oracle from the bundled message, pass the remaining oracles through. -/
def sendEvalClaimRouteMap
    (p : Statement.AfterFirstSumcheck R pp × ∀ i, OracleStatement.AfterFirstSumcheck R pp i)
    (m : ∀ i, EvalClaim R i) :
    Statement.AfterSendEvalClaim R pp × ∀ i, OracleStatement.AfterSendEvalClaim R pp i :=
  (p.1, fun i => match i with
    | .inl idx => m idx
    | .inr j => p.2 j)

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] in
/-- The compiled `sendEvalClaim` verifier, in closed form: it forwards the statement, routes the
scalar claim family from the bundled message, and passes the remaining oracles through. -/
theorem sendEvalClaim_toVerifier_closed :
    (oracleReduction.completedSendEvalClaim R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (sendEvalClaimRouteMap (R := R) pp p (tr.messages ⟨0, rfl⟩))⟩ := by
  rw [OracleVerifier.toVerifier_eq_pure_of_collapse
    (oracleReduction.completedSendEvalClaim R pp oSpec).verifier (fun p _ => p.1)
    (fun _ _ _ => by
      simp only [oracleReduction.completedSendEvalClaim, sendEvalClaimVerifier]
      exact simulateQ_pure _ _)]
  congr 1

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] in
/-- The compiled `linearCombination` verifier, in closed form: it returns the sampled RLC
challenge paired with the input statement and passes every oracle through. -/
theorem linearCombination_toVerifier_closed :
    (oracleReduction.completedLinearCombination R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure ((fun p (c : LinearCombinationChallenge R) => ((c, p.1), p.2)) p
          (tr.challenges ⟨0, rfl⟩))⟩ := by
  rw [OracleVerifier.toVerifier_eq_pure_of_collapse
    (oracleReduction.completedLinearCombination R pp oSpec).verifier
    (fun p tr => (tr.challenges ⟨0, rfl⟩, p.1))
    (fun _ _ _ => by
      simp only [oracleReduction.completedLinearCombination, linearCombinationVerifier]
      exact simulateQ_pure _ _)]
  rfl

/-! ### Leaf `h₁` — `firstMessage` (perfect, error `0`) -/

/-- **Leaf `h₁`.** The `firstMessage` (`SendSingleWitness`) phase is perfectly rbr
knowledge-sound from `spartanRelIn` to `relB`. -/
theorem firstMessage_rbrKnowledgeSoundness_spartanRelIn :
    (oracleReduction.firstMessage R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) (firstMessageRbrRelB (R := R) pp) 0 :=
  SendSingleWitness.oracleReduction_rbr_knowledge_soundness (oSpec := oSpec)
    (init := init) (impl := impl) (oRelIn := spartanRelIn R pp)

/-! ### Leaf `h₂` — `firstChallenge` (Schwartz–Zippel, error `ℓ_m / |R|`) -/

omit [Fintype R] [Inhabited R] [SampleableType R] in
/-- Every variable degree of the zero-check polynomial `𝒢` is at most `1` (it is a sum of
`eqPolynomial · C` products). -/
theorem zeroCheckVirtualPolynomial_degreeOf_le
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) (j : Fin pp.ℓ_m) :
    (zeroCheckVirtualPolynomial R pp 𝕩 oStmt).degreeOf j ≤ 1 := by
  classical
  unfold zeroCheckVirtualPolynomial
  refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) ?_
  rw [Finset.sup_le_iff]
  intro x _
  refine le_trans (MvPolynomial.degreeOf_mul_le _ _ _) ?_
  have h1 := MvPolynomial.eqPolynomial_degreeOf
    (R := R) (finFunctionFinEquiv.symm x : Fin pp.ℓ_m → R) j
  have h2 := MvPolynomial.degreeOf_C (σ := Fin pp.ℓ_m)
    ((Matrix.mulVec (oStmt (.inl .A)) (R1CS.𝕫 𝕩 (oStmt (.inr 0)))) x *
      (Matrix.mulVec (oStmt (.inl .B)) (R1CS.𝕫 𝕩 (oStmt (.inr 0)))) x -
      (Matrix.mulVec (oStmt (.inl .C)) (R1CS.𝕫 𝕩 (oStmt (.inr 0)))) x) j
  omega

omit [Inhabited R] in
/-- **The Schwartz–Zippel flip bound.** If the sent witness does not satisfy the R1CS instance,
then the zero-check polynomial `𝒢` is nonzero and a uniformly sampled `τ` is a zero of `𝒢` with
probability at most `ℓ_m / |R|`. -/
theorem zeroCheck_flip_prob_le (hm : 0 < pp.ℓ_m)
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (hbad : ¬ R1CS.relation R pp.toSizeR1CS 𝕩 (fun idx => oStmt (.inl idx)) (oStmt (.inr 0))) :
    probEvent (fun τ : FirstChallenge R pp =>
        MvPolynomial.eval τ (zeroCheckVirtualPolynomial R pp 𝕩 oStmt) = 0) ($ᵗ (FirstChallenge R pp))
      ≤ (((pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0) : ℝ≥0) : ENNReal) := by
  classical
  -- `𝒢 ≠ 0`: it fails to vanish at some Boolean point.
  have hG : zeroCheckVirtualPolynomial R pp 𝕩 oStmt ≠ 0 := by
    intro h0
    exact hbad ((relation_iff_zeroCheck_vanishes R pp 𝕩 oStmt).mpr
      (fun w => by rw [h0]; exact map_zero _))
  set q : ℕ := Fintype.card R with hq
  have hq0 : 0 < q := Fintype.card_pos
  set Z : Finset (Fin pp.ℓ_m → R) :=
    Finset.univ.filter
      (fun τ => MvPolynomial.eval τ (zeroCheckVirtualPolynomial R pp 𝕩 oStmt) = 0) with hZ
  -- Schwartz–Zippel over `S i = univ`, with per-variable degree `≤ 1`: the natural-number
  -- zero-set bound `#Z ≤ ℓ_m * q ^ (ℓ_m - 1)`.
  have hcard : (Z.card : ℚ≥0) ≤ (pp.ℓ_m : ℚ≥0) * (q : ℚ≥0) ^ (pp.ℓ_m - 1) := by
    have hSZ := MvPolynomial.schwartz_zippel_sum_degreeOf hG
      (fun _ : Fin pp.ℓ_m => (Finset.univ : Finset R))
    have hdom :
        ({x ∈ Fintype.piFinset (fun _ : Fin pp.ℓ_m => (Finset.univ : Finset R)) |
            MvPolynomial.eval x (zeroCheckVirtualPolynomial R pp 𝕩 oStmt) = 0} : Finset _)
          = Z := by
      rw [Fintype.piFinset_univ]
    rw [hdom] at hSZ
    have hprod : (∏ _i : Fin pp.ℓ_m, ((Finset.univ : Finset R).card : ℚ≥0))
        = (q : ℚ≥0) ^ pp.ℓ_m := by
      simp [Finset.card_univ, hq]
    rw [hprod] at hSZ
    have hRHS : (∑ i : Fin pp.ℓ_m,
        ((zeroCheckVirtualPolynomial R pp 𝕩 oStmt).degreeOf i /
          ((Finset.univ : Finset R).card : ℚ≥0))) ≤ (pp.ℓ_m : ℚ≥0) / (q : ℚ≥0) := by
      calc (∑ i : Fin pp.ℓ_m,
            ((zeroCheckVirtualPolynomial R pp 𝕩 oStmt).degreeOf i /
              ((Finset.univ : Finset R).card : ℚ≥0)))
          ≤ ∑ _i : Fin pp.ℓ_m, (1 : ℚ≥0) / (q : ℚ≥0) := by
            refine Finset.sum_le_sum fun i _ => ?_
            simp only [Finset.card_univ, ← hq]
            gcongr
            exact_mod_cast zeroCheckVirtualPolynomial_degreeOf_le pp 𝕩 oStmt i
        _ = (pp.ℓ_m : ℚ≥0) / (q : ℚ≥0) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              mul_one_div]
    have hZQ : (Z.card : ℚ≥0) ≤ ((pp.ℓ_m : ℚ≥0) / (q : ℚ≥0)) * (q : ℚ≥0) ^ pp.ℓ_m := by
      have hqpow : (0 : ℚ≥0) < (q : ℚ≥0) ^ pp.ℓ_m := by positivity
      calc (Z.card : ℚ≥0) = ((Z.card : ℚ≥0) / (q : ℚ≥0) ^ pp.ℓ_m) * (q : ℚ≥0) ^ pp.ℓ_m := by
            rw [div_mul_cancel₀]
            exact ne_of_gt hqpow
        _ ≤ ((pp.ℓ_m : ℚ≥0) / (q : ℚ≥0)) * (q : ℚ≥0) ^ pp.ℓ_m :=
            mul_le_mul_of_nonneg_right (le_trans hSZ hRHS) (by positivity)
    calc (Z.card : ℚ≥0) ≤ ((pp.ℓ_m : ℚ≥0) / (q : ℚ≥0)) * (q : ℚ≥0) ^ pp.ℓ_m := hZQ
      _ = (pp.ℓ_m : ℚ≥0) * (q : ℚ≥0) ^ (pp.ℓ_m - 1) := by
          rw [div_mul_eq_mul_div, mul_comm ((pp.ℓ_m : ℚ≥0)) _, mul_comm ((pp.ℓ_m : ℚ≥0)) _]
          rw [← pow_sub_one_mul hm.ne' ((q : ℚ≥0))]
          rw [mul_comm ((q : ℚ≥0) ^ (pp.ℓ_m - 1)) _, mul_assoc, mul_comm ((q : ℚ≥0)) _,
            mul_div_assoc, div_self (by exact_mod_cast hq0.ne'), mul_one,
            mul_comm]
  have hcardN : Z.card ≤ pp.ℓ_m * q ^ (pp.ℓ_m - 1) := by exact_mod_cast hcard
  -- Transfer to the probability.
  simp only [probEvent]
  rw [SampleableType.prEvent_uniformSample]
  rw [← hZ]
  have hcardC : (Fintype.card (FirstChallenge R pp)) = q ^ pp.ℓ_m := by
    simp [FirstChallenge, hq]
  rw [hcardC]
  have hpow : q ^ pp.ℓ_m = q ^ (pp.ℓ_m - 1) * q := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  have hstep : ((Z.card : ENNReal) / ((q ^ pp.ℓ_m : ℕ) : ENNReal))
      ≤ (((pp.ℓ_m * q ^ (pp.ℓ_m - 1) : ℕ) : ENNReal)) / ((q ^ pp.ℓ_m : ℕ) : ENNReal) := by
    gcongr
  refine le_trans hstep (le_of_eq ?_)
  rw [hpow, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  rw [mul_comm ((pp.ℓ_m : ENNReal)) _]
  rw [ENNReal.mul_div_mul_left _ _
    (by exact_mod_cast (Nat.pow_pos hq0 (n := pp.ℓ_m - 1)).ne')
    (by exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top q))]
  rw [ENNReal.coe_div (by exact_mod_cast hq0.ne')]
  simp

omit [Inhabited R] in
/-- The projected round-`0` sum-check claim of `firstChallenge`'s output is exactly the
vanishing of the zero-check polynomial `𝒢` at the sampled `τ`. -/
theorem mem_firstSumcheckRbrRelIn_iff_zeroCheckEval
    (τ : Fin pp.ℓ_m → R) (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) :
    (((((τ, 𝕩) : Statement.AfterFirstChallenge R pp), oStmt), ()) ∈
        Spartan.Spec.firstSumcheckRbrRelIn (R := R) pp oSpec)
      ↔ MvPolynomial.eval τ (zeroCheckVirtualPolynomial R pp 𝕩 oStmt) = 0 := by
  simp only [Spartan.Spec.firstSumcheckRbrRelIn, Extractor.Lens.Honest.pullbackRelIn,
    Set.mem_ofPred_eq, Sumcheck.Spec.relationRound]
  have hsum : (∑ x ∈ (Finset.univ.map (boolEmbedding R)) ^ᶠ (pp.ℓ_m - 0),
      (firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt) ⸨(Fin.elim0 : Fin 0 → R), x⸩)
      = MvPolynomial.eval τ (zeroCheckVirtualPolynomial R pp 𝕩 oStmt) := by
    rw [Spartan.sum_boolDomain_eq_sum_boolFn,
      ← firstSumCheckVirtualPolynomial_hypercubeSum_eq_zeroCheckEval pp τ 𝕩 oStmt]
    refine Finset.sum_congr rfl fun Y _ => ?_
    apply congrArg (fun pt => MvPolynomial.eval pt (firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt))
    funext j
    simp only [Function.comp_apply, Fin.append, Fin.addCases, Fin.cast,
      eq_rec_constant, Fin.castLT, Fin.subNat]
    rfl
  exact ⟨fun h => hsum.symm.trans h, fun h => hsum.trans h⟩

omit [Inhabited R] in
/-- **Leaf `h₂` (the Schwartz–Zippel leaf).** The `firstChallenge` phase is rbr knowledge-sound
from `relB` (R1CS satisfiability of the sent witness) to the first sum-check's honest input
relation, with per-round error `ℓ_m / |R|`. -/
theorem firstChallenge_rbrKnowledgeSoundness_schwartzZippel (hm : 0 < pp.ℓ_m) :
    (oracleReduction.completedFirstChallenge R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstMessageRbrRelB (R := R) pp)
      (Spartan.Spec.firstSumcheckRbrRelIn (R := R) pp oSpec)
      (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0)) := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [firstChallenge_toVerifier_closed]
  refine Verifier.rbrKnowledgeSoundness_singleChallenge_pure (C := FirstChallenge R pp)
    init impl
    (fun (p : Statement.AfterFirstMessage R pp ×
        ∀ i, OracleStatement.AfterFirstMessage R pp i) c => ((c, p.1), p.2))
    (firstMessageRbrRelB (R := R) pp)
    (Spartan.Spec.firstSumcheckRbrRelIn (R := R) pp oSpec) _ ?_
  rintro ⟨𝕩, oStmt⟩ hbad
  have hbad' : ¬ R1CS.relation R pp.toSizeR1CS 𝕩
      (fun idx => oStmt (.inl idx)) (oStmt (.inr 0)) := by
    intro h
    exact hbad h
  refine le_trans (prEvent_mono_of_support _ _ _ ?_) (zeroCheck_flip_prob_le pp hm 𝕩 oStmt hbad')
  intro τ _ hτ
  exact (mem_firstSumcheckRbrRelIn_iff_zeroCheckEval pp oSpec τ 𝕩 oStmt).mp hτ

/-! ### Leaf `h₄` — `sendEvalClaim` (pure transport, error `0`) -/

/-- **Leaf `h₄`.** The `sendEvalClaim` phase is perfectly rbr knowledge-sound from the first
sum-check's transported output relation to its pass-through reading `relE`: the statement and
the matrix/witness oracles are forwarded unchanged, so input membership is recovered from any
output in `relE` regardless of the adversarial claim message. -/
theorem sendEvalClaim_rbrKnowledgeSoundness_leaf :
    (oracleReduction.completedSendEvalClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (Spartan.Spec.firstSumcheckRbrRelOut (R := R) pp oSpec)
      (sendEvalClaimRbrRelE (R := R) pp oSpec) 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [sendEvalClaim_toVerifier_closed]
  exact Verifier.rbrKnowledgeSoundness_singleMessage_pure init impl _
    (fun stmtIn msg h => h)

/-! ### Leaf `h₅` — `linearCombination` (error `1`; see the module docstring) -/

/-- **Leaf `h₅`.** The `linearCombination` phase is rbr knowledge-sound from `relE` to `relF`
with per-round error `1`. The error is genuinely `1` for this relation chain: see the module
docstring — a prover sending the true evaluation claims defeats any smaller bound, because
`relF` (forced to be the pullback of the pinned `secondSumcheckRbrRelIn`) cannot see the first
sum-check's doom. The trivial bound keeps the composed theorem honest rather than laundering an
unprovable per-round error. -/
theorem linearCombination_rbrKnowledgeSoundness_leaf :
    (oracleReduction.completedLinearCombination R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (sendEvalClaimRbrRelE (R := R) pp oSpec)
      (prependRLCTargetRbrRelF (R := R) pp oSpec)
      (fun _ => 1) := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [linearCombination_toVerifier_closed]
  refine Verifier.rbrKnowledgeSoundness_singleChallenge_pure
    (C := LinearCombinationChallenge R)
    init impl
    (fun (p : Statement.AfterSendEvalClaim R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i) c => ((c, p.1), p.2))
    (sendEvalClaimRbrRelE (R := R) pp oSpec)
    (prependRLCTargetRbrRelF (R := R) pp oSpec) _ ?_
  intro stmtIn _
  exact le_trans (prEvent_le_one _) (by simp)

/-! ### Leaf `h₆` — `prependRLCTarget` (zero-round pullback, error `0`) -/

/-- **Leaf `h₆`.** The zero-round `prependRLCTarget` adapter is perfectly rbr knowledge-sound
from the pullback relation `relF` to the second sum-check's honest input relation. -/
theorem prependRLCTarget_rbrKnowledgeSoundness_pullbackLeaf :
    (prependRLCTarget (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (prependRLCTargetRbrRelF (R := R) pp oSpec)
      (Spartan.Spec.secondSumcheckRbrRelIn (R := R) pp oSpec) 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [prependRLCTarget_toVerifier_pure]
  exact Verifier.rbrKnowledgeSoundness_zeroRound_pure init impl _
    (fun stmtIn h => h)

/-! ### The composed theorem with explicit round bounds -/

/-- The completed Spartan composition construction, conditional on the actual canonical
sumcheck degree-2, degree-3 per-round knowledge bounds. The former unconditional zero-flip
completion is retired; exact source and the added obligations are recorded in the migration audit. -/
theorem composedRbrKnowledgeSoundnessPreserving_of_sumcheck_rounds [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : prFail (init) = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hRound2 : Sumcheck.Spec.RoundKnowledge R 2 (boolEmbedding R) pp.ℓ_n oSpec init impl)
    (hRound3 : Sumcheck.Spec.RoundKnowledge R 3 (boolEmbedding R) pp.ℓ_m oSpec init impl)
    :
    (composedPIOP_Rc (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) (Spartan.Spec.secondSumcheckRbrRelOut (R := R) pp oSpec)
      (composedRbrError pp
        (0 : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0))
        (fun _ => (3 : ℝ≥0) / (Fintype.card R))
        (0 : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => 1)
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)
        (fun _ => (2 : ℝ≥0) / (Fintype.card R))
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)) :=
  composedRbrKnowledgeSoundnessPreserving_of_nonsumcheck_leaves_of_sumcheck_rounds (hRound2 :=
    hRound2) (hRound3 := hRound3) pp oSpec hm hn
    (firstMessage_rbrKnowledgeSoundness_spartanRelIn pp oSpec)
    (firstChallenge_rbrKnowledgeSoundness_schwartzZippel pp oSpec hm)
    (sendEvalClaim_rbrKnowledgeSoundness_leaf pp oSpec)
    (linearCombination_rbrKnowledgeSoundness_leaf pp oSpec)
    (prependRLCTarget_rbrKnowledgeSoundness_pullbackLeaf pp oSpec)
    hInit hInitNF hNE_B hNE_C hNE_E hNE_F hNE_G

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.rbrKnowledgeSoundness_zeroRound_pure
#print axioms Verifier.rbrKnowledgeSoundness_singleMessage_pure
#print axioms Verifier.rbrKnowledgeSoundness_singleChallenge_pure
#print axioms Spartan.Spec.Bricks.firstMessage_rbrKnowledgeSoundness_spartanRelIn
#print axioms Spartan.Spec.Bricks.firstChallenge_rbrKnowledgeSoundness_schwartzZippel
#print axioms Spartan.Spec.Bricks.sendEvalClaim_rbrKnowledgeSoundness_leaf
#print axioms Spartan.Spec.Bricks.linearCombination_rbrKnowledgeSoundness_leaf
#print axioms Spartan.Spec.Bricks.prependRLCTarget_rbrKnowledgeSoundness_pullbackLeaf
#print axioms Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessPreserving_of_sumcheck_rounds
