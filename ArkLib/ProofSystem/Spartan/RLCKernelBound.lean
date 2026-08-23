/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ShortPhaseRbrKnowledgeLeaves
import ArkLib.ToMathlib.LinearFormKernelCard

/-!
# The tight `1/|R|` rbr-KS leaf for Spartan's `linearCombination` round (issue #329)

The in-tree leaf `linearCombination_rbrKnowledgeSoundness_leaf` carries per-round error `1`, and
this is proven-forced for the claim-blind relation chain `relE → relF`: a prover that sends the
*true* evaluation claims makes the RLC target equal the second sum-check cube sum for every
challenge, so `relF` cannot see the first sum-check's doom.  Issue #329's target-carrying program
re-divides the labor so that the `linearCombination` round is accountable for exactly one thing:
**catching wrong evaluation claims**.  This module proves that leaf at its exact error.

* `sendEvalClaimClaimsCorrectRel`: the claims-correctness relation at the `sendEvalClaim`
  endpoint — the bundled claim oracle stores exactly the honest `evalClaimValue`s.
* `mem_prependRLCTargetRbrRelF_iff_rlc`: membership in the *unchanged* pinned downstream relation
  `relF` is precisely the scalar RLC identity
  `∑ idx, c idx * v idx = ∑ idx, c idx * evalClaimValue idx` (via the cube-sum identity
  `secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue`, which is linear in `c`).
* `linearCombination_flip_prob_eq`: for a doomed statement (some claim wrong, deviation
  `d := v - evalClaimValue ≠ 0`), the false-to-true flip probability over a uniform RLC challenge
  is **exactly** `1/|R|` — the affine level-set density of a nonzero linear form on
  `R1CS.MatrixIdx → R` (`LinearFormKernel.probEvent_linearForm_eq_inv_card_of_ne_zero`).
* `linearCombination_rbrKnowledgeSoundness_claimBound`: the leaf — rbr knowledge soundness from
  `sendEvalClaimClaimsCorrectRel` to the **unchanged** `prependRLCTargetRbrRelF` at per-round
  error `(Fintype.card R)⁻¹`.

Because `relF` is unchanged, every downstream seam (`prependRLCTarget`, `secondSumcheck`,
`finalCheck`) composes exactly as in the proven chain.  Structural invariants that must ride
along the round (the carried first-sum-check target `t'`, the `e₁`-consistency predicate of
scope item 3) are pass-through statement predicates, so they conjoin onto this leaf at unchanged
error via `Verifier.rbrKnowledgeSoundness_conjoin`.  This replaces the `err₅ = 1` slot with the
bound Spartan itself assigns to this round (eprint 2019/550, Lemma 5.1) — here proven as an
equality, not just `≤`.
-/

open MvPolynomial OracleComp ProtocolSpec Sumcheck
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The claims-correctness relation at the `sendEvalClaim` endpoint: the bundled evaluation-claim
oracle stores exactly the honest evaluation values `evalClaimValue` determined by the first
sum-check challenge point and the matrix/witness oracles.  This is the input relation on which
the `linearCombination` round is quantitatively accountable: a statement outside it has a nonzero
claim deviation, which survives the RLC challenge with probability exactly `1/|R|`. -/
@[reducible]
def sendEvalClaimClaimsCorrectRel :
    Set ((Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit) :=
  { x | ∀ idx, x.1.2 (.inl 0) idx
      = evalClaimValue R pp x.1.1 (fun i => x.1.2 (.inr i)) idx }

/-- Membership in the pinned downstream relation `relF` is exactly the scalar RLC identity
between the stored claims and the honest evaluation values.  This is the cube-sum identity
`secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue` (the second sum-check's initial
cube sum is *linear* in the RLC challenge), threaded through the sum-check domain bridge. -/
theorem mem_prependRLCTargetRbrRelF_iff_rlc
    (c : LinearCombinationChallenge R) (stmt : Statement.AfterSendEvalClaim R pp)
    (oStmt : ∀ i, OracleStatement.AfterSendEvalClaim R pp i) :
    ((((c, stmt), oStmt), ()) ∈ prependRLCTargetRbrRelF (R := R) pp oSpec)
      ↔ ∑ idx, c idx * oStmt (.inl 0) idx
          = ∑ idx, c idx * evalClaimValue R pp stmt (fun i => oStmt (.inr i)) idx := by
  simp only [prependRLCTargetRbrRelF, Spartan.Spec.secondSumcheckRbrRelIn,
    Extractor.Lens.Honest.pullbackRelIn, Set.mem_setOf_eq, Sumcheck.Spec.relationRound,
    Spartan.Spec.secondSumcheckOracleLens, Spartan.Spec.secondSumcheckStmtLens,
    Statement.Lens.proj]
  have hsum : (∑ x ∈ (Finset.univ.map (boolEmbedding R)) ^ᶠ (pp.ℓ_n - 0),
      (secondSumCheckVirtualPolynomial R pp (c, stmt) oStmt)
        ⸨(Fin.elim0 : Fin 0 → R), x⸩)
      = ∑ idx, c idx * evalClaimValue R pp stmt (fun i => oStmt (.inr i)) idx := by
    rw [Spartan.sum_boolDomain_eq_sum_boolFn,
      ← secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue R pp (c, stmt) oStmt]
    refine Finset.sum_congr rfl fun Y _ => ?_
    apply congrArg
      (fun pt => MvPolynomial.eval pt (secondSumCheckVirtualPolynomial R pp (c, stmt) oStmt))
    funext j
    simp only [Function.comp_apply, Fin.append, Fin.addCases, Fin.cast, eq_rec_constant,
      Fin.castLT, Fin.subNat]
    rfl
  constructor
  · intro h
    exact h.symm.trans hsum
  · intro h
    exact hsum.trans h.symm

/-- **The exact flip probability of the `linearCombination` round.**  If some stored claim
deviates from its honest value, then a uniformly sampled RLC challenge lands the output in the
pinned downstream relation `relF` with probability **exactly** `1/|R|`: the surviving challenges
form one affine level set of the nonzero linear form `c ↦ ∑ idx, c idx * (v - evalClaimValue) idx`
on `R1CS.MatrixIdx → R`. -/
theorem linearCombination_flip_prob_eq
    (stmt : Statement.AfterSendEvalClaim R pp)
    (oStmt : ∀ i, OracleStatement.AfterSendEvalClaim R pp i)
    (hbad : ¬ ∀ idx, oStmt (.inl 0) idx
      = evalClaimValue R pp stmt (fun i => oStmt (.inr i)) idx) :
    Pr[fun c : LinearCombinationChallenge R =>
        ((((c, stmt), oStmt), ()) ∈ prependRLCTargetRbrRelF (R := R) pp oSpec)
      | $ᵗ (LinearCombinationChallenge R)]
      = ((Fintype.card R : ENNReal))⁻¹ := by
  classical
  have hiff : ∀ c : LinearCombinationChallenge R,
      ((((c, stmt), oStmt), ()) ∈ prependRLCTargetRbrRelF (R := R) pp oSpec)
        ↔ ∑ idx, c idx * (oStmt (.inl 0) idx
            - evalClaimValue R pp stmt (fun i => oStmt (.inr i)) idx) = 0 := by
    intro c
    rw [mem_prependRLCTargetRbrRelF_iff_rlc pp oSpec c stmt oStmt, ← sub_eq_zero,
      ← Finset.sum_sub_distrib]
    constructor
    · intro h
      rw [← h]
      exact Finset.sum_congr rfl fun idx _ => mul_sub _ _ _
    · intro h
      rw [← h]
      exact Finset.sum_congr rfl fun idx _ => (mul_sub _ _ _).symm
  rw [probEvent_ext (q := fun c : LinearCombinationChallenge R =>
      ∑ idx, c idx * (oStmt (.inl 0) idx
        - evalClaimValue R pp stmt (fun i => oStmt (.inr i)) idx) = 0)
    (fun c _ => hiff c)]
  have hd : (fun idx => oStmt (.inl 0) idx
      - evalClaimValue R pp stmt (fun i => oStmt (.inr i)) idx) ≠ 0 := by
    intro h0
    refine hbad fun idx => ?_
    have := congrFun h0 idx
    simpa [sub_eq_zero] using this
  exact LinearFormKernel.probEvent_linearForm_eq_inv_card_of_ne_zero hd 0

/-- **The tight `linearCombination` rbr-KS leaf (issue #329).**  The `linearCombination` phase is
rbr knowledge-sound from the claims-correctness relation to the **unchanged** pinned downstream
relation `relF`, with per-round error `1/|R|` — the bound Spartan itself assigns to this round
(eprint 2019/550, Lemma 5.1), here at the exact level-set density.  Structural invariants
(the carried first-sum-check target, the `e₁`-consistency predicate) are pass-through statement
predicates and conjoin onto this leaf at unchanged error via
`Verifier.rbrKnowledgeSoundness_conjoin`. -/
theorem linearCombination_rbrKnowledgeSoundness_claimBound :
    (oracleReduction.linearCombination R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (sendEvalClaimClaimsCorrectRel (R := R) pp)
      (prependRLCTargetRbrRelF (R := R) pp oSpec)
      (fun _ => ((Fintype.card R : ℝ≥0))⁻¹) := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [linearCombination_toVerifier_closed]
  refine Verifier.rbrKnowledgeSoundness_singleChallenge_pure
    (C := LinearCombinationChallenge R)
    init impl
    (fun (p : Statement.AfterSendEvalClaim R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i) c => ((c, p.1), p.2))
    (sendEvalClaimClaimsCorrectRel (R := R) pp)
    (prependRLCTargetRbrRelF (R := R) pp oSpec) _ ?_
  rintro ⟨stmt, oStmt⟩ hbad
  have hbad' : ¬ ∀ idx, oStmt (.inl 0) idx
      = evalClaimValue R pp stmt (fun i => oStmt (.inr i)) idx := by
    intro h
    exact hbad (by simpa [sendEvalClaimClaimsCorrectRel] using h)
  refine le_of_eq ?_
  rw [linearCombination_flip_prob_eq pp oSpec stmt oStmt hbad']
  rw [← ENNReal.coe_natCast, ← ENNReal.coe_inv (by exact_mod_cast Fintype.card_pos.ne')]

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.mem_prependRLCTargetRbrRelF_iff_rlc
#print axioms Spartan.Spec.Bricks.linearCombination_flip_prob_eq
#print axioms Spartan.Spec.Bricks.linearCombination_rbrKnowledgeSoundness_claimBound
