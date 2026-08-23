/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckCubeSum
import ArkLib.ProofSystem.Spartan.FirstChallengeCoherent
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.Sumcheck.Domain
import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
# The Spartan first sum-check oracle reduction (issue #114)

Constructs Spartan's **first sum-check** oracle reduction (phase 3), the analogue of
`secondSumcheckReduction`, by lifting the proven full sum-check oracle reduction
(`Sumcheck.Spec.oracleReduction`) onto the first sum-check virtual polynomial

  `ℱ(X) = eqPolynomial(τ)(X) · (Ã(X)·B̃(X) − C̃(X))`  (`firstSumCheckVirtualPolynomial`),

via `OracleReduction.liftContext`.

Two structural differences from the second sum-check:

* **Degree `3`, not `2`.** `ℱ` is `eq · (product of two multilinear factors)`, so it has degree
  `≤ 3` per variable (`firstSumCheckVirtualPolynomial_mem_restrictDegree`); the lift therefore uses
  `Sumcheck.Spec.oracleReduction R 3 …`.

* **Constant target `0`.** Unlike the second sum-check (whose target is the oracle-dependent random
  linear combination, hence carried in the statement), the first sum-check's target is the
  zero-check value `𝒢(τ)`, which the preceding `RandomQuery` (`firstChallenge`) phase pins to `0`.
  So `projStmt` produces the *constant* target `0`, and the outer input statement is the plain
  `Statement.AfterFirstChallenge` (no `R ×` target-carrying), matching `firstSumcheckResidual`.

Inner univariate evaluation queries to `ℱ` at a point `pt : Fin ℓ_m → R` are answered by the lens'
`simOStmt` reconstruction `firstSCEvalFromOracles`: for each matrix factor `M̃`, an outer
`x`-hypercube fold of inner `y`-hypercube folds reconstructs `eval pt M̃` from the matrix/witness
oracles (reusing the proven inner fold `matVecRowSum_simOracle`), and the three are combined with the
`eqPolynomial(τ)` weight. Faithfulness is `firstSCEvalFromOracles_simOracle`, and the
`LiftContextCoherent` gate is discharged by `firstSumcheckCoherent` (mirroring `secondSumcheckCoherent`).
-/

open MvPolynomial Matrix OracleComp OracleSpec OracleInterface OracleVerifier.LiftContext

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- A left fold accumulating `acc + g y` over a list equals `acc` plus the list sum of `g`. -/
private theorem foldl_add_eq_sum' {S : Type} [AddCommMonoid S] {β : Type} (g : β → S) :
    ∀ (l : List β) (acc : S), l.foldl (fun a y => a + g y) acc = acc + (l.map g).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons y ys ih => intro acc; simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [ih]; abel

/-- The verifier-side oracle reconstruction of `eval point M̃`, the multilinear-extension factor of
the first sum-check virtual polynomial. An outer `x`-hypercube fold weights each row `(M *ᵥ 𝕫)(x)`
(reconstructed by the inner `y`-hypercube fold `matVecSummandFromOracles`) by the equality kernel
`eq(point, x)`. -/
noncomputable def matVecMLEEvalFromOracles
    (𝕩 : Statement.AfterFirstMessage R pp) (point : Fin pp.ℓ_m → R) (idx : R1CS.MatrixIdx) :
    OracleComp (oSpec + [OracleStatement.AfterFirstMessage R pp]ₒ) R :=
  (Finset.univ : Finset (Fin (2 ^ pp.ℓ_m))).toList.foldlM
    (fun (acc : R) (xEnum : Fin (2 ^ pp.ℓ_m)) => do
      let coeff : R := MvPolynomial.eval point (MvPolynomial.eqPolynomial (boolPoint R xEnum))
      let rowVal ← (Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldlM
        (fun (a : R) (yEnum : Fin (2 ^ pp.ℓ_n)) => do
          let term ← matVecSummandFromOracles R pp oSpec 𝕩 idx (boolPoint R xEnum) yEnum
          pure (a + term)) (0 : R)
      pure (acc + coeff * rowVal))
    (0 : R)

omit [SampleableType R] in
/-- **`M̃`-factor faithfulness.** The honest simulation of `matVecMLEEvalFromOracles` equals
`eval point M̃` (`= eval point (matVecMLE …)`). The outer fold collapses to the `eqTilde`-weighted
hypercube sum that is exactly `MLE_eval_eq_sum_eqTilde` for `M *ᵥ 𝕫`. -/
theorem matVecMLEEvalFromOracles_simOracle
    (oos : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (𝕩 : Statement.AfterFirstMessage R pp) (point : Fin pp.ℓ_m → R) (idx : R1CS.MatrixIdx) :
    simulateQ (simOracle oSpec oos) (matVecMLEEvalFromOracles pp oSpec 𝕩 point idx)
      = pure (MvPolynomial.eval point (matVecMLE pp 𝕩 oos idx)) := by
  classical
  unfold matVecMLEEvalFromOracles
  rw [simulateQ_simOracle_foldlM oos _
    (fun (acc : R) (xEnum : Fin (2 ^ pp.ℓ_m)) =>
      acc + MvPolynomial.eval point (MvPolynomial.eqPolynomial (boolPoint R xEnum)) *
        (Matrix.mulVec (oos (.inl idx)) (R1CS.𝕫 𝕩 (oos (.inr 0)))) xEnum)]
  · -- collapse the outer fold to a `Finset.sum`, then identify it with `eval point M̃`
    congr 1
    rw [foldl_add_eq_sum', zero_add, Finset.sum_map_toList]
    rw [matVecMLE, MLE_eval_eq_sum_eqTilde, ← Equiv.sum_comp finFunctionFinEquiv]
    refine Finset.sum_congr rfl fun xBits _ => ?_
    have hb : boolPoint R (finFunctionFinEquiv xBits) = (fun i => ((xBits i : Fin 2) : R)) := by
      funext j; simp [boolPoint, Equiv.symm_apply_apply]
    rw [hb, eqTilde, eqPolynomial_symm, Function.comp_apply]
  · -- each outer step is deterministic: the inner fold reconstructs `(M *ᵥ 𝕫)(x)`
    intro acc xEnum
    simp only [simulateQ_bind, matVecRowSum_simOracle, pure_bind, simulateQ_pure]

/-- The verifier-side oracle reconstruction of `eval point ℱ` for the first sum-check virtual
polynomial: reconstruct each matrix factor `M̃(point)` via `matVecMLEEvalFromOracles` and combine
with the `eqPolynomial(τ)` weight. -/
noncomputable def firstSCEvalFromOracles
    (stmt : Statement.AfterFirstChallenge R pp) (point : Fin pp.ℓ_m → R) :
    OracleComp (oSpec + [OracleStatement.AfterFirstChallenge R pp]ₒ) R := do
  let a ← matVecMLEEvalFromOracles pp oSpec stmt.2 point .A
  let b ← matVecMLEEvalFromOracles pp oSpec stmt.2 point .B
  let c ← matVecMLEEvalFromOracles pp oSpec stmt.2 point .C
  pure (MvPolynomial.eval point (MvPolynomial.eqPolynomial stmt.1) * (a * b - c))

omit [SampleableType R] in
/-- **`simOStmt` faithfulness (single-family).** The honest simulation of `firstSCEvalFromOracles`
equals `eval point ℱ`. -/
theorem firstSCEvalFromOracles_simOracle
    (oos : ∀ i, OracleStatement.AfterFirstChallenge R pp i)
    (stmt : Statement.AfterFirstChallenge R pp) (point : Fin pp.ℓ_m → R) :
    simulateQ (simOracle oSpec oos) (firstSCEvalFromOracles pp oSpec stmt point)
      = pure (MvPolynomial.eval point (firstSumCheckVirtualPolynomial pp stmt.1 stmt.2 oos)) := by
  unfold firstSCEvalFromOracles
  simp only [simulateQ_bind, matVecMLEEvalFromOracles_simOracle, pure_bind, simulateQ_pure]
  refine congrArg pure ?_
  simp only [firstSumCheckVirtualPolynomial, map_mul, map_sub]

omit [SampleableType R] in
/-- **`hfaith` for the first sum-check lens.** The lens' reconstruction lifted into the verifier's
full oracle spec and simulated under the honest two-family oracle equals `eval point ℱ`. -/
theorem firstSCEvalFromOracles_simOracle2
    (oos : ∀ i, OracleStatement.AfterFirstChallenge R pp i)
    (msgs : ∀ i, (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Message i)
    (stmt : Statement.AfterFirstChallenge R pp) (point : Fin pp.ℓ_m → R) :
    simulateQ (OracleInterface.simOracle2 oSpec oos msgs)
        (OracleComp.liftComp (firstSCEvalFromOracles pp oSpec stmt point)
          (oSpec + ([OracleStatement.AfterFirstChallenge R pp]ₒ
            + [(Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Message]ₒ)))
      = pure (MvPolynomial.eval point (firstSumCheckVirtualPolynomial pp stmt.1 stmt.2 oos)) := by
  rw [simulateQ_simOracle2_liftComp]
  exact firstSCEvalFromOracles_simOracle pp oSpec oos stmt point

/-- The value-level oracle-statement lens for the first sum-check. Maps the outer `(τ, 𝕩)` context to
the inner sum-check oracle `⟨ℱ, deg ≤ 3⟩` with **constant target `0`**, and lifts the inner output
challenge `r_x` back into Spartan's `AfterFirstSumcheck` statement. -/
noncomputable def firstSumcheckStmtLens :
    OracleStatement.Lens
      (Statement.AfterFirstChallenge R pp) (Statement.AfterFirstSumcheck R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m (Fin.last pp.ℓ_m))
      (OracleStatement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstSumcheck R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3) (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3) where
  toFunA := fun ⟨⟨τ, 𝕩⟩, oStmt⟩ =>
    ⟨⟨0, Fin.elim0⟩,
     fun _ => ⟨firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt,
               firstSumCheckVirtualPolynomial_mem_restrictDegree pp τ 𝕩 oStmt⟩⟩
  toFunB := fun ⟨stmt, oStmt⟩ ⟨⟨_t', r_x⟩, _innerO⟩ => ⟨(r_x, stmt), oStmt⟩

/-- The oracle-routing lens for the first sum-check. -/
noncomputable def firstSumcheckOracleLens :
    OracleStatement.OracleLens oSpec
      (Statement.AfterFirstChallenge R pp) (Statement.AfterFirstSumcheck R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m (Fin.last pp.ℓ_m))
      (OracleStatement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstSumcheck R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3) (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3)
      (Sumcheck.Spec.pSpec R 3 pp.ℓ_m) where
  toLens := firstSumcheckStmtLens pp
  projStmt := fun _ => ⟨0, Fin.elim0⟩
  liftStmt := fun stmt ⟨_t', r_x⟩ => (r_x, stmt)
  simOStmt := fun q => match q with
    | ⟨_, point⟩ => ReaderT.mk fun stmt => firstSCEvalFromOracles pp oSpec stmt point
  embedOStmt := Function.Embedding.inl
  hEqOStmt := fun _ => rfl

/-- The value-level oracle context lens for the first sum-check. -/
noncomputable def firstSumcheckContextLens :
    OracleContext.Lens
      (Statement.AfterFirstChallenge R pp) (Statement.AfterFirstSumcheck R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m (Fin.last pp.ℓ_m))
      (OracleStatement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstSumcheck R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3) (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3)
      Unit Unit Unit Unit where
  stmt := firstSumcheckStmtLens pp
  wit := ⟨fun _ => (), fun _ _ => ()⟩

/-- **The Spartan first sum-check oracle reduction**, constructed by lifting the proven full
sum-check oracle reduction (degree `3`, Boolean domain) onto Spartan's virtual polynomial `ℱ(X)`
(issue #114). Discharges `firstSumcheckResidual` (with the corrected degree `3`). -/
noncomputable def firstSumcheckReduction :
    OracleReduction oSpec
      (Statement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstChallenge R pp) Unit
      (Statement.AfterFirstSumcheck R pp) (OracleStatement.AfterFirstSumcheck R pp) Unit
      (Sumcheck.Spec.pSpec R 3 pp.ℓ_m) :=
  (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).liftContext
    (firstSumcheckContextLens pp) (firstSumcheckOracleLens pp oSpec)

instance instFirstSumcheckVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (firstSumcheckReduction (R := R) pp oSpec).verifier where
  hCohInl i k h := by
    simp only [firstSumcheckReduction, OracleVerifier.liftContext, Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [firstSumcheckReduction, OracleVerifier.liftContext, Function.Embedding.inl_apply] at h
    cases h

/-- **`LiftContextCoherent` instance for the Spartan first sum-check lens** — the #433 framework gate
for the first sum-check lift, the first-phase analogue of `secondSumcheckCoherent`. -/
@[reducible] noncomputable def firstSumcheckCoherent :
    OracleVerifier.LiftContextCoherent (firstSumcheckOracleLens pp oSpec)
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier :=
  liftContextCoherent_of (firstSumcheckOracleLens pp oSpec) _
    (fun _ _ => rfl)
    (by
      intro os oos transcript q
      obtain ⟨τ, 𝕩⟩ := os
      obtain ⟨idx, point⟩ := q
      refine (firstSCEvalFromOracles_simOracle2 pp oSpec oos transcript.messages ⟨τ, 𝕩⟩
        point).trans ?_
      simp only [firstSumcheckOracleLens, firstSumcheckStmtLens, OracleStatement.Lens.proj,
        OracleInterface.simOracle2, QueryImpl.addLift,
        QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
      rfl)
    (by
      intro os oos transcript so
      obtain ⟨τ, 𝕩⟩ := os
      simp [firstSumcheckOracleLens, firstSumcheckStmtLens, OracleStatement.Lens.lift,
        OracleStatement.Lens.proj])

omit [Fintype R] [SampleableType R] in
/-- **`firstSumcheckResidual` discharged (degree-corrected).** The first sum-check oracle reduction
exists, of the type the Spartan composition consumes — over `ℓ_m` variables with the **degree-`3`**
sum-check protocol spec. (The scaffold's `firstSumcheckResidual` declares degree `2`; the honest
degree is `3` because `ℱ = eq · (Ã·B̃ − C̃)` is `eq` (degree 1) times a degree-2 product.) -/
theorem firstSumcheckReduction_nonempty :
    Nonempty (OracleReduction oSpec
      (Statement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstChallenge R pp) Unit
      (Statement.AfterFirstSumcheck R pp) (OracleStatement.AfterFirstSumcheck R pp) Unit
      (Sumcheck.Spec.pSpec R 3 pp.ℓ_m)) :=
  ⟨firstSumcheckReduction pp oSpec⟩

end Spartan.Spec
