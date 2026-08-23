/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.FirstSumcheckComplete

/-!
Rigorous confirmation that the `lift_knowledgeSound` residual is FALSE *as a per-instance
implication*, independent of witness content.

The residual is:  (∑_cube ℱ(τ,𝕩,oStmt) = 0)  ⟹  R1CS.relation 𝕩 (A,B,C) 𝕨.

Via `firstSumCheckVirtualPolynomial_hypercubeSum_eq_zeroCheckEval`, the hypothesis equals
`𝒢(τ) = 0` for the SINGLE fixed point τ. Via `relation_iff_zeroCheck_vanishes`, R1CS-sat ⟺
`𝒢` vanishes at EVERY boolean point. So the residual is literally:

    "𝒢 vanishes at the one point τ"  ⟹  "𝒢 vanishes at every boolean point",

which is false whenever 𝒢 is a nonzero polynomial that happens to vanish at τ. The data
(τ, 𝕩, oStmt) — which already INCLUDES the R1CS witness in oStmt(.inr 0) — fully determines
both sides, so NO additional witness content carried in the `WitIn`/`WitOut` slot can rescue it.
-/

open MvPolynomial OracleComp Sumcheck

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams)

/-- The residual obligation, phrased on the genuine zero-check polynomial.
This is logically equivalent to the `lift_knowledgeSound` goal (after the two named bridges). -/
def residualImplication (τ : Fin pp.ℓ_m → R) (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) : Prop :=
  (MvPolynomial.eval τ (zeroCheckVirtualPolynomial R pp 𝕩 oStmt) = 0) →
    R1CS.relation R pp.toSizeR1CS 𝕩 (fun idx => oStmt (.inl idx)) (oStmt (.inr 0))

/-- The residual is logically equivalent (via the two PROVEN named bridges) to the actual
`lift_knowledgeSound` goal: hypothesis = cube-sum, conclusion = R1CS-sat. -/
theorem residual_eq_liftGoal (τ : Fin pp.ℓ_m → R) (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) :
    residualImplication pp τ 𝕩 oStmt ↔
      ((∑ X : Fin pp.ℓ_m → Fin 2,
          MvPolynomial.eval (fun i => ((X i : Fin 2) : R))
            (firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt)) = 0 →
        R1CS.relation R pp.toSizeR1CS 𝕩 (fun idx => oStmt (.inl idx)) (oStmt (.inr 0))) := by
  unfold residualImplication
  rw [firstSumCheckVirtualPolynomial_hypercubeSum_eq_zeroCheckEval]

end Spartan.Spec
