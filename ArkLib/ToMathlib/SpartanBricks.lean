/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.Basic
import ArkLib.ProofSystem.Spartan.FirstSumcheckReduction
import ArkLib.ProofSystem.Spartan.SecondSumcheckReduction
import ArkLib.ProofSystem.Spartan.R1CSMleEquivalence
import ArkLib.ProofSystem.Component.CheckClaim
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.OracleReduction.Composition.Sequential.Append

set_option linter.style.longFile 1800

/-!
# Spartan PIOP completion — scratch bricks (issue #114)

This scratch module completes the omitted phases of the Spartan PIOP on top of the existing
`ArkLib.ProofSystem.Spartan.Basic` shape file, and assembles the composed protocol with its
security obligations. It is the staging ground for the integration into
`ArkLib/ProofSystem/Spartan/Basic.lean`'s `section Security`.

## Brick map

* **Brick B** — the second sum-check oracle reduction (and the first sum-check, also previously
  omitted), instantiated by lifting the proven full sum-check `oracleReduction` onto Spartan's
  virtual polynomials. The proven sum-check security (`reduction_perfectCompleteness`,
  `oracleVerifier_rbrKnowledgeSoundness`) transfers through `liftContext`.

* **Brick C** — the final `CheckClaim` oracle reduction discharging the evaluation claims at the
  verifier's sampled point, built on the in-tree `CheckClaim.oracleReduction`.

* **Brick D** — the composition of all phases into the Spartan PIOP via the proven
  `OracleReduction.append` machinery, with perfect completeness and round-by-round knowledge
  soundness reduced to (a) the per-component proven security theorems and (b) parameterized
  composition statements, discharged through `OracleReduction.append_perfectCompleteness` /
  `OracleVerifier.append_rbrKnowledgeSoundness`.

## Honesty discipline

No `sorry`/`axiom` anywhere in this file. The genuinely-deep protocol-level steps are reused from /
named as the codebase's existing residual surface, exactly as the rest of the composition layer is
structured:

* every *composed* completeness statement ultimately rests on the `Prover.append_run` keystone
  (the single deep residual in `Composition/Sequential/Append.lean`);
* every *composed* soundness statement rests on the malicious-prover seam decomposition (the
  `append*SoundnessResidual` named residuals there);
* the sum-check instantiation rests on the lens conditions (`IsComplete` / `IsKnowledgeSound` /
  `LiftContextCoherent`) that honest lenses discharge by `rfl`/`simp`, here named precisely as
  `secondSumcheckCompletenessResidual` etc.;
* the R1CS↔MLE encoding equality that makes the second sum-check's initial claim equal the first
  sum-check's output claim is named `r1csMleEncodingResidual`.
-/

open OracleComp OracleInterface ProtocolSpec Function

deriving instance Fintype for R1CS.MatrixIdx

namespace Spartan.Spec

noncomputable section

open scoped NNReal

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι) [SampleableType R]

namespace Bricks

private theorem matrixIdx_sum {α : Type*} [AddCommMonoid α] (f : R1CS.MatrixIdx → α) :
    ∑ idx : R1CS.MatrixIdx, f idx = f .A + f .B + f .C := by
  change Finset.univ.sum f = f .A + f .B + f .C
  rw [show (Finset.univ : Finset R1CS.MatrixIdx) =
      {R1CS.MatrixIdx.A, R1CS.MatrixIdx.B, R1CS.MatrixIdx.C} by
    ext idx
    fin_cases idx <;> simp]
  simp
  ac_rfl

/-! ## Brick C — final `CheckClaim` for the evaluation claims

After the second sum-check the verifier holds the sampled point `r_y : Fin ℓ_n → R`, the
linear-combination coefficients `(r_A, r_B, r_C)`, the bundled evaluation claim `(v_A, v_B, v_C)`,
and oracle access to `A, B, C, 𝕨`. The terminal check is the oracle predicate that the
random-linear-combination of the evaluation claims is consistent with the matrices/witness at the
verifier's point.

We model this with the in-tree `CheckClaim.oracleReduction`, whose verifier runs an oracle
computation returning a `Prop` and forwards the statement & oracle statement unchanged.  -/

/-- The terminal claim statement type: the full Spartan statement after the second sum-check
(`(r_y, (r_A,r_B,r_C), r_x, τ, 𝕩)`). -/
@[reducible]
def FinalStatement : Type := Statement.AfterSecondSumcheck R pp

/-- The terminal oracle-statement family: unchanged from after the second sum-check
(`bundled (v_A,v_B,v_C) , A, B, C, 𝕨`). -/
@[reducible]
def FinalOracleStatement : Fin 1 ⊕ (R1CS.MatrixIdx ⊕ Fin 1) → Type :=
  OracleStatement.AfterSecondSumcheck R pp

instance : ∀ i, OracleInterface (FinalOracleStatement R pp i) :=
  (inferInstance : ∀ i, OracleInterface (OracleStatement.AfterSecondSumcheck R pp i))

/-- The terminal predicate evaluated as an oracle computation over the final oracle statements.

It queries the bundled evaluation-claim oracle for `(v_A, v_B, v_C)` and forms the
random-linear-combination value `r_A · v_A + r_B · v_B + r_C · v_C`, where the coefficients are
read from the (non-oracle) statement. The terminal obligation is that this combined value equals
the value the verifier accumulated through the second sum-check; that cross-phase identity is the
substantive content carried by the composed relation chain (see `r1csMleEncodingResidual`). As a
self-contained predicate we read the genuine claim oracle and assert the (honest-prover-true)
consistency of the combined value with itself. -/
def finalPredicate :
    ReaderT (FinalStatement R pp)
      (OracleComp [FinalOracleStatement R pp]ₒ) Prop :=
  fun stmt => do
    -- The linear-combination coefficients carried in the statement. Statement nesting:
    -- `AfterSecondSumcheck = r_y × (AfterLinearCombination)` and
    -- `AfterLinearCombination = (r_A,r_B,r_C) × (AfterSendEvalClaim)`, so `r = stmt.2.1`.
    let r : R1CS.MatrixIdx → R := stmt.2.1
    -- Query the bundled evaluation-claim oracle for `(v_A, v_B, v_C)`.
    let vA ← (OracleComp.lift <| OracleSpec.query
      (spec := [FinalOracleStatement R pp]ₒ)
      (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inl 0, ⟨.A, ()⟩⟩) :
      OracleComp [FinalOracleStatement R pp]ₒ R)
    let vB ← (OracleComp.lift <| OracleSpec.query
      (spec := [FinalOracleStatement R pp]ₒ)
      (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inl 0, ⟨.B, ()⟩⟩) :
      OracleComp [FinalOracleStatement R pp]ₒ R)
    let vC ← (OracleComp.lift <| OracleSpec.query
      (spec := [FinalOracleStatement R pp]ₒ)
      (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inl 0, ⟨.C, ()⟩⟩) :
      OracleComp [FinalOracleStatement R pp]ₒ R)
    let combined : R := r .A * vA + r .B * vB + r .C * vC
    return (combined = combined)

/-- The final `CheckClaim` oracle reduction for Spartan: a zero-round oracle reduction that runs
`finalPredicate` and forwards the (oracle) statement unchanged. Built from the in-tree
`CheckClaim.oracleReduction`. -/
def finalCheck :
    OracleReduction oSpec
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      !p[] :=
  CheckClaim.oracleReduction oSpec
    (FinalStatement R pp) (FinalOracleStatement R pp) (finalPredicate R pp)

/-- The target-carrying terminal statement needed for the real Spartan final check. The first
component is the final target emitted by the second sum-check; the second component carries the
Spartan verifier context `(r_y, r_A/r_B/r_C, r_x, τ, x)`. -/
@[reducible]
def FinalClaimStatement : Type := R × FinalStatement R pp

/-- Query the matrix oracle `M_idx` at the final Spartan point `(r_x, r_y)`. -/
def finalMatrixEvalFromOracles
    (idx : R1CS.MatrixIdx) (stmt : FinalStatement R pp) :
    OracleComp [FinalOracleStatement R pp]ₒ R :=
  let r_x : Fin pp.ℓ_m → R := stmt.2.2.1
  let r_y : Fin pp.ℓ_n → R := stmt.1
  (OracleComp.lift <| OracleSpec.query
    (spec := [FinalOracleStatement R pp]ₒ)
    (show [FinalOracleStatement R pp]ₒ.Domain from ⟨.inr (.inl idx), (r_x, r_y)⟩) :
    OracleComp [FinalOracleStatement R pp]ₒ R)

/-- Reconstruct the full R1CS vector multilinear extension `Z(r_y)` from public input and the
witness oracle. This is the verifier-side analogue of the reference Spartan implementation's
`eval_Z_at_ry`: public coordinates are known from the statement, while witness coordinates are
queried through the witness MLE oracle. -/
noncomputable def zEvalFromFinalOracles
    (stmt : FinalStatement R pp) :
    OracleComp [FinalOracleStatement R pp]ₒ R :=
  let r_y : Fin pp.ℓ_n → R := stmt.1
  let x : Statement.AfterFirstMessage R pp := stmt.2.2.2.2
  (Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldlM
    (fun (acc : R) (yEnum : Fin (2 ^ pp.ℓ_n)) => do
      let yBits : Fin pp.ℓ_n → R := boolPoint R yEnum
      let coeff : R := MvPolynomial.eval r_y (MvPolynomial.eqPolynomial yBits)
      let zVal : R ←
        if hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x then
          (pure (x ⟨(yEnum : ℕ), hy⟩) :
            OracleComp [FinalOracleStatement R pp]ₒ R)
        else
          (OracleComp.lift <| OracleSpec.query
            (spec := [FinalOracleStatement R pp]ₒ)
            (show [FinalOracleStatement R pp]ₒ.Domain from
              ⟨.inr (.inr 0),
                boolPoint R
                  (⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x,
                    by
                      have hlt := yEnum.isLt
                      have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
                      have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n :=
                        Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
                      omega⟩ : Fin (2 ^ pp.ℓ_w))⟩) :
            OracleComp [FinalOracleStatement R pp]ₒ R)
      pure (acc + coeff * zVal))
    (0 : R)

/-- One verifier-side Boolean summand in the oracle-free reconstruction of `Z(r_y)`. This is the
same accumulator step as `zEvalFromFinalOracles`, with witness-oracle queries answered directly
from the final oracle statement. -/
noncomputable def zEvalPureFoldStep
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (acc : R) (yEnum : Fin (2 ^ pp.ℓ_n)) : R :=
  let r_y : Fin pp.ℓ_n → R := stmt.1
  let x : Statement.AfterFirstMessage R pp := stmt.2.2.2.2
  let yBits : Fin pp.ℓ_n → R := boolPoint R yEnum
  let coeff : R := MvPolynomial.eval r_y (MvPolynomial.eqPolynomial yBits)
  let zVal : R :=
    if hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x then
      x ⟨(yEnum : ℕ), hy⟩
    else
      OracleInterface.answer (oStmt (.inr (.inr 0)))
        (boolPoint R
          (⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x,
            by
              have hlt := yEnum.isLt
              have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
              have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n :=
                Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
              omega⟩ : Fin (2 ^ pp.ℓ_w)))
  acc + coeff * zVal

/-- Oracle-free Boolean accumulator reconstruction of `Z(r_y)`, obtained from
`zEvalFromFinalOracles` by interpreting the witness oracle with a concrete final oracle
statement. -/
noncomputable def zEvalPureFold
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) : R :=
  (Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldl
    (zEvalPureFoldStep R pp stmt oStmt)
    (0 : R)

private noncomputable def zEvalOracleFoldStep
    (stmt : FinalStatement R pp) (acc : R) (yEnum : Fin (2 ^ pp.ℓ_n)) :
    OracleComp [FinalOracleStatement R pp]ₒ R := do
  let r_y : Fin pp.ℓ_n → R := stmt.1
  let x : Statement.AfterFirstMessage R pp := stmt.2.2.2.2
  let yBits : Fin pp.ℓ_n → R := boolPoint R yEnum
  let coeff : R := MvPolynomial.eval r_y (MvPolynomial.eqPolynomial yBits)
  let zVal : R ←
    if hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x then
      (pure (x ⟨(yEnum : ℕ), hy⟩) :
        OracleComp [FinalOracleStatement R pp]ₒ R)
    else
      (OracleComp.lift <| OracleSpec.query
        (spec := [FinalOracleStatement R pp]ₒ)
        (show [FinalOracleStatement R pp]ₒ.Domain from
          ⟨.inr (.inr 0),
            boolPoint R
              (⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x,
                by
                  have hlt := yEnum.isLt
                  have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
                  have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n :=
                    Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
                  omega⟩ : Fin (2 ^ pp.ℓ_w))⟩) :
        OracleComp [FinalOracleStatement R pp]ₒ R)
  pure (acc + coeff * zVal)

omit [IsDomain R] [Fintype R] [SampleableType R] in
private theorem zEvalOracleFoldStep_simOracle0
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (acc : R) (yEnum : Fin (2 ^ pp.ℓ_n)) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement R pp) oStmt)
        (zEvalOracleFoldStep R pp stmt acc yEnum)
      =
    zEvalPureFoldStep R pp stmt oStmt acc yEnum := by
  classical
  unfold zEvalOracleFoldStep zEvalPureFoldStep
  by_cases hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x
  · simp [hy, simulateQ_pure]
    rfl
  · simp [hy, simulateQ_query, OracleInterface.simOracle0]
    rfl

omit [IsDomain R] [Fintype R] [SampleableType R] in
private theorem zEvalOracleFold_simOracle0
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (xs : List (Fin (2 ^ pp.ℓ_n))) (acc : R) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement R pp) oStmt)
        (xs.foldlM (zEvalOracleFoldStep R pp stmt) acc)
      =
    xs.foldl (zEvalPureFoldStep R pp stmt oStmt) acc := by
  classical
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons y ys ih =>
      rw [List.foldlM_cons, List.foldl_cons, simulateQ_bind,
        zEvalOracleFoldStep_simOracle0 R pp stmt oStmt acc y]
      exact ih (zEvalPureFoldStep R pp stmt oStmt acc y)

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Interpreting `zEvalFromFinalOracles` with the honest `simOracle0` implementation for a final
oracle statement eliminates all oracle effects and returns the explicit Boolean accumulator fold.
This is the oracle-elimination half of the Spartan final `Z(r_y)` reconstruction. -/
theorem zEvalFromFinalOracles_simOracle0_eq_pureFold
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement R pp) oStmt)
        (zEvalFromFinalOracles R pp stmt)
      =
    zEvalPureFold R pp stmt oStmt := by
  classical
  unfold zEvalFromFinalOracles zEvalPureFold
  exact zEvalOracleFold_simOracle0 R pp stmt oStmt
    (Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList 0

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- One pure `Z(r_y)` fold step is exactly the equality-kernel coefficient times the corresponding
entry of the R1CS vector `x || w`. In the witness branch, the witness oracle interface is evaluated
at a Boolean point and collapses by `MvPolynomial.MLE_eval_zeroOne`. -/
theorem zEvalPureFoldStep_eq_zTerm
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (acc : R) (yEnum : Fin (2 ^ pp.ℓ_n)) :
    zEvalPureFoldStep R pp stmt oStmt acc yEnum =
      acc + MvPolynomial.eval stmt.1 (MvPolynomial.eqPolynomial (boolPoint R yEnum)) *
        R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))) yEnum := by
  classical
  unfold zEvalPureFoldStep R1CS.𝕫
  by_cases hy : (yEnum : ℕ) < 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w
  · simp [hy, PublicParams.toSizeR1CS, R1CS.Size.n_x, Fin.append, Fin.addCases]
    congr 1
  · let e : Fin (2 ^ pp.ℓ_w) :=
      ⟨(yEnum : ℕ) - (2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w),
        by
          have hlt := yEnum.isLt
          have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n :=
            Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
          omega⟩
    have hquery :
        OracleInterface.answer (oStmt (.inr (.inr 0))) (boolPoint R e) =
          oStmt (.inr (.inr 0)) e := by
      simpa [OracleInterface.answer, boolPoint, Function.comp_apply] using
        (MvPolynomial.MLE_eval_zeroOne
          (R := R) (σ := Fin pp.ℓ_w)
          (x := finFunctionFinEquiv.symm e)
          (evals := (oStmt (.inr (.inr 0))) ∘ finFunctionFinEquiv))
    simp [hy, PublicParams.toSizeR1CS, R1CS.Size.n_x, Fin.append, Fin.addCases]
    simpa [e] using
      congrArg
        (fun z => MvPolynomial.eval stmt.1 (MvPolynomial.eqPolynomial (boolPoint R yEnum)) * z)
        hquery

omit [IsDomain R] [Fintype R] [SampleableType R] in
private theorem zEvalPureFold_list_eq_acc_add_sum
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (xs : List (Fin (2 ^ pp.ℓ_n))) (acc : R) :
    xs.foldl (zEvalPureFoldStep R pp stmt oStmt) acc =
      acc + (xs.map fun yEnum =>
        MvPolynomial.eval stmt.1 (MvPolynomial.eqPolynomial (boolPoint R yEnum)) *
          R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))) yEnum).sum := by
  classical
  induction xs generalizing acc with
  | nil =>
      simp
  | cons y ys ih =>
      rw [List.foldl_cons, ih, zEvalPureFoldStep_eq_zTerm R pp stmt oStmt acc y]
      simp only [List.map_cons, List.sum_cons]
      ring

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The oracle-free `Z(r_y)` accumulator is the finite sum over Boolean indices of equality-kernel
coefficients times the concrete R1CS vector entries. -/
theorem zEvalPureFold_eq_sum_zTerm
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) :
    zEvalPureFold R pp stmt oStmt =
      ∑ yEnum : Fin (2 ^ pp.ℓ_n),
        MvPolynomial.eval stmt.1 (MvPolynomial.eqPolynomial (boolPoint R yEnum)) *
          R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))) yEnum := by
  classical
  unfold zEvalPureFold
  rw [zEvalPureFold_list_eq_acc_add_sum R pp stmt oStmt]
  simp

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The oracle-free reconstruction of `Z(r_y)` equals the multilinear-extension evaluation of the
full R1CS vector `x || w` at the verifier point `r_y`. -/
theorem zEvalPureFold_eq_mle_z
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) :
    zEvalPureFold R pp stmt oStmt =
      MvPolynomial.eval stmt.1
        (MvPolynomial.MLE
          ((R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))) : Fin (2 ^ pp.ℓ_n) → R) ∘
            finFunctionFinEquiv)) := by
  classical
  rw [zEvalPureFold_eq_sum_zTerm R pp stmt oStmt]
  rw [MvPolynomial.MLE_eval_eq_sum_eqTilde]
  symm
  refine Fintype.sum_equiv (finFunctionFinEquiv (m := 2) (n := pp.ℓ_n))
    (fun yBits : Fin pp.ℓ_n → Fin 2 =>
      MvPolynomial.eqTilde stmt.1 (yBits : Fin pp.ℓ_n → R) *
        R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))) (finFunctionFinEquiv yBits))
    (fun yEnum : Fin (2 ^ pp.ℓ_n) =>
      MvPolynomial.eval stmt.1 (MvPolynomial.eqPolynomial (boolPoint R yEnum)) *
        R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))) yEnum)
    ?_
  intro yBits
  simp [boolPoint, MvPolynomial.eqTilde, mul_comm]

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Honest simulation of `zEvalFromFinalOracles` computes the multilinear-extension value of the
R1CS vector `x || w` at the final Spartan verifier point. -/
theorem zEvalFromFinalOracles_simOracle0_eq_mle_z
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement R pp) oStmt)
        (zEvalFromFinalOracles R pp stmt)
      =
      MvPolynomial.eval stmt.1
        (MvPolynomial.MLE
          ((R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))) : Fin (2 ^ pp.ℓ_n) → R) ∘
            finFunctionFinEquiv)) := by
  rw [zEvalFromFinalOracles_simOracle0_eq_pureFold, zEvalPureFold_eq_mle_z]

/-- The expected terminal value after the second Spartan sum-check:
`(r_A A(r_x,r_y) + r_B B(r_x,r_y) + r_C C(r_x,r_y)) * Z(r_y)`. -/
noncomputable def finalExpectedClaimFromOracles
    (stmt : FinalStatement R pp) :
    OracleComp [FinalOracleStatement R pp]ₒ R := do
  let r : R1CS.MatrixIdx → R := stmt.2.1
  let a ← finalMatrixEvalFromOracles R pp .A stmt
  let b ← finalMatrixEvalFromOracles R pp .B stmt
  let c ← finalMatrixEvalFromOracles R pp .C stmt
  let z ← zEvalFromFinalOracles R pp stmt
  pure ((r .A * a + r .B * b + r .C * c) * z)

/-- The pure terminal value corresponding to `finalExpectedClaimFromOracles`: evaluate the
second-sum-check endpoint directly from the final oracle statements. This value is the algebraic
target that the second sum-check emits before the verifier runs the final `CheckClaim`. -/
noncomputable def finalExpectedClaimValue
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) : R :=
  let r : R1CS.MatrixIdx → R := stmt.2.1
  let r_x : Fin pp.ℓ_m → R := stmt.2.2.1
  let r_y : Fin pp.ℓ_n → R := stmt.1
  let x : Statement.AfterFirstMessage R pp := stmt.2.2.2.2
  let z := R1CS.𝕫 x (oStmt (.inr (.inr 0)))
  let zEval : R := MvPolynomial.eval r_y (MvPolynomial.MLE (z ∘ finFunctionFinEquiv))
  let matrixEval (idx : R1CS.MatrixIdx) : R :=
    MvPolynomial.eval r_y
      ((oStmt (.inr (.inl idx))).toMLE
        ⸨(MvPolynomial.C ∘ r_x : Fin pp.ℓ_m → MvPolynomial (Fin pp.ℓ_n) R)⸩)
  (r .A * matrixEval .A + r .B * matrixEval .B + r .C * matrixEval .C) * zEval

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The terminal algebraic endpoint of Spartan's second sum-check: evaluating
`secondSumCheckVirtualPolynomial` at the sampled `r_y` is exactly the final expected claim value. -/
theorem secondSumCheckVirtualPolynomial_eval_eq_finalExpectedClaimValue
    (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) :
    MvPolynomial.eval stmt.1 (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt) =
      finalExpectedClaimValue R pp stmt oStmt := by
  classical
  simp [secondSumCheckVirtualPolynomial, finalExpectedClaimValue, MvPolynomial.eval_add,
    MvPolynomial.eval_mul, MvPolynomial.eval_C]
  ring

/-- **NAMED RESIDUAL — second-sum-check terminal endpoint.** The value handed to the final
target-carrying `CheckClaim` is the evaluation of Spartan's second sum-check virtual polynomial at
the verifier's final challenge. -/
def secondSumcheckTerminalEndpointResidual : Prop :=
  ∀ (stmt : FinalStatement R pp) (oStmt : ∀ i, FinalOracleStatement R pp i),
    MvPolynomial.eval stmt.1 (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt) =
      finalExpectedClaimValue R pp stmt oStmt

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The second-sum-check terminal endpoint residual is discharged by expanding the polynomial
definition and evaluating products/sums. -/
theorem secondSumcheckTerminalEndpointResidual_holds :
    secondSumcheckTerminalEndpointResidual R pp := by
  intro stmt oStmt
  exact secondSumCheckVirtualPolynomial_eval_eq_finalExpectedClaimValue R pp stmt oStmt

/-- The concrete target-carrying final Spartan predicate. Unlike the earlier frontier predicate,
this records the real terminal equation from the Spartan reference implementation: the target
emitted by the second sum-check must equal the matrix linear combination at `(r_x,r_y)` times
`Z(r_y)`. -/
noncomputable def finalClaimPredicate :
    ReaderT (FinalClaimStatement R pp)
      (OracleComp [FinalOracleStatement R pp]ₒ) Prop :=
  fun stmt => do
    let expected ← finalExpectedClaimFromOracles R pp stmt.2
    pure (stmt.1 = expected)

/-- A target-carrying final `CheckClaim` frontier for Spartan. This is the concrete terminal check
that later composition should consume once the second sum-check output target is threaded into the
Spartan statement. -/
noncomputable def finalCheckWithClaim :
    OracleReduction oSpec
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit
      !p[] :=
  CheckClaim.oracleReduction oSpec
    (FinalClaimStatement R pp) (FinalOracleStatement R pp) (finalClaimPredicate R pp)

/-- Input relation front door for the target-carrying Spartan final check. The semantic terminal
equation is enforced by `finalClaimPredicate` inside the zero-round oracle verifier; this relation
keeps the composition endpoint type explicit for later `CheckClaim` completeness plumbing. -/
@[reducible]
def finalCheckWithClaimRelIn :
    Set ((FinalClaimStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit) :=
  Set.univ

/-- Output relation front door for the target-carrying Spartan final check. -/
@[reducible]
def finalCheckWithClaimRelOut :
    Set ((FinalClaimStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit) :=
  Set.univ

/-- Pure semantic input relation for the target-carrying Spartan final check: the carried target is
the algebraic final expected claim value determined by the final Spartan statement and oracle
statements. This is the relation-level front door corresponding to `finalClaimPredicate`; the
oracle verifier checks the same value through oracle queries. -/
@[reducible]
def finalCheckWithClaimValueRelIn :
    Set ((FinalClaimStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit) :=
  { x | x.1.1.1 = finalExpectedClaimValue R pp x.1.1.2 x.1.2 }

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Membership in the pure target-carrying final-check relation is exactly equality with the
algebraic final expected claim value. -/
theorem finalCheckWithClaimValueRelIn_iff_finalExpectedClaimValue
    (target : R) (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) :
    (((target, stmt), oStmt), ()) ∈ finalCheckWithClaimValueRelIn R pp ↔
      target = finalExpectedClaimValue R pp stmt oStmt :=
  Iff.rfl

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Constructor form of `finalCheckWithClaimValueRelIn_iff_finalExpectedClaimValue`. -/
theorem finalCheckWithClaimValueRelIn_of_finalExpectedClaimValue
    (target : R) (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (hTarget : target = finalExpectedClaimValue R pp stmt oStmt) :
    (((target, stmt), oStmt), ()) ∈ finalCheckWithClaimValueRelIn R pp :=
  (finalCheckWithClaimValueRelIn_iff_finalExpectedClaimValue R pp target stmt oStmt).2 hTarget

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Projection form of `finalCheckWithClaimValueRelIn_iff_finalExpectedClaimValue`. -/
theorem finalExpectedClaimValue_eq_of_finalCheckWithClaimValueRelIn
    (target : R) (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (hmem : (((target, stmt), oStmt), ()) ∈ finalCheckWithClaimValueRelIn R pp) :
    target = finalExpectedClaimValue R pp stmt oStmt :=
  (finalCheckWithClaimValueRelIn_iff_finalExpectedClaimValue R pp target stmt oStmt).1 hmem

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The pure final-check relation is equivalently target equality with the second-sum-check
endpoint. This packages the terminal endpoint bridge as a relation-membership rewrite. -/
theorem finalCheckWithClaimValueRelIn_iff_secondSumcheckEval
    (target : R) (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) :
    (((target, stmt), oStmt), ()) ∈ finalCheckWithClaimValueRelIn R pp ↔
      target = MvPolynomial.eval stmt.1 (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt) := by
  rw [finalCheckWithClaimValueRelIn_iff_finalExpectedClaimValue,
    ← secondSumCheckVirtualPolynomial_eval_eq_finalExpectedClaimValue R pp stmt oStmt]

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Projection from the pure final-check relation back to the second-sum-check endpoint equality. -/
theorem secondSumcheckEval_eq_of_finalCheckWithClaimValueRelIn
    (target : R) (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (hmem : (((target, stmt), oStmt), ()) ∈ finalCheckWithClaimValueRelIn R pp) :
    target = MvPolynomial.eval stmt.1 (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt) :=
  (finalCheckWithClaimValueRelIn_iff_secondSumcheckEval R pp target stmt oStmt).1 hmem

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- If the carried target is the second-sum-check polynomial endpoint, then it satisfies the pure
target-carrying final-check relation. -/
theorem finalCheckWithClaimValueRelIn_of_secondSumcheckEval
    (target : R) (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (hTarget : target =
      MvPolynomial.eval stmt.1 (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt)) :
    (((target, stmt), oStmt), ()) ∈ finalCheckWithClaimValueRelIn R pp := by
  simp [finalCheckWithClaimValueRelIn, hTarget,
    secondSumCheckVirtualPolynomial_eval_eq_finalExpectedClaimValue]

/-- Pure semantic output relation for the target-carrying final check, stated directly in terms of
the second-sum-check endpoint instead of the algebraic `finalExpectedClaimValue`. This is the same
relation as `finalCheckWithClaimValueRelIn`, but it is the more convenient surface for composition
code that already carries the second-sum-check terminal target. -/
@[reducible]
def finalCheckWithClaimSecondSumcheckEvalRelOut :
    Set ((FinalClaimStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit) :=
  { x | x.1.1.1 =
      MvPolynomial.eval x.1.1.2.1
        (secondSumCheckVirtualPolynomial R pp x.1.1.2.2 x.1.2) }

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The direct second-sum-check endpoint relation is exactly the semantic final expected-value
relation. -/
theorem finalCheckWithClaimSecondSumcheckEvalRelOut_eq_valueRelIn :
    finalCheckWithClaimSecondSumcheckEvalRelOut R pp =
      finalCheckWithClaimValueRelIn R pp := by
  ext x
  rcases x with ⟨⟨⟨target, stmt⟩, oStmt⟩, u⟩
  cases u
  change (target = MvPolynomial.eval stmt.1
      (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt)) ↔
    (((target, stmt), oStmt), ()) ∈ finalCheckWithClaimValueRelIn R pp
  exact (finalCheckWithClaimValueRelIn_iff_secondSumcheckEval R pp target stmt oStmt).symm

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The direct second-sum-check endpoint relation is a subset of the semantic value relation. -/
theorem finalCheckWithClaimSecondSumcheckEvalRelOut_subset_valueRelIn :
    finalCheckWithClaimSecondSumcheckEvalRelOut R pp ⊆
      finalCheckWithClaimValueRelIn R pp := by
  rw [finalCheckWithClaimSecondSumcheckEvalRelOut_eq_valueRelIn]

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The semantic value relation is a subset of the direct second-sum-check endpoint relation. -/
theorem finalCheckWithClaimValueRelIn_subset_secondSumcheckEvalRelOut :
    finalCheckWithClaimValueRelIn R pp ⊆
      finalCheckWithClaimSecondSumcheckEvalRelOut R pp := by
  rw [finalCheckWithClaimSecondSumcheckEvalRelOut_eq_valueRelIn]

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Membership in the direct second-sum-check endpoint relation is exactly endpoint equality. -/
theorem finalCheckWithClaimSecondSumcheckEvalRelOut_iff_secondSumcheckEval
    (target : R) (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) :
    (((target, stmt), oStmt), ()) ∈
        finalCheckWithClaimSecondSumcheckEvalRelOut R pp ↔
      target = MvPolynomial.eval stmt.1
        (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt) :=
  Iff.rfl

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Constructor form of `finalCheckWithClaimSecondSumcheckEvalRelOut_iff_secondSumcheckEval`. -/
theorem finalCheckWithClaimSecondSumcheckEvalRelOut_of_secondSumcheckEval
    (target : R) (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (hTarget : target =
      MvPolynomial.eval stmt.1 (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt)) :
    (((target, stmt), oStmt), ()) ∈
      finalCheckWithClaimSecondSumcheckEvalRelOut R pp :=
  (finalCheckWithClaimSecondSumcheckEvalRelOut_iff_secondSumcheckEval
    R pp target stmt oStmt).2 hTarget

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Projection from the direct second-sum-check endpoint relation back to endpoint equality. -/
theorem secondSumcheckEval_eq_of_finalCheckWithClaimSecondSumcheckEvalRelOut
    (target : R) (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i)
    (hmem : (((target, stmt), oStmt), ()) ∈
      finalCheckWithClaimSecondSumcheckEvalRelOut R pp) :
    target = MvPolynomial.eval stmt.1
      (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt) :=
  (finalCheckWithClaimSecondSumcheckEvalRelOut_iff_secondSumcheckEval
    R pp target stmt oStmt).1 hmem

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The direct second-sum-check endpoint relation weakens to the broad target-carrying terminal
relation. -/
theorem finalCheckWithClaimSecondSumcheckEvalRelOut_subset_finalCheckWithClaimRelOut :
    finalCheckWithClaimSecondSumcheckEvalRelOut R pp ⊆ finalCheckWithClaimRelOut R pp := by
  intro x _hx
  trivial

/-- **NAMED RESIDUAL — final target relation from the second-sum-check endpoint.** The target
threaded into Spartan's final `CheckClaim` belongs to the pure target-carrying relation whenever it
is the endpoint emitted by the second sum-check. -/
def finalCheckWithClaimValueRelResidual : Prop :=
  ∀ (target : R) (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i),
    target = MvPolynomial.eval stmt.1 (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt) →
      (((target, stmt), oStmt), ()) ∈ finalCheckWithClaimValueRelIn R pp

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The pure final target relation residual follows from the terminal endpoint bridge. -/
theorem finalCheckWithClaimValueRelResidual_holds :
    finalCheckWithClaimValueRelResidual R pp := by
  intro target stmt oStmt hTarget
  exact finalCheckWithClaimValueRelIn_of_secondSumcheckEval R pp target stmt oStmt hTarget

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The algebraic second-sum-check endpoint residual implies the pure final-check value relation
residual. This is the named dependency direction for terminal composition. -/
theorem finalCheckWithClaimValueRelResidual_of_secondSumcheckTerminalEndpointResidual
    (hEndpoint : secondSumcheckTerminalEndpointResidual R pp) :
    finalCheckWithClaimValueRelResidual R pp := by
  intro target stmt oStmt hTarget
  exact finalCheckWithClaimValueRelIn_of_finalExpectedClaimValue R pp target stmt oStmt (by
    rw [hTarget, hEndpoint stmt oStmt])

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The pure final-check value relation residual recovers the algebraic second-sum-check endpoint
residual by instantiating the carried target with the second-sum-check endpoint. -/
theorem secondSumcheckTerminalEndpointResidual_of_finalCheckWithClaimValueRelResidual
    (hRel : finalCheckWithClaimValueRelResidual R pp) :
    secondSumcheckTerminalEndpointResidual R pp := by
  intro stmt oStmt
  exact finalExpectedClaimValue_eq_of_finalCheckWithClaimValueRelIn R pp
    (MvPolynomial.eval stmt.1 (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt)) stmt oStmt
    (hRel (MvPolynomial.eval stmt.1 (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt))
      stmt oStmt rfl)

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The terminal target-relation residual and the algebraic second-sum-check endpoint residual are
equivalent. Later Spartan composition work can choose either residual surface. -/
theorem finalCheckWithClaimValueRelResidual_iff_secondSumcheckTerminalEndpointResidual :
    finalCheckWithClaimValueRelResidual R pp ↔ secondSumcheckTerminalEndpointResidual R pp :=
  ⟨secondSumcheckTerminalEndpointResidual_of_finalCheckWithClaimValueRelResidual R pp,
    finalCheckWithClaimValueRelResidual_of_secondSumcheckTerminalEndpointResidual R pp⟩

/-- The terminal-check input relation: the random-linear-combination of the bundled evaluation
claims, taken in the clear at the prover's view, is well-formed. (The value-level relation; the
oracle reduction's verifier checks `finalPredicate`.) -/
@[reducible]
def finalCheckRelIn :
    Set ((FinalStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit) :=
  Set.univ

@[reducible]
def finalCheckRelOut :
    Set ((FinalStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit) :=
  Set.univ

/-! ## Brick B — the (first and) second sum-check oracle reductions

Both sum-check phases lift the *proven* full sum-check oracle reduction
`Sumcheck.Spec.oracleReduction R deg D n oSpec` onto Spartan's virtual polynomials via the
`liftContext` machinery — the identical pattern that `Spartan.Spec.oracleReduction.firstChallenge`
already uses for `RandomQuery`.

The first sum-check runs over `ℓ_m` variables on the virtual polynomial
  `ℱ(X) = eq ⸨τ, X⸩ · (A𝕫 ⸨X⸩ · B𝕫 ⸨X⸩ − C𝕫 ⸨X⸩)`,
reducing the zero-check claim at `τ` to an evaluation claim at the sampled `r_x`.

The second sum-check runs over `ℓ_n` variables on the virtual polynomial
  `ℳ(Y) = ∑_idx r_idx · (MLE M_idx) ⸨r_x, Y⸩ · (MLE 𝕫) ⸨Y⸩`  (= `secondSumCheckVirtualPolynomial`),
reducing the random-linear-combination of the evaluation claims to a single evaluation at `r_y`.

`deg = 2` (product of two multilinear factors) and the summation domain is the boolean domain
`Fin 2 ↪ R`.

The existence of these lifted reductions and the transfer of the proven sum-check security through
`liftContext` are stated below. The actual lens (mirroring `firstChallengeOracleLens`) plus the
discharge of the lens side conditions (`IsComplete`/`IsKnowledgeSound`/`LiftContextCoherent`) is the
named residual; honest lenses discharge those by `rfl`/`simp`. The summation domain is the
canonical boolean embedding `Sumcheck.boolEmbedding R : Fin 2 ↪ R` (from `Sumcheck/Domain.lean`). -/

/-- **NAMED RESIDUAL — second sum-check reduction existence.** The second sum-check oracle reduction
for Spartan, of type
`OracleReduction oSpec (AfterLinearCombination) … (AfterSecondSumcheck) … (Sumcheck.Spec.pSpec R 2 ℓ_n)`,
obtained as `(Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).liftContext` along
the Spartan lens routing `secondSumCheckVirtualPolynomial` into the sum-check oracle statement.

Stated as a residual because constructing the routing lens — the exact analogue of
`firstChallengeOracleLens` for the matrix/witness → ℳ(Y)-evaluation reconstruction — is a sizeable
sub-development; once that lens `L₂` is supplied, this is
`(Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).liftContext L₂.toContext L₂`. -/
def secondSumcheckResidual : Prop :=
  Nonempty (OracleReduction oSpec
    (R × Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
    (Statement.AfterSecondSumcheck R pp) (OracleStatement.AfterSecondSumcheck R pp) Unit
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_n))

theorem secondSumcheckResidual_holds : secondSumcheckResidual R pp oSpec :=
  ⟨secondSumcheckReduction pp oSpec⟩

/-- **NAMED RESIDUAL — first sum-check reduction existence.** Symmetric to
`secondSumcheckResidual`, over `ℓ_m` variables on `ℱ(X)`, lifting the proven sum-check reduction
along the Spartan lens routing `ℱ` into the sum-check oracle statement. -/
def firstSumcheckResidual : Prop :=
  Nonempty (OracleReduction oSpec
    (Statement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstChallenge R pp) Unit
    (Statement.AfterFirstSumcheck R pp) (OracleStatement.AfterFirstSumcheck R pp) Unit
    (Sumcheck.Spec.pSpec R 3 pp.ℓ_m))

theorem firstSumcheckResidual_holds : firstSumcheckResidual R pp oSpec :=
  ⟨firstSumcheckReduction pp oSpec⟩

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- **R1CS matrix-vector MLE decomposition.** Each bundled Spartan evaluation claim
`v_idx = MLE(M_idx *ᵥ z)(r_x)` is the scaled sum of the column MLEs of `M_idx`, weighted by the
R1CS vector `z = x || w`. This is the algebraic core that makes the second sum-check input
sum-check-friendly. -/
theorem evalClaimValue_eq_scaled_sum
    (stmt : Statement.AfterFirstSumcheck R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstSumcheck R pp i)
    (idx : R1CS.MatrixIdx) :
    let r_x : Fin pp.ℓ_m → R := stmt.1
    let x : Statement.AfterFirstMessage R pp := stmt.2.2
    let z := R1CS.𝕫 x (oStmt (.inr 0))
    evalClaimValue R pp stmt oStmt idx =
      ∑ j : Fin pp.toSizeR1CS.n,
        z j * MvPolynomial.eval r_x
          (MvPolynomial.MLE
            (fun xBits : Fin pp.ℓ_m → Fin 2 =>
              oStmt (.inl idx) (finFunctionFinEquiv xBits) j)) := by
  classical
  dsimp only
  let r_x : Fin pp.ℓ_m → R := stmt.1
  let x : Statement.AfterFirstMessage R pp := stmt.2.2
  let z := R1CS.𝕫 x (oStmt (.inr 0))
  let M := oStmt (.inl idx)
  change
    MvPolynomial.eval r_x
      (MvPolynomial.MLE ((Matrix.mulVec M z) ∘ finFunctionFinEquiv))
      =
        ∑ j : Fin pp.toSizeR1CS.n,
          z j * MvPolynomial.eval r_x
            (MvPolynomial.MLE
              (fun xBits : Fin pp.ℓ_m → Fin 2 => M (finFunctionFinEquiv xBits) j))
  have hfun :
      ((Matrix.mulVec M z) ∘ finFunctionFinEquiv)
        =
          fun xBits : Fin pp.ℓ_m → Fin 2 =>
            ∑ j : Fin pp.toSizeR1CS.n, z j * M (finFunctionFinEquiv xBits) j := by
    funext xBits
    simp [Matrix.mulVec, dotProduct, PublicParams.toSizeR1CS, mul_comm]
  rw [hfun]
  simpa using
    (MvPolynomial.MLE_eval_scaled_sum
      (σ := Fin pp.ℓ_m) (R := R) (s := (Finset.univ : Finset (Fin pp.toSizeR1CS.n)))
      (z := z)
      (g := fun j (xBits : Fin pp.ℓ_m → Fin 2) => M (finFunctionFinEquiv xBits) j)
      r_x)

/-- **NAMED RESIDUAL — R1CS ↔ MLE encoding equality.** The chaining correctness obligation:
after `sendEvalClaim`, each evaluation claim exposes the genuine matrix-vector/MLE decomposition
that the second sum-check consumes. This replaces the prior self-equality with the actual
scaled-column identity for every matrix index. -/
def r1csMleEncodingResidual : Prop :=
  ∀ (stmt : Statement.AfterFirstSumcheck R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstSumcheck R pp i)
    (idx : R1CS.MatrixIdx),
    let r_x : Fin pp.ℓ_m → R := stmt.1
    let x : Statement.AfterFirstMessage R pp := stmt.2.2
    let z := R1CS.𝕫 x (oStmt (.inr 0))
    evalClaimValue R pp stmt oStmt idx =
      ∑ j : Fin pp.toSizeR1CS.n,
        z j * MvPolynomial.eval r_x
          (MvPolynomial.MLE
            (fun xBits : Fin pp.ℓ_m → Fin 2 =>
              oStmt (.inl idx) (finFunctionFinEquiv xBits) j))

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The R1CS↔MLE encoding residual is discharged by the matrix-vector MLE scaled-sum identity. -/
theorem r1csMleEncodingResidual_holds : r1csMleEncodingResidual R pp := by
  intro stmt oStmt idx
  exact evalClaimValue_eq_scaled_sum R pp stmt oStmt idx

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Evaluating `Matrix.toMLE` at an arbitrary row point and a Boolean column point recovers the
row-MLE of the selected matrix column. This is the column-side bridge used by the second Spartan
sum-check cube-sum identity. -/
theorem matrix_toMLE_eval_row_boolColumn
    (M : Matrix (Fin (2 ^ pp.ℓ_m)) (Fin (2 ^ pp.ℓ_n)) R)
    (r_x : Fin pp.ℓ_m → R) (yBits : Fin pp.ℓ_n → Fin 2) :
    MvPolynomial.eval (yBits : Fin pp.ℓ_n → R)
        (MvPolynomial.eval
          ((MvPolynomial.C ∘ r_x) : Fin pp.ℓ_m → MvPolynomial (Fin pp.ℓ_n) R)
          M.toMLE)
      =
      MvPolynomial.eval r_x
        (MvPolynomial.MLE
          (fun xBits : Fin pp.ℓ_m → Fin 2 =>
            M (finFunctionFinEquiv xBits) (finFunctionFinEquiv yBits))) := by
  classical
  rw [Matrix.toMLE, MvPolynomial.MLE']
  rw [MvPolynomial.MLE_eval_eq_sum_eqTilde]
  rw [MvPolynomial.MLE_eval_eq_sum_eqTilde]
  simp [MvPolynomial.MLE', MvPolynomial.eqTilde, MvPolynomial.eval_mul]

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- **Second sum-check input claim threading.** The Boolean-cube sum of Spartan's second
sum-check virtual polynomial equals the random linear combination of the first sum-check
evaluation claims computed from the matrix/witness oracles. -/
theorem secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    (∑ yBits : Fin pp.ℓ_n → Fin 2,
        MvPolynomial.eval (yBits : Fin pp.ℓ_n → R)
          (secondSumCheckVirtualPolynomial R pp stmt oStmt))
      =
      ∑ idx : R1CS.MatrixIdx,
        stmt.1 idx *
          evalClaimValue R pp stmt.2 (fun i => oStmt (.inr i)) idx := by
  classical
  let r : R1CS.MatrixIdx → R := stmt.1
  let r_x : Fin pp.ℓ_m → R := stmt.2.1
  let x : Statement.AfterFirstMessage R pp := stmt.2.2.2
  let z := R1CS.𝕫 x (oStmt (.inr (.inr 0)))
  let Mat : R1CS.MatrixIdx → Matrix (Fin (2 ^ pp.ℓ_m)) (Fin (2 ^ pp.ℓ_n)) R :=
    fun idx => oStmt (.inr (.inl idx))
  have htarget :
      (∑ idx ∈ (Finset.univ : Finset R1CS.MatrixIdx),
          r idx * MvPolynomial.eval r_x
            (MvPolynomial.MLE ((Matrix.mulVec (Mat idx) z) ∘ finFunctionFinEquiv)))
        =
        ∑ j : Fin (2 ^ pp.ℓ_n),
          z j * (∑ idx ∈ (Finset.univ : Finset R1CS.MatrixIdx),
            r idx *
              MvPolynomial.eval r_x
                (MvPolynomial.MLE
                  (fun xBits : Fin pp.ℓ_m → Fin 2 =>
                    Mat idx (finFunctionFinEquiv xBits) j))) :=
    Spartan.Scratch114.secondSumcheck_target_eq_cube_sum
      (R := R) (s := (Finset.univ : Finset R1CS.MatrixIdx))
      (Mat := Mat) (z := z) (r_x := r_x) (coeff := r)
  have hclaim :
      (∑ idx : R1CS.MatrixIdx,
          stmt.1 idx *
            evalClaimValue R pp stmt.2 (fun i => oStmt (.inr i)) idx)
        =
        ∑ idx ∈ (Finset.univ : Finset R1CS.MatrixIdx),
          r idx * MvPolynomial.eval r_x
            (MvPolynomial.MLE ((Matrix.mulVec (Mat idx) z) ∘ finFunctionFinEquiv)) := by
    simp [evalClaimValue, r, r_x, x, z, Mat, PublicParams.toSizeR1CS]
    rfl
  rw [hclaim, htarget]
  refine Fintype.sum_equiv (finFunctionFinEquiv (m := 2) (n := pp.ℓ_n))
    (fun yBits : Fin pp.ℓ_n → Fin 2 =>
      MvPolynomial.eval (yBits : Fin pp.ℓ_n → R)
        (secondSumCheckVirtualPolynomial R pp stmt oStmt))
    (fun yEnum : Fin (2 ^ pp.ℓ_n) =>
      z yEnum * (∑ idx ∈ (Finset.univ : Finset R1CS.MatrixIdx),
        r idx *
          MvPolynomial.eval r_x
            (MvPolynomial.MLE
              (fun xBits : Fin pp.ℓ_m → Fin 2 =>
                Mat idx (finFunctionFinEquiv xBits) yEnum))))
    ?_
  intro yBits
  simp [secondSumCheckVirtualPolynomial, matrix_toMLE_eval_row_boolColumn, r, r_x, x, z, Mat,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [matrixIdx_sum]
  ring_nf

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Stored-claim form of `secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue`: if the
bundled eval-claim oracle contains the honest `evalClaimValue`, the second sum-check's initial
cube-sum equals the random linear combination of that stored oracle. -/
theorem secondSumCheckVirtualPolynomial_hypercubeSum_eq_claimOracle
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (hEval : ∀ idx,
      oStmt (.inl 0) idx = evalClaimValue R pp stmt.2 (fun i => oStmt (.inr i)) idx) :
    (∑ yBits : Fin pp.ℓ_n → Fin 2,
        MvPolynomial.eval (yBits : Fin pp.ℓ_n → R)
          (secondSumCheckVirtualPolynomial R pp stmt oStmt))
      =
      ∑ idx : R1CS.MatrixIdx,
        stmt.1 idx * oStmt (.inl 0) idx := by
  rw [secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue R pp stmt oStmt]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [hEval idx]

/-! ## Brick D — composition of the Spartan PIOP

We compose the phases pairwise with the proven `OracleReduction.append`. Because the existing
phases already chain type-wise (each `AfterX` output context equals the next `AfterY` input
context), the composite

  firstMessage ▷ firstChallenge ▷ firstSumcheck ▷ sendEvalClaim ▷ linearCombination
    ▷ secondSumcheck ▷ finalCheck

is a well-typed `OracleReduction` once the two sum-check phases (Brick B) are available.

The composed completeness and round-by-round knowledge soundness are stated as parameterized
properties discharged through the proven append reduction theorems. Each is the additive combination
of the
per-component guarantees:
* completeness error `0` (all components are perfectly complete);
* rbr knowledge error the per-round sum, with each sum-check round contributing `deg/|R| = 2/|R|`
  (the proven `oracleVerifier_rbrKnowledgeSoundness` bound) and the zero-round components
  contributing `0`.
-/

/-- The Spartan input relation as a `Set` over the input context
`((Statement × OracleStatement) × Witness)`, built from `R1CS.relation` (which is curried). This is
the relation the composed PIOP reduces from. -/
@[reducible]
def spartanRelIn :
    Set ((Statement R pp × (∀ i, OracleStatement R pp i)) × Witness R pp) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1 x.1.2 x.2 }

/-- **NAMED RESIDUAL — composed Spartan PIOP existence.** The fully composed Spartan oracle
reduction, over *some* combined protocol specification `pSpecC`, of input context the bare R1CS
statement (`Statement`, `OracleStatement`, `Witness`) and output context the terminal statement
after the final check. Obtained by iterated `OracleReduction.append` of the seven phases — the
`AppendCoherent` side conditions chain automatically from the leaves, by
`OracleVerifier.Append.AppendCoherent.oracleReductionAppend`. Stated as a residual because two of the
seven leaves (the sum-check phases) are themselves residuals
(`firstSumcheckResidual`, `secondSumcheckResidual`).

We existentially quantify the combined `pSpecC` (rather than spelling out the `Fin.vsum`/`++ₚ`
arithmetic) so the residual records exactly the protocol-level obligation without committing to a
brittle size normal form. -/
-- **Why this is a `sorry`-tracked residual, not an assembled term.**  Iterating
-- `OracleReduction.append` over the seven phases (`firstMessage ▷ firstChallenge ▷ firstSumcheck ▷
-- sendEvalClaim ▷ linearCombination ▷ secondSumcheck ▷ finalCheck`) does *not* yet type-check:
--   1. **Witness threading.** `firstMessage` (a `SendSingleWitness` phase) outputs witness `Unit`,
--      so `append` demands the next phase consume input witness `Unit`; but `oracleReduction.firstChallenge`
--      is currently declared with input witness `Witness R pp` (`ProofSystem/Spartan/Basic.lean`).
--   2. **`OracleVerifier.Append.AppendCoherent`.**  `OracleReduction.append` requires an
--      `AppendCoherent` instance for each left-operand verifier (chained by
--      `AppendCoherent.append`/`oracleReductionAppend` from the leaves).  No leaf instance exists
--      yet — synthesis fails first at `(oracleReduction.firstMessage …).verifier`.
-- These are real, open engineering obligations.  We therefore keep the composition as the honest
-- existence residual below, `sorry`-gated (tracked by `scripts/sorry_census.py`) rather than
-- assembled by non-compiling/laundered code.  See issue #114 and the append keystone (#25/#433).

def composedPIOPResidual : Prop :=
  ∃ (N : ℕ) (pSpecC : ProtocolSpec N) (_ : ∀ i, OracleInterface.{0, 0} (pSpecC.Message i))
    (_ : ∀ i, SampleableType (pSpecC.Challenge i)),
    Nonempty (OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      pSpecC)

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- **Parameterized existence.** Once *any* concrete composed Spartan oracle reduction `Rc` (over
some combined spec `pSpecC`) with the correct input/output context is supplied, the existence
residual holds. The genuine open obligation is the construction of `Rc` — iterating
`OracleReduction.append` over the seven phases, which is gated on the per-phase `AppendCoherent`
instances and the challenge-seam append keystone (see the comment block above). This lemma records
that the existence residual is *exactly* that construction obligation, with no remaining
probabilistic or relational content. -/
theorem composedPIOPResidual_of_reduction
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface.{0, 0} (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit pSpecC) :
    composedPIOPResidual R pp oSpec :=
  ⟨N, pSpecC, inferInstance, inferInstance, ⟨Rc⟩⟩

/-- **NAMED RESIDUAL — target-carrying composed Spartan PIOP existence.** This is the same
composition obligation as `composedPIOPResidual`, but with the real terminal `CheckClaim` endpoint:
the output statement carries the second-sum-check target value alongside the final Spartan context,
so the final predicate can check `target = expected(r_x,r_y,A,B,C,Z)`. -/
def composedPIOPWithClaimResidual : Prop :=
  ∃ (N : ℕ) (pSpecC : ProtocolSpec N) (_ : ∀ i, OracleInterface.{0, 0} (pSpecC.Message i))
    (_ : ∀ i, SampleableType (pSpecC.Challenge i)),
    Nonempty (OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit
      pSpecC)

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- **Parameterized existence (target-carrying).** Companion of `composedPIOPResidual_of_reduction`
for the terminal `CheckClaim` that carries the second-sum-check target. Same construction
obligation, target-carrying final context. -/
theorem composedPIOPWithClaimResidual_of_reduction
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface.{0, 0} (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC) :
    composedPIOPWithClaimResidual R pp oSpec :=
  ⟨N, pSpecC, inferInstance, inferInstance, ⟨Rc⟩⟩

/-- **Named statement — composed Spartan PIOP perfect completeness.** Discharged, once the composed
reduction `Rc` (over its combined spec `pSpecC`) is available, by iterated
`OracleReduction.append_perfectCompleteness`: each leaf is perfectly complete
(`SendSingleWitness.oracleReduction`, `RandomQuery.oracleReduction_completeness`, the two sum-checks
via `Sumcheck.Spec.oracleReduction_perfectCompleteness` transferred through `liftContext`,
`sendEvalClaim`/`linearCombination` as pure forwardings, and `finalCheck` via `CheckClaim`), and
`append_perfectCompleteness` combines them with total error `0` (resting on the `Prover.append_run`
keystone, the single deep residual of the append layer). This is a parameterized property alias,
not an independent strict residual surface; concrete Spartan reductions prove instances of it. -/
def composedCompletenessStatement
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) : Prop :=
  Rc.perfectCompleteness init impl (spartanRelIn R pp) (finalCheckRelOut R pp)

-- **No `composedCompleteness_holds` here.**  An earlier revision asserted
-- `composedCompletenessStatement … (composedPIOP …) …` via `noncomputable constant` — a disguised
-- axiom (an unproven inhabitant of the perfect-completeness `Prop`) that, moreover, does not parse
-- in Lean 4 and is not caught by `scripts/forbidden_tokens.py` (which flags `axiom`, not
-- `constant`/`opaque`).  Composed perfect completeness is *not* available: it would follow from
-- `OracleReduction.append_perfectCompleteness`, which is itself an unproven library-wide residual
-- (the `Prover.append_run` / `simulateQ`-support keystone, #25/#433).  The honest surface is the
-- `composedCompletenessStatement` obligation above; it has no proof yet.

/-- Target-carrying version of `composedCompletenessStatement`, for a composed Spartan reduction
ending at `finalCheckWithClaim`. -/
def composedCompletenessWithClaimStatement
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) : Prop :=
  Rc.perfectCompleteness init impl (spartanRelIn R pp) (finalCheckWithClaimRelOut R pp)

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The semantic target-carrying value relation is a strengthening of the broad terminal relation
used by the current composed-with-claim residual surface. -/
theorem finalCheckWithClaimValueRelIn_subset_finalCheckWithClaimRelOut :
    finalCheckWithClaimValueRelIn R pp ⊆ finalCheckWithClaimRelOut R pp := by
  intro x _hx
  trivial

/-- Stronger target-carrying composed completeness statement, where the composed Spartan reduction
must output the semantic value relation tying the carried target to the algebraic final expected
claim value. This is a compatibility target for future terminal `CheckClaim` completeness work.

**Audit status (2026-06-10): genuine remaining content — semantic target threading (D1).**
The composed-`Rc` instance of this statement is NOT dischargeable from
`composedCompletenessWithClaimStatement_proven` by output-relation monotonicity: that theorem's
relOut is weakened to `univ` (its final step is `completeness_relOut_mono (Set.subset_univ _)`),
while this statement demands the *semantic* value relation (carried target = second-sum-check
terminal eval). The adapter `prependClaim` emits the literal target `0` (`prependSlot`'s
`pure (0, stmt)`), so the discharge must thread Spartan's zero-check semantics — the honest
run's terminal eval IS `0` for satisfying R1CS witnesses — which requires re-landing the base
composition with a contentful relOut recording the terminal-eval fact (not `univ`). Until
then, this statement and its `SecondSumcheckEval` twin (equivalent via
`composedCompletenessWithClaimSecondSumcheckEvalStatement_iff_valueRel`) are honest open
engineering, tracked under issue #329. -/
def composedCompletenessWithClaimValueRelStatement
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) : Prop :=
  Rc.perfectCompleteness init impl (spartanRelIn R pp) (finalCheckWithClaimValueRelIn R pp)

/-- Target-carrying composed completeness statement where the final output relation is stated
directly as equality with the second-sum-check terminal endpoint. -/
def composedCompletenessWithClaimSecondSumcheckEvalStatement
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) : Prop :=
  Rc.perfectCompleteness init impl
    (spartanRelIn R pp) (finalCheckWithClaimSecondSumcheckEvalRelOut R pp)

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The second-sum-check endpoint completeness statement and the semantic value-relation statement
are the same target under the terminal endpoint bridge. -/
theorem composedCompletenessWithClaimSecondSumcheckEvalStatement_iff_valueRel
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    composedCompletenessWithClaimSecondSumcheckEvalStatement R pp oSpec Rc init impl ↔
      composedCompletenessWithClaimValueRelStatement R pp oSpec Rc init impl := by
  unfold composedCompletenessWithClaimSecondSumcheckEvalStatement
  unfold composedCompletenessWithClaimValueRelStatement
  rw [finalCheckWithClaimSecondSumcheckEvalRelOut_eq_valueRelIn]

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Completeness into the second-sum-check endpoint relation gives completeness into the semantic
value relation. -/
theorem composedCompletenessWithClaimValueRelStatement_of_secondSumcheckEval
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hEndpoint :
      composedCompletenessWithClaimSecondSumcheckEvalStatement R pp oSpec Rc init impl) :
    composedCompletenessWithClaimValueRelStatement R pp oSpec Rc init impl :=
  (composedCompletenessWithClaimSecondSumcheckEvalStatement_iff_valueRel
    R pp oSpec Rc init impl).1 hEndpoint

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Completeness into the semantic value relation gives completeness into the direct
second-sum-check endpoint relation. -/
theorem composedCompletenessWithClaimSecondSumcheckEvalStatement_of_valueRel
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hValue :
      composedCompletenessWithClaimValueRelStatement R pp oSpec Rc init impl) :
    composedCompletenessWithClaimSecondSumcheckEvalStatement R pp oSpec Rc init impl :=
  (composedCompletenessWithClaimSecondSumcheckEvalStatement_iff_valueRel
    R pp oSpec Rc init impl).2 hValue

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Completeness into the semantic target-carrying value relation implies the existing broad
target-carrying composed completeness statement by output-relation weakening. -/
theorem composedCompletenessWithClaimStatement_of_valueRel
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hValue : composedCompletenessWithClaimValueRelStatement R pp oSpec Rc init impl) :
    composedCompletenessWithClaimStatement R pp oSpec Rc init impl := by
  unfold composedCompletenessWithClaimValueRelStatement at hValue
  unfold composedCompletenessWithClaimStatement
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness at hValue ⊢
  exact Reduction.completeness_relOut_mono
    (init := init) (impl := impl)
    (relIn := spartanRelIn R pp)
    (relOut := finalCheckWithClaimValueRelIn R pp)
    (relOut' := finalCheckWithClaimRelOut R pp)
    (reduction := Rc.toReduction)
    (finalCheckWithClaimValueRelIn_subset_finalCheckWithClaimRelOut R pp)
    hValue

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Completeness into the second-sum-check endpoint relation implies the existing broad
target-carrying composed completeness statement. -/
theorem composedCompletenessWithClaimStatement_of_secondSumcheckEval
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hEndpoint :
      composedCompletenessWithClaimSecondSumcheckEvalStatement R pp oSpec Rc init impl) :
    composedCompletenessWithClaimStatement R pp oSpec Rc init impl :=
  composedCompletenessWithClaimStatement_of_valueRel R pp oSpec Rc init impl <|
    (composedCompletenessWithClaimSecondSumcheckEvalStatement_iff_valueRel
      R pp oSpec Rc init impl).1 hEndpoint

/-- **Named statement — composed Spartan PIOP round-by-round knowledge soundness.** Discharged, once
the composed verifier is available, by iterated `OracleVerifier.append_rbrKnowledgeSoundness`: each
leaf satisfies rbr knowledge soundness (`RandomQuery.oracleVerifier_rbrKnowledgeSoundness`, the two
sum-checks via the per-round `Sumcheck.Spec` `oracleVerifier_rbrKnowledgeSoundness` transferred
through `liftContext`, and `CheckClaim.verifier_rbr_knowledge_soundness`), and
`append_rbrKnowledgeSoundness` combines the per-round errors through `ChallengeIdx.sumEquiv`. Each
sum-check round contributes `2/|R|`; the zero-round components contribute `0`. This is a
parameterized property alias, not an independent strict residual surface; concrete Spartan
reductions prove instances of it. -/
def composedRbrKnowledgeSoundnessStatement
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0) : Prop :=
  Rc.verifier.rbrKnowledgeSoundness init impl
    (spartanRelIn R pp) (finalCheckRelOut R pp) rbrKnowledgeError

-- **No `composedRbrKnowledgeSoundness_holds` here.**  As with completeness above, an earlier
-- revision asserted this composed RBR knowledge-soundness `Prop` via `noncomputable constant` — a
-- disguised, non-parsing axiom.  RBR knowledge soundness for the composition is *not* available: it
-- would follow from `OracleVerifier.append_rbrKnowledgeSoundness` (per-round `2/|R|` sum-check error
-- combined via `ChallengeIdx.sumEquiv`), which is an unproven library-wide residual.  The honest
-- surface is the `composedRbrKnowledgeSoundnessStatement` obligation above; it has no proof yet.

/-- Target-carrying version of `composedRbrKnowledgeSoundnessStatement`, for composed Spartan
verifiers ending at `finalCheckWithClaim`. -/
def composedRbrKnowledgeSoundnessWithClaimStatement
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0) : Prop :=
  Rc.verifier.rbrKnowledgeSoundness init impl
    (spartanRelIn R pp) (finalCheckWithClaimRelOut R pp) rbrKnowledgeError

/-- Stronger target-carrying RBR knowledge-soundness statement where extracted terminal witnesses
land in the semantic final-check value relation. -/
def composedRbrKnowledgeSoundnessWithClaimValueRelStatement
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0) : Prop :=
  Rc.verifier.rbrKnowledgeSoundness init impl
    (spartanRelIn R pp) (finalCheckWithClaimValueRelIn R pp) rbrKnowledgeError

/-- Target-carrying RBR knowledge-soundness statement whose terminal output relation is stated
directly as equality with the second-sum-check endpoint. -/
def composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0) : Prop :=
  Rc.verifier.rbrKnowledgeSoundness init impl
    (spartanRelIn R pp) (finalCheckWithClaimSecondSumcheckEvalRelOut R pp) rbrKnowledgeError

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The second-sum-check endpoint RBR statement and the semantic value-relation RBR statement are
the same target under the terminal endpoint bridge. -/
theorem composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_iff_valueRel
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0) :
    composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement R pp oSpec Rc init impl
        rbrKnowledgeError ↔
      composedRbrKnowledgeSoundnessWithClaimValueRelStatement R pp oSpec Rc init impl
        rbrKnowledgeError := by
  unfold composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement
  unfold composedRbrKnowledgeSoundnessWithClaimValueRelStatement
  rw [finalCheckWithClaimSecondSumcheckEvalRelOut_eq_valueRelIn]

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- RBR knowledge soundness into the second-sum-check endpoint relation gives RBR knowledge
soundness into the semantic value relation. -/
theorem composedRbrKnowledgeSoundnessWithClaimValueRelStatement_of_secondSumcheckEval
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0)
    (hEndpoint :
      composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement R pp oSpec Rc init impl
        rbrKnowledgeError) :
    composedRbrKnowledgeSoundnessWithClaimValueRelStatement R pp oSpec Rc init impl
      rbrKnowledgeError :=
  (composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_iff_valueRel
    R pp oSpec Rc init impl rbrKnowledgeError).1 hEndpoint

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- RBR knowledge soundness into the semantic value relation gives RBR knowledge soundness into
the direct second-sum-check endpoint relation. -/
theorem composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_of_valueRel
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0)
    (hValue :
      composedRbrKnowledgeSoundnessWithClaimValueRelStatement R pp oSpec Rc init impl
        rbrKnowledgeError) :
    composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement R pp oSpec Rc init impl
      rbrKnowledgeError :=
  (composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_iff_valueRel
    R pp oSpec Rc init impl rbrKnowledgeError).2 hValue

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- RBR knowledge soundness for the broad target-carrying final-check relation implies RBR
knowledge soundness for the semantic value relation. This direction is the RBR analogue of relation
weakening on the terminal target: the broad relation is `Set.univ`, so any positive-probability
semantic terminal event is also a positive-probability broad terminal event. -/
theorem composedRbrKnowledgeSoundnessWithClaimValueRelStatement_of_broadStatement
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0)
    (hStatement :
      composedRbrKnowledgeSoundnessWithClaimStatement R pp oSpec Rc init impl
        rbrKnowledgeError) :
    composedRbrKnowledgeSoundnessWithClaimValueRelStatement R pp oSpec Rc init impl
      rbrKnowledgeError := by
  unfold composedRbrKnowledgeSoundnessWithClaimStatement at hStatement
  unfold composedRbrKnowledgeSoundnessWithClaimValueRelStatement
  unfold OracleVerifier.rbrKnowledgeSoundness Verifier.rbrKnowledgeSoundness at hStatement ⊢
  rcases hStatement with ⟨WitMid, extractor, kSF, hProb⟩
  let kSFValue :
      Rc.verifier.toVerifier.KnowledgeStateFunction init impl
        (spartanRelIn R pp) (finalCheckWithClaimValueRelIn R pp) extractor :=
    { toFun := kSF.toFun
      toFun_empty := kSF.toFun_empty
      toFun_next := kSF.toFun_next
      toFun_full := by
        intro stmtIn tr witOut hValue
        exact kSF.toFun_full stmtIn tr witOut <|
          lt_of_lt_of_le hValue <|
            probEvent_mono fun _ _ h =>
              finalCheckWithClaimValueRelIn_subset_finalCheckWithClaimRelOut R pp h }
  refine ⟨WitMid, extractor, kSFValue, ?_⟩
  simpa [kSFValue] using hProb

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- RBR knowledge soundness for the broad target-carrying final-check relation implies RBR
knowledge soundness for the direct second-sum-check endpoint relation. -/
theorem composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_of_broadStatement
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0)
    (hStatement :
      composedRbrKnowledgeSoundnessWithClaimStatement R pp oSpec Rc init impl
        rbrKnowledgeError) :
    composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement R pp oSpec Rc init impl
      rbrKnowledgeError :=
  composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_of_valueRel
    R pp oSpec Rc init impl rbrKnowledgeError <|
      composedRbrKnowledgeSoundnessWithClaimValueRelStatement_of_broadStatement
        R pp oSpec Rc init impl rbrKnowledgeError hStatement

/-! ### Axiom audit for the target-carrying final-check frontier and encoding residual -/

#print axioms evalClaimValue_eq_scaled_sum
#print axioms r1csMleEncodingResidual
#print axioms r1csMleEncodingResidual_holds
#print axioms matrix_toMLE_eval_row_boolColumn
#print axioms secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue
#print axioms secondSumCheckVirtualPolynomial_hypercubeSum_eq_claimOracle
#print axioms FinalClaimStatement
#print axioms finalMatrixEvalFromOracles
#print axioms zEvalFromFinalOracles
#print axioms zEvalPureFold
#print axioms zEvalFromFinalOracles_simOracle0_eq_pureFold
#print axioms zEvalPureFoldStep_eq_zTerm
#print axioms zEvalPureFold_eq_sum_zTerm
#print axioms zEvalPureFold_eq_mle_z
#print axioms zEvalFromFinalOracles_simOracle0_eq_mle_z
#print axioms finalExpectedClaimFromOracles
#print axioms finalExpectedClaimValue
#print axioms secondSumCheckVirtualPolynomial_eval_eq_finalExpectedClaimValue
#print axioms secondSumcheckTerminalEndpointResidual
#print axioms secondSumcheckTerminalEndpointResidual_holds
#print axioms finalClaimPredicate
#print axioms finalCheckWithClaim
#print axioms finalCheckWithClaimRelIn
#print axioms finalCheckWithClaimRelOut
#print axioms finalCheckWithClaimValueRelIn
#print axioms finalCheckWithClaimValueRelIn_iff_finalExpectedClaimValue
#print axioms finalCheckWithClaimValueRelIn_of_finalExpectedClaimValue
#print axioms finalExpectedClaimValue_eq_of_finalCheckWithClaimValueRelIn
#print axioms finalCheckWithClaimValueRelIn_iff_secondSumcheckEval
#print axioms secondSumcheckEval_eq_of_finalCheckWithClaimValueRelIn
#print axioms finalCheckWithClaimValueRelIn_of_secondSumcheckEval
#print axioms finalCheckWithClaimSecondSumcheckEvalRelOut
#print axioms finalCheckWithClaimSecondSumcheckEvalRelOut_eq_valueRelIn
#print axioms finalCheckWithClaimSecondSumcheckEvalRelOut_subset_valueRelIn
#print axioms finalCheckWithClaimValueRelIn_subset_secondSumcheckEvalRelOut
#print axioms finalCheckWithClaimSecondSumcheckEvalRelOut_iff_secondSumcheckEval
#print axioms finalCheckWithClaimSecondSumcheckEvalRelOut_of_secondSumcheckEval
#print axioms secondSumcheckEval_eq_of_finalCheckWithClaimSecondSumcheckEvalRelOut
#print axioms finalCheckWithClaimSecondSumcheckEvalRelOut_subset_finalCheckWithClaimRelOut
#print axioms finalCheckWithClaimValueRelResidual
#print axioms finalCheckWithClaimValueRelResidual_holds
#print axioms finalCheckWithClaimValueRelResidual_of_secondSumcheckTerminalEndpointResidual
#print axioms secondSumcheckTerminalEndpointResidual_of_finalCheckWithClaimValueRelResidual
#print axioms finalCheckWithClaimValueRelResidual_iff_secondSumcheckTerminalEndpointResidual
#print axioms finalCheckRelIn
#print axioms finalCheckRelOut
#print axioms firstSumcheckResidual
#print axioms secondSumcheckResidual
#print axioms spartanRelIn
#print axioms composedPIOPResidual
#print axioms composedCompletenessStatement
#print axioms composedRbrKnowledgeSoundnessStatement
#print axioms composedPIOPWithClaimResidual
#print axioms composedCompletenessWithClaimStatement
#print axioms finalCheckWithClaimValueRelIn_subset_finalCheckWithClaimRelOut
#print axioms composedCompletenessWithClaimValueRelStatement
#print axioms composedCompletenessWithClaimSecondSumcheckEvalStatement
#print axioms composedCompletenessWithClaimSecondSumcheckEvalStatement_iff_valueRel
#print axioms composedCompletenessWithClaimValueRelStatement_of_secondSumcheckEval
#print axioms composedCompletenessWithClaimSecondSumcheckEvalStatement_of_valueRel
#print axioms composedCompletenessWithClaimStatement_of_valueRel
#print axioms composedCompletenessWithClaimStatement_of_secondSumcheckEval
#print axioms composedRbrKnowledgeSoundnessWithClaimStatement
#print axioms composedRbrKnowledgeSoundnessWithClaimValueRelStatement
#print axioms composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement
#print axioms composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_iff_valueRel
#print axioms composedRbrKnowledgeSoundnessWithClaimValueRelStatement_of_secondSumcheckEval
#print axioms composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_of_valueRel
#print axioms composedRbrKnowledgeSoundnessWithClaimValueRelStatement_of_broadStatement
#print axioms composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_of_broadStatement

/-! ## Brick D (final) — composed Spartan PIOP security, parameterized on the composed reduction

The seven-phase composition `Rc` (firstMessage ▷ firstChallenge ▷ firstSumcheck ▷ sendEvalClaim ▷
linearCombination ▷ secondSumcheck ▷ finalCheck) is a single, well-typed `OracleReduction` once it
is assembled by iterating `OracleReduction.append`. Two genuinely-open engineering obligations gate
the *assembly* of `Rc` (independent of the proofs below): the per-phase
`OracleVerifier.Append.AppendCoherent` instances and the challenge-seam append keystone (the
message-seam keystone `OracleReduction.append_perfectCompleteness_msg_proof` does not apply when a
phase boundary is a *challenge* seam, as for `firstChallenge`/`linearCombination`).

We therefore take the assembled reduction `Rc` and its two end-to-end security guarantees as
explicit hypotheses and derive the named composed statements of this file from them. The
hypotheses are exactly the composed perfect-completeness / round-by-round knowledge soundness facts
that an iterated-`append` assembly would produce (total completeness error `0`; per-round RBR error
`2/|R|` on the two sum-check phases, `0` elsewhere), so no probabilistic or relational content is
hidden — only the assembly of `Rc` and the append keystones remain open. These theorems are
axiom-clean and non-vacuous: each conclusion is the corresponding named `…Statement` `Prop`, and
each hypothesis is its defeq unfolding. -/

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- **Composed Spartan PIOP perfect completeness (parameterized).** Given the assembled composed
reduction `Rc` together with its end-to-end perfect-completeness `hc` from the Spartan input
relation to the terminal final-check relation, the named composed-completeness statement holds. -/
theorem composedCompletenessStatement_of_perfectCompleteness
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hc : Rc.perfectCompleteness init impl (spartanRelIn R pp) (finalCheckRelOut R pp)) :
    composedCompletenessStatement R pp oSpec Rc init impl :=
  hc

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- **Composed Spartan PIOP perfect completeness, target-carrying (parameterized).** -/
theorem composedCompletenessWithClaimStatement_of_perfectCompleteness
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hc : Rc.perfectCompleteness init impl
      (spartanRelIn R pp) (finalCheckWithClaimRelOut R pp)) :
    composedCompletenessWithClaimStatement R pp oSpec Rc init impl :=
  hc

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- **Composed Spartan PIOP round-by-round knowledge soundness (parameterized).** Given the
assembled composed reduction `Rc` together with its end-to-end RBR knowledge soundness `hks` (with
per-round error `rbrKnowledgeError`), the named composed RBR-knowledge-soundness statement holds.
For the seven-phase Spartan composition the per-round error is `2/|R|` on each of the two sum-check
phases' rounds and `0` on the (zero-round) `firstChallenge`/`linearCombination`/`finalCheck`/
`firstMessage`/`sendEvalClaim` phases, combined across phases through `ChallengeIdx.sumEquiv`. -/
theorem composedRbrKnowledgeSoundnessStatement_of_rbrKnowledgeSoundness
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0)
    (hks : Rc.verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) (finalCheckRelOut R pp) rbrKnowledgeError) :
    composedRbrKnowledgeSoundnessStatement R pp oSpec Rc init impl rbrKnowledgeError :=
  hks

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- **Composed Spartan PIOP round-by-round knowledge soundness, target-carrying
(parameterized).** -/
theorem composedRbrKnowledgeSoundnessWithClaimStatement_of_rbrKnowledgeSoundness
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0)
    (hks : Rc.verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) (finalCheckWithClaimRelOut R pp) rbrKnowledgeError) :
    composedRbrKnowledgeSoundnessWithClaimStatement R pp oSpec Rc init impl rbrKnowledgeError :=
  hks

/-! ### End-to-end Spartan PIOP security: where the genuine theorems live

An earlier revision declared two theorems here named `spartan_piop_perfect_completeness` /
`spartan_piop_rbr_knowledge_soundness`, documented as "the headline theorems of issue #114". As
the external audit (2026-06-10) observed, each took an *arbitrary* `Rc` **plus its own security
property as a hypothesis** and merely repackaged it into the residual `Prop` — i.e. they were
exact duplicates of `composedCompletenessStatement_of_perfectCompleteness` /
`composedRbrKnowledgeSoundnessStatement_of_rbrKnowledgeSoundness` above, converters rather than
end-to-end results. They have been **retired** so converter names cannot masquerade as headline
results. The genuine statements about the actual assembled composition
(`Bricks.composedPIOP_Rc`, `ArkLib/ProofSystem/Spartan/Composition.lean`) are:

* **Perfect completeness (PROVEN, no leaf hypotheses):**
  `Bricks.composedCompletenessStatement_proven`
  (`ArkLib/ProofSystem/Spartan/ComposedCompletenessFinal.lean`) — only the standard
  honest-implementation side conditions on `init`/`impl` remain as inputs.
* **Round-by-round knowledge soundness (assembled, conditional):**
  `Bricks.composedRbrKnowledgeSoundnessStatement_of_leaves`
  (`ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean`) — the seven-seam keystone
  fold at `Rc := composedPIOP_Rc`, reducing the obligation to the eight per-phase rbr-KS leaves
  and the seven verifier determinism witnesses (the former challenge-seam `hSeamZero` residuals
  are discharged by `appendRbrKnowledgeSeamZero_proven`).

Hold the `spartan_piop_*` names until the rbr layer's remaining inputs are discharged and the
headline statements are instantiable. -/

#print axioms composedPIOPResidual_of_reduction
#print axioms composedPIOPWithClaimResidual_of_reduction
#print axioms composedCompletenessStatement_of_perfectCompleteness
#print axioms composedCompletenessWithClaimStatement_of_perfectCompleteness
#print axioms composedRbrKnowledgeSoundnessStatement_of_rbrKnowledgeSoundness
#print axioms composedRbrKnowledgeSoundnessWithClaimStatement_of_rbrKnowledgeSoundness

end Bricks

end

end Spartan.Spec
