/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.OracleCompleteness
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracle

/-!
# Verifier fusion and the LogUp / Sumcheck bridge (#13, #25, #433)

`OracleVerifier.BinaryVerifierFusion` packages the equality between the materialized append of
two oracle verifiers and the append of their materialized verifiers. The generic lemmas retain
the downstream interfaces for binary and sequential verifier fusion.

Canonical Sumcheck uses a dedicated oracle verifier. Its materialization equality
`Sumcheck.Spec.oracleReduction_toReduction` supplies the exact `hBridge` consumed by LogUp.
The historical bridge theorem retains its binary and per-round arguments for existing callers.

The per-round bridge `hPerRound`
(`(SingleRound.oracleReduction i).toReduction = SingleRound.reduction i`) also holds
unconditionally: canonical `SingleRound.oracleReduction_toReduction`, restated below under its
downstream name `SingleRound.oracleReduction_toReduction_eq_reduction`. It is not a mere
`liftContext`-commutation fact: it also asserts that the oracle round verifier and the plain round
verifier read the same data, which holds for the canonical message-reading verifiers of
`Sumcheck/Spec/SingleRound.lean`. (An earlier downstream oracle verifier ignored the message and
re-checked the input claim directly; for that verifier `hPerRound` was false. That verifier is
retired.)
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}

/-- **Named residual (★): the single binary verifier-fusion law**, stated *fully polymorphically*
over all statement / oracle-statement / protocol data. For any two appendable oracle verifiers, the
`toVerifier` image of their `append` equals the `append` of their `toVerifier` images. This is the
verifier analogue of `Prover.append_run`; its per-input/per-transcript content is exactly the
`simulateQ`-factoring isolated by `OracleReduction.verifier_append_eq_iff_verify`. We keep it as the
one explicit deep hypothesis from which the full `seqCompose` fusion follows.

It is phrased as a universally-quantified `Prop` so that the `seqCompose` induction can instantiate it
on the head verifier against the (re-typed) `seqCompose`d tail at each step. -/
def BinaryVerifierFusion (oSpec : OracleSpec ι) : Prop :=
  ∀ {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface.{0, 0} (OStmt₁ i)]
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface.{0, 0} (OStmt₂ i)]
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [_Oₛ₃ : ∀ i, OracleInterface.{0, 0} (OStmt₃ i)]
    {p q : ℕ} {pSpec₁ : ProtocolSpec p} {pSpec₂ : ProtocolSpec q}
    [Oₘ₁ : ∀ i, OracleInterface.{0, 0} (pSpec₁.Message i)]
    [_Oₘ₂ : ∀ i, OracleInterface.{0, 0} (pSpec₂.Message i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂),
    (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).toVerifier
      = Verifier.append V₁.toVerifier V₂.toVerifier

/-- **`BinaryVerifierFusion` is exactly the per-pair, per-input `verify`-factoring obligation.**

This pins down precisely what the named residual asks for: for *every* appendable pair `V₁`, `V₂` and
*every* input/transcript, the appended oracle-verifier's `toVerifier.verify` equals the two-stage
composite. By `OracleReduction.verifier_append_eq_iff_verify`, that per-input equality is equivalent
to the `Verifier`-level equation in `BinaryVerifierFusion`. So `BinaryVerifierFusion` is neither
vacuous nor stronger than the upstream-isolated deep core — it is the universally-quantified
`simulateQ`-factoring (the verifier analogue of `Prover.append_run`). -/
theorem binaryVerifierFusion_of_verify (oSpec : OracleSpec ι)
    (hVerify :
      ∀ {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
        [Oₛ₁ : ∀ i, OracleInterface.{0, 0} (OStmt₁ i)]
        {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
        [Oₛ₂ : ∀ i, OracleInterface.{0, 0} (OStmt₂ i)]
        {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
        [_Oₛ₃ : ∀ i, OracleInterface.{0, 0} (OStmt₃ i)]
        {p q : ℕ} {pSpec₁ : ProtocolSpec p} {pSpec₂ : ProtocolSpec q}
        [Oₘ₁ : ∀ i, OracleInterface.{0, 0} (pSpec₁.Message i)]
        [_Oₘ₂ : ∀ i, OracleInterface.{0, 0} (pSpec₂.Message i)]
        (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

        (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
        (x : Stmt₁ × ∀ i, OStmt₁ i) (t : FullTranscript (pSpec₁ ++ₚ pSpec₂)),
        (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).toVerifier.verify x t
          = (Verifier.append V₁.toVerifier V₂.toVerifier).verify x t) :
    BinaryVerifierFusion oSpec := by
  intro Stmt₁ ιₛ₁ OStmt₁ Oₛ₁ Stmt₂ ιₛ₂ OStmt₂ Oₛ₂ Stmt₃ ιₛ₃ OStmt₃ Oₛ₃
    p q pSpec₁ pSpec₂ Oₘ₁ Oₘ₂ V₁ V₂
  exact (OracleReduction.verifier_append_eq_iff_verify (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁)
    V₁ V₂).mpr (fun x t => hVerify V₁ V₂ x t)

/-- Historical sequential verifier fusion, supplied by canonical
`OracleVerifier.seqCompose_toVerifier`. -/
theorem seqCompose_toVerifier_of_binary (_hBinaryFusion : BinaryVerifierFusion oSpec) {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Oₛ : ∀ i, ∀ j, OracleInterface.{0, 0} (OStmt i j))
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (Oₘ : ∀ i, ∀ j, OracleInterface.{0, 0} ((pSpec i).Message j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
     :
    (OracleVerifier.seqCompose (Oₛ := Oₛ) (Oₘ := Oₘ) Stmt OStmt V ).toVerifier =
      Verifier.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier) :=
  OracleVerifier.seqCompose_toVerifier Stmt OStmt V

end OracleVerifier

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι}

/-- **The `Reduction`-level fusion from the verifier fusion.** Since `toReduction` packages the
*identical* `seqCompose`d prover with `verifier.toVerifier`, and `Reduction.seqCompose` packages the
same prover with `Verifier.seqCompose`, the `Reduction`-level equation
`(OracleReduction.seqCompose …).toReduction = Reduction.seqCompose …` is the verifier fusion plus a
`rfl` prover side. -/
theorem seqCompose_toReduction_of_verifier {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))

    (hVerifier :
      (OracleVerifier.seqCompose Stmt OStmt (fun i => (R i).verifier)).toVerifier =
        Verifier.seqCompose (fun i => Stmt i × (∀ j, OStmt i j))
          (fun i => (R i).verifier.toVerifier)) :
    (OracleReduction.seqCompose Stmt OStmt Wit R).toReduction =
      Reduction.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit
        (fun i => (R i).toReduction) := by
  -- Unfold both reductions to their (prover, verifier) pairs.
  unfold OracleReduction.toReduction OracleReduction.seqCompose Reduction.seqCompose
  -- The prover field is definitionally identical (`OracleProver.seqCompose = Prover.seqCompose`),
  -- and `(R i).toReduction.prover = (R i).prover`; so only the verifier field needs `hVerifier`.
  refine Reduction.ext rfl ?_
  -- `(R i).toReduction.verifier = (R i).verifier.toVerifier`, definitionally.
  exact hVerifier

end OracleReduction

namespace Sumcheck.Spec

variable {R : Type} [CommSemiring R] [SampleableType R] [DecidableEq R] [Fintype R] [Inhabited R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]

omit [Fintype R] [Inhabited R] [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)] in
/-- **The per-round single-round bridge `hPerRound` holds.** Downstream name for canonical
`SingleRound.oracleReduction_toReduction`: the oracle round verifier and the plain round verifier
both check the prover message's `D`-sum and take the new target from the message at the
challenge. -/
theorem SingleRound.oracleReduction_toReduction_eq_reduction (i : Fin n) :
    (SingleRound.oracleReduction R n deg D oSpec i).toReduction =
      SingleRound.reduction R n deg D oSpec i :=
  SingleRound.oracleReduction_toReduction R n deg D oSpec i

omit [Fintype R] [Inhabited R] [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)] in
/-- The historical Sumcheck `hBridge`, supplied by `oracleReduction_toReduction`. The binary-fusion
and per-round arguments are retained only for existing callers and are not used. -/
theorem oracleReductionToReductionResidual_of_binary
    (hBinaryFusion : OracleVerifier.BinaryVerifierFusion oSpec)
    (hPerRound : ∀ i, (SingleRound.oracleReduction R n deg D oSpec i).toReduction =
      SingleRound.reduction R n deg D oSpec i) :
    oracleReductionToReductionResidual R deg D n oSpec :=
  oracleReduction_toReduction R deg D n oSpec

end Sumcheck.Spec

#print axioms OracleVerifier.binaryVerifierFusion_of_verify
#print axioms OracleVerifier.seqCompose_toVerifier_of_binary
#print axioms OracleReduction.seqCompose_toReduction_of_verifier
#print axioms Sumcheck.Spec.oracleReductionToReductionResidual_of_binary
#print axioms Sumcheck.Spec.SingleRound.oracleReduction_toReduction_eq_reduction
