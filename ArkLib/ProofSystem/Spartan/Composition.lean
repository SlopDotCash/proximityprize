/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SpartanBricks

/-!
# The composed Spartan PIOP oracle reduction (issue #114, direct assembly)

This file discharges the two *existence* residuals
`Spartan.Spec.Bricks.composedPIOPResidual` and
`Spartan.Spec.Bricks.composedPIOPWithClaimResidual` from `ArkLib/ToMathlib/SpartanBricks.lean` by
*actually assembling* the fully-composed Spartan oracle reduction through iterated
`OracleReduction.append`, rather than leaving them as `sorry`-tracked existence obligations.

`composedPIOPResidual` asserts the existence of a fully-composed Spartan oracle reduction with input
context the bare R1CS instance `(Statement, OracleStatement, Witness)` and output context the
terminal `(FinalStatement, FinalOracleStatement, Unit)`, over *some* combined protocol spec. Its
companion `composedPIOPResidual_of_reduction` records that this existence holds as soon as *any*
concrete `Rc` of that type is supplied. We construct `Rc` by iterating `OracleReduction.append` over
the seven Spartan phases:

  firstMessage ▷ firstChallenge ▷ firstSumcheck ▷ sendEvalClaim ▷ linearCombination
              ▷ prependTarget ▷ secondSumcheck ▷ finalCheck

and the target-carrying variant adds a trailing `prependClaim` to land in
`FinalClaimStatement = R × FinalStatement`.

## Why the two documented blockers do not block

* **Witness threading** already lines up on the developed tree: `firstMessage` (a
  `SendSingleWitness` phase) outputs witness `Unit`, and every subsequent phase consumes/outputs
  `Unit`, so each `append` seam's witness types match definitionally. No coercion lens is needed.
* **`AppendCoherent` leaves.** `OracleReduction.append R₁ R₂` needs `AppendCoherent R₁.verifier`.
  With the chain **right-associated** (via `<|`), every left operand is a single phase (a *leaf*),
  so only the per-phase leaf instances are needed; those already exist for the six real phases
  (`instFirstMessageVerifierAppendCoherent`, …, `instSecondSumcheckVerifierAppendCoherent`). The
  composite `AppendCoherent` for any nested right operand is supplied automatically by
  `OracleVerifier.Append.AppendCoherent.oracleReductionAppend`. The new `prependRLCTarget` /
  `prependClaim` adapters carry their own immediate `inl`-shaped instances.

The only new ingredient is the 0-round (`!p[]`) honest statement adapter `prependRLCTarget`, bridging
`linearCombination`'s output statement `AfterLinearCombination` to `secondSumcheck`'s input statement
`R × AfterLinearCombination` (the leading `R` is the second sum-check's claimed target).  It reads the
bundled evaluation-claim oracle and carries the random linear combination required by the second
sum-check relation. `prependClaim` is its terminal analogue, prepending the final target slot to land in
`FinalClaimStatement`.

## Honesty

No `sorry`/`axiom`. `composedPIOPResidual` is purely a *typed-existence* statement, and the assembled
reduction uses the honest RLC-target adapter so the same term is suitable for the composed
perfect-completeness layer.
-/

open OracleComp OracleInterface ProtocolSpec Function

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 512
-- The bottom-up `++ₚ` instance restatements and the doc comments are naturally wide; suppress the
-- cosmetic long-line linter (this file is under `ProofSystem/`, outside the Data warning budget).
set_option linter.style.longLine false

namespace Spartan.Spec

noncomputable section

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι) [SampleableType R]

namespace Bricks

/-- `R1CS.MatrixIdx` is `VCVCompatible` (`Fintype` is derived in `SpartanBricks`; `Inhabited` and
`DecidableEq` are derived on the inductive). This makes `LinearCombinationChallenge R = MatrixIdx → R`
a `SampleableType` (via `instSampleableTypePiVCV`), needed for the combined-spec challenge instance of
the `linearCombination` phase in the append fold. -/
instance instVCVCompatibleMatrixIdx : VCVCompatible R1CS.MatrixIdx :=
  { (inferInstance : Fintype R1CS.MatrixIdx), (inferInstance : Inhabited R1CS.MatrixIdx) with
    type_decidableEq' := inferInstance }

/-- The `linearCombination` challenge `LinearCombinationChallenge R = R1CS.MatrixIdx → R` is a
`SampleableType`: it is a nonempty `Fintype` (`Fintype (MatrixIdx → R)` via `Pi.fintype`, nonempty
since `R` is), so `SampleableType.ofFintype` applies. Stated explicitly so the combined-spec
challenge instance of the `linearCombination` phase resolves in the append fold. -/
noncomputable instance instSampleableTypeLinearCombinationChallenge :
    SampleableType (LinearCombinationChallenge R) :=
  SampleableType.ofFintype (R1CS.MatrixIdx → R)

/-! ### A trivial 0-round "prepend a target slot" oracle reduction

Prepends a default scalar slot `R` to the statement over the empty protocol `!p[]`, forwarding the
oracle-statement family and `Unit` witness unchanged. Modeled on `CheckClaim.oracleReduction`; its
embedding is `inl`, so its `AppendCoherent` instance is immediate. This is the statement-reshaping
component that bridges output statements differing only by a leading `R` target slot. -/

variable {ιₛ : Type} (Stmt : Type) (OStmt : ιₛ → Type) [∀ i, OracleInterface (OStmt i)]

/-- The 0-round prepend-slot oracle prover: prepends `0 : R` to the statement and forwards all
oracles and the `Unit` witness unchanged. -/
def prependSlotProver :
    OracleProver oSpec Stmt OStmt Unit (R × Stmt) OStmt Unit !p[] where
  PrvState := fun _ => Stmt × (∀ i, OStmt i)
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun st => pure (((0, st.1), st.2), ())

/-- The 0-round prepend-slot oracle verifier: returns `(0, stmt)` and routes every output oracle from
the corresponding input oracle (`embed = inl`). -/
def prependSlotVerifier :
    OracleVerifier oSpec Stmt OStmt (R × Stmt) OStmt !p[] where
  verify := fun stmt _ => pure (0, stmt)
  embed := Embedding.inl
  hEq := by intro i; simp

/-- The 0-round prepend-slot oracle reduction. -/
def prependSlot :
    OracleReduction oSpec Stmt OStmt Unit (R × Stmt) OStmt Unit !p[] where
  prover := prependSlotProver (R := R) oSpec Stmt OStmt
  verifier := prependSlotVerifier (R := R) oSpec Stmt OStmt

instance instPrependSlotVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (prependSlotVerifier (R := R) oSpec Stmt OStmt) where
  hCohInl i k h := by
    simp only [prependSlotVerifier, Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [prependSlotVerifier, Function.Embedding.inl_apply] at h
    cases h

/-- **`prependTarget`**: the target-slot adapter between `linearCombination` and `secondSumcheck`,
bridging `AfterLinearCombination` to `R × AfterLinearCombination`. -/
def prependTarget :
    OracleReduction oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      !p[] :=
  prependSlot oSpec
    (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp)

instance instPrependTargetVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (prependTarget (R := R) pp oSpec).verifier :=
    inferInstanceAs (OracleVerifier.Append.AppendCoherent
      (prependSlotVerifier (R := R) oSpec
        (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp)))

/-! ### Honest RLC-target adapter -/

/-- The 0-round honest RLC-target oracle prover: emits the RLC
`∑ idx, r idx * v idx`, reading the bundled eval-claim oracle `.inl 0`. -/
noncomputable def prependRLCTargetProver :
    OracleProver oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombination R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] where
  PrvState := fun _ =>
    Statement.AfterLinearCombination R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun st =>
    pure (((∑ idx, st.1.1 idx * st.2 (.inl 0) idx, st.1), st.2), ())

/-- Direct combined-spec query of the bundled claim oracle `.inl 0` at index `idx`. -/
noncomputable def queryClaimDirect (idx : R1CS.MatrixIdx) :
    OracleComp (oSpec + ([OracleStatement.AfterLinearCombination R pp]ₒ
      + [(!p[] : ProtocolSpec 0).Message]ₒ)) R :=
  (OracleComp.lift <| OracleSpec.query
    (spec := oSpec + ([OracleStatement.AfterLinearCombination R pp]ₒ
      + [(!p[] : ProtocolSpec 0).Message]ₒ))
    (show (oSpec + ([OracleStatement.AfterLinearCombination R pp]ₒ
      + [(!p[] : ProtocolSpec 0).Message]ₒ)).Domain from
        Sum.inr (Sum.inl ⟨.inl 0, ⟨idx, ()⟩⟩)) :
    OracleComp _ R)

/-- One RLC-verifier query step: query the claim oracle, return `(idx, value)`. -/
noncomputable def rlcStep (idx : R1CS.MatrixIdx) :
    OptionT (OracleComp (oSpec + ([OracleStatement.AfterLinearCombination R pp]ₒ
      + [(!p[] : ProtocolSpec 0).Message]ₒ))) (R1CS.MatrixIdx × R) := do
  let v ← liftM (queryClaimDirect pp oSpec idx)
  pure (idx, v)

/-- The honest RLC-target verifier: queries the bundled claim oracle for each matrix index and
emits `(∑ idx, r idx * v idx, stmt)`. -/
noncomputable def prependRLCTargetVerifier :
    OracleVerifier oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp)
      (R × Statement.AfterLinearCombination R pp)
      (OracleStatement.AfterLinearCombination R pp) !p[] where
  verify := fun stmt _ => do
    let claims ← (liftM ((Finset.univ : Finset R1CS.MatrixIdx).toList.mapM (rlcStep pp oSpec)) :
      OptionT (OracleComp _) (List (R1CS.MatrixIdx × R)))
    let rlc : R := (claims.map (fun p => stmt.1 p.1 * p.2)).sum
    pure (rlc, stmt)
  embed := Embedding.inl
  hEq := by intro i; simp

/-- The honest RLC-target oracle reduction between `linearCombination` and the second sum-check. -/
noncomputable def prependRLCTarget :
    OracleReduction oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombination R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] where
  prover := prependRLCTargetProver pp oSpec
  verifier := prependRLCTargetVerifier pp oSpec

instance instPrependRLCTargetVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (prependRLCTargetVerifier (R := R) pp oSpec) where
  hCohInl i k h := by
    simp only [prependRLCTargetVerifier, Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [prependRLCTargetVerifier, Function.Embedding.inl_apply] at h
    cases h

instance instPrependRLCTargetReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent (prependRLCTarget (R := R) pp oSpec).verifier :=
  inferInstanceAs
    (OracleVerifier.Append.AppendCoherent (prependRLCTargetVerifier (R := R) pp oSpec))

/-- **`prependClaim`**: the terminal target-slot adapter after `finalCheck`, bridging `FinalStatement`
to the target-carrying `FinalClaimStatement = R × FinalStatement`. -/
def prependClaim :
    OracleReduction oSpec
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      (R × FinalStatement R pp) (FinalOracleStatement R pp) Unit
      !p[] :=
  prependSlot oSpec (FinalStatement R pp) (FinalOracleStatement R pp)

instance instPrependClaimVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (prependClaim (R := R) pp oSpec).verifier :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent
    (prependSlotVerifier (R := R) oSpec
      (FinalStatement R pp) (FinalOracleStatement R pp)))

/-- `AppendCoherent` for `(oracleReduction.sendEvalClaim …).verifier`. The Basic-file instance
`instSendEvalClaimVerifierAppendCoherent` is keyed on the raw `sendEvalClaimVerifier`, which is the
`.verifier` field of `oracleReduction.sendEvalClaim`; since that def is not reducible, instance
synthesis does not bridge the two, so we re-key it here (by `inferInstanceAs`, defeq). -/
instance instSendEvalClaimReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent (oracleReduction.sendEvalClaim R pp oSpec).verifier :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent (sendEvalClaimVerifier R pp oSpec))

/-- `AppendCoherent` for `(oracleReduction.linearCombination …).verifier`; re-keyed from the Basic
instance `instLinearCombinationVerifierAppendCoherent` (keyed on the raw `linearCombinationVerifier`)
by `inferInstanceAs` (defeq). -/
instance instLinearCombinationReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent (oracleReduction.linearCombination R pp oSpec).verifier :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent (linearCombinationVerifier R pp oSpec))

/-- `AppendCoherent` for the terminal `finalCheck` verifier (a `CheckClaim` oracle verifier with
`embed = inl`). Needed only for the target-carrying variant, where `finalCheck` becomes a *left*
operand of the trailing `prependClaim` append. (The analogous instance is `local` in
`Sumcheck/Spec/SingleRound.lean`, so we re-establish it here.) -/
instance instFinalCheckVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (finalCheck R pp oSpec).verifier where
  hCohInl i k h := by
    simp only [finalCheck, CheckClaim.oracleReduction, CheckClaim.oracleVerifier,
      Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [finalCheck, CheckClaim.oracleReduction, CheckClaim.oracleVerifier,
      Function.Embedding.inl_apply] at h
    cases h

/-! ### The composed Spartan oracle reduction

  Right-associated iterated `OracleReduction.append` over the seven phases (plus the `prependRLCTarget`
  empty adapter, and — for the target-carrying variant — the trailing `prependClaim`). Every left
operand is a leaf phase, so the required `AppendCoherent` instances are exactly the per-phase leaves;
the nested right composites get theirs automatically from `AppendCoherent.oracleReductionAppend`.

The combined protocol-spec is built right-associated from named suffixes `sfx2 … sfxFull`, with the
combined `OracleInterface (Message …)` / `SampleableType (Challenge …)` instances declared
**explicitly bottom-up** via `instOracleInterfaceMessageAppend` / `instSampleableTypeChallengeAppend`.
This restatement is required because (per the note in `Sumcheck/Spec/SingleRound.lean`) instance
synthesis does *not* automatically chain the `++ₚ` message/challenge instances through nested appends;
the leaves' instances must be threaded through each `++ₚ` level by hand. -/

-- Standalone message/challenge instances for the two *general* sum-check sub-specs (the seqCompose
-- form, whose instances are not auto-synthesized; cf. the same restatement need in `SingleRound`).
instance instSumcheck3Msg : ∀ i, OracleInterface ((Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Message i) :=
  inferInstance
instance instSumcheck3Chal : ∀ i, SampleableType ((Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Challenge i) :=
  inferInstance
instance instSumcheck2Msg : ∀ i, OracleInterface ((Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Message i) :=
  inferInstance
instance instSumcheck2Chal : ∀ i, SampleableType ((Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Challenge i) :=
  inferInstance

/-- suffix `[secondSumcheck ▷ finalCheck]` (= `sumcheck₂ ++ₚ !p[]`). -/
abbrev sfx6 := Sumcheck.Spec.pSpec R 2 pp.ℓ_n ++ₚ (!p[] : ProtocolSpec 0)
instance : ∀ i, OracleInterface ((sfx6 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := Sumcheck.Spec.pSpec R 2 pp.ℓ_n)
    (pSpec₂ := (!p[] : ProtocolSpec 0))
instance : ∀ i, SampleableType ((sfx6 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := Sumcheck.Spec.pSpec R 2 pp.ℓ_n)
    (pSpec₂ := (!p[] : ProtocolSpec 0))

/-- suffix `[prependRLCTarget ▷ …]` (= `!p[] ++ₚ sfx6`). -/
abbrev sfx5 := (!p[] : ProtocolSpec 0) ++ₚ sfx6 (R := R) pp
instance : ∀ i, OracleInterface ((sfx5 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := (!p[] : ProtocolSpec 0)) (pSpec₂ := sfx6 (R := R) pp)
instance : ∀ i, SampleableType ((sfx5 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := (!p[] : ProtocolSpec 0)) (pSpec₂ := sfx6 (R := R) pp)

/-- suffix `[linearCombination ▷ …]` (= `⟨V_to_P, LinComb⟩ ++ₚ sfx5`). -/
abbrev sfx4 :=
  (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) ++ₚ sfx5 (R := R) pp
instance : ∀ i, OracleInterface ((sfx4 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1))
    (pSpec₂ := sfx5 (R := R) pp)
instance : ∀ i, SampleableType ((sfx4 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1))
    (pSpec₂ := sfx5 (R := R) pp)

/-- suffix `[sendEvalClaim ▷ …]` (= `⟨P_to_V, BundledEvalClaim⟩ ++ₚ sfx4`). -/
abbrev sfx3 :=
  (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1) ++ₚ sfx4 (R := R) pp
instance : ∀ i, OracleInterface ((sfx3 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1)) (pSpec₂ := sfx4 (R := R) pp)
instance : ∀ i, SampleableType ((sfx3 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1)) (pSpec₂ := sfx4 (R := R) pp)

/-- suffix `[firstSumcheck ▷ …]` (= `sumcheck₃ ++ₚ sfx3`). -/
abbrev sfx2 := Sumcheck.Spec.pSpec R 3 pp.ℓ_m ++ₚ sfx3 (R := R) pp
instance : ∀ i, OracleInterface ((sfx2 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
    (pSpec₂ := sfx3 (R := R) pp)
instance : ∀ i, SampleableType ((sfx2 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
    (pSpec₂ := sfx3 (R := R) pp)

/-- suffix `[firstChallenge ▷ …]` (= `⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2`). -/
abbrev sfx1 :=
  (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) ++ₚ sfx2 (R := R) pp
instance : ∀ i, OracleInterface ((sfx1 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1)) (pSpec₂ := sfx2 (R := R) pp)
instance : ∀ i, SampleableType ((sfx1 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1)) (pSpec₂ := sfx2 (R := R) pp)

/-- The full combined protocol-spec of the composed Spartan PIOP (= `firstMessage ++ₚ sfx1`),
right-associated to match the `.append <|` fold. -/
abbrev composedPSpec :=
  (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1) ++ₚ sfx1 (R := R) pp
instance : ∀ i, OracleInterface ((composedPSpec (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1)) (pSpec₂ := sfx1 (R := R) pp)
instance : ∀ i, SampleableType ((composedPSpec (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1)) (pSpec₂ := sfx1 (R := R) pp)

/-- **The fully-composed Spartan PIOP oracle reduction** (issue #114): input context the bare R1CS
instance, terminal context `(FinalStatement, FinalOracleStatement, Unit)`. -/
def composedPIOP_Rc :
    OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      (composedPSpec (R := R) pp) :=
  (oracleReduction.firstMessage R pp oSpec).append <|
  (oracleReduction.firstChallenge R pp oSpec).append <|
    (firstSumcheckReduction pp oSpec).append <|
    (oracleReduction.sendEvalClaim R pp oSpec).append <|
    (oracleReduction.linearCombination R pp oSpec).append <|
    (prependRLCTarget pp oSpec).append <|
    (secondSumcheckReduction pp oSpec).append <|
    (finalCheck R pp oSpec)

/-- suffix `[finalCheck ▷ prependClaim]` (= `!p[] ++ₚ !p[]`), the terminal of the with-claim fold. -/
abbrev sfxC7 := (!p[] : ProtocolSpec 0) ++ₚ (!p[] : ProtocolSpec 0)
instance : ∀ i, OracleInterface ((sfxC7).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := (!p[] : ProtocolSpec 0))
    (pSpec₂ := (!p[] : ProtocolSpec 0))
instance : ∀ i, SampleableType ((sfxC7).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := (!p[] : ProtocolSpec 0))
    (pSpec₂ := (!p[] : ProtocolSpec 0))

/-- suffix `[secondSumcheck ▷ finalCheck ▷ prependClaim]` (= `sumcheck₂ ++ₚ sfxC7`). -/
abbrev sfxC6 := Sumcheck.Spec.pSpec R 2 pp.ℓ_n ++ₚ sfxC7
instance : ∀ i, OracleInterface ((sfxC6 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := Sumcheck.Spec.pSpec R 2 pp.ℓ_n) (pSpec₂ := sfxC7)
instance : ∀ i, SampleableType ((sfxC6 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := Sumcheck.Spec.pSpec R 2 pp.ℓ_n) (pSpec₂ := sfxC7)

/-- suffix `[prependRLCTarget ▷ …]` (= `!p[] ++ₚ sfxC6`). -/
abbrev sfxC5 := (!p[] : ProtocolSpec 0) ++ₚ sfxC6 (R := R) pp
instance : ∀ i, OracleInterface ((sfxC5 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := (!p[] : ProtocolSpec 0)) (pSpec₂ := sfxC6 (R := R) pp)
instance : ∀ i, SampleableType ((sfxC5 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := (!p[] : ProtocolSpec 0)) (pSpec₂ := sfxC6 (R := R) pp)

/-- suffix `[linearCombination ▷ …]` (= `⟨V_to_P, LinComb⟩ ++ₚ sfxC5`). -/
abbrev sfxC4 :=
  (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) ++ₚ sfxC5 (R := R) pp
instance : ∀ i, OracleInterface ((sfxC4 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1))
    (pSpec₂ := sfxC5 (R := R) pp)
instance : ∀ i, SampleableType ((sfxC4 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1))
    (pSpec₂ := sfxC5 (R := R) pp)

/-- suffix `[sendEvalClaim ▷ …]` (= `⟨P_to_V, BundledEvalClaim⟩ ++ₚ sfxC4`). -/
abbrev sfxC3 :=
  (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1) ++ₚ sfxC4 (R := R) pp
instance : ∀ i, OracleInterface ((sfxC3 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1)) (pSpec₂ := sfxC4 (R := R) pp)
instance : ∀ i, SampleableType ((sfxC3 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1)) (pSpec₂ := sfxC4 (R := R) pp)

/-- suffix `[firstSumcheck ▷ …]` (= `sumcheck₃ ++ₚ sfxC3`). -/
abbrev sfxC2 := Sumcheck.Spec.pSpec R 3 pp.ℓ_m ++ₚ sfxC3 (R := R) pp
instance : ∀ i, OracleInterface ((sfxC2 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
    (pSpec₂ := sfxC3 (R := R) pp)
instance : ∀ i, SampleableType ((sfxC2 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
    (pSpec₂ := sfxC3 (R := R) pp)

/-- suffix `[firstChallenge ▷ …]` (= `⟨V_to_P, FirstChallenge⟩ ++ₚ sfxC2`). -/
abbrev sfxC1 :=
  (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) ++ₚ sfxC2 (R := R) pp
instance : ∀ i, OracleInterface ((sfxC1 (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1))
    (pSpec₂ := sfxC2 (R := R) pp)
instance : ∀ i, SampleableType ((sfxC1 (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1))
    (pSpec₂ := sfxC2 (R := R) pp)

/-- The full combined protocol-spec of the target-carrying composed Spartan PIOP
(= `firstMessage ++ₚ sfxC1`). -/
abbrev composedPSpecWithClaim :=
  (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1) ++ₚ sfxC1 (R := R) pp
instance : ∀ i, OracleInterface ((composedPSpecWithClaim (R := R) pp).Message i) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1)) (pSpec₂ := sfxC1 (R := R) pp)
instance : ∀ i, SampleableType ((composedPSpecWithClaim (R := R) pp).Challenge i) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1)) (pSpec₂ := sfxC1 (R := R) pp)

/-- **The target-carrying fully-composed Spartan PIOP oracle reduction**: `composedPIOP_Rc` followed
by the terminal `prependClaim`, landing in `FinalClaimStatement`. -/
def composedPIOPWithClaim_Rc :
    OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit
      (composedPSpecWithClaim (R := R) pp) :=
  (oracleReduction.firstMessage R pp oSpec).append <|
  (oracleReduction.firstChallenge R pp oSpec).append <|
    (firstSumcheckReduction pp oSpec).append <|
    (oracleReduction.sendEvalClaim R pp oSpec).append <|
    (oracleReduction.linearCombination R pp oSpec).append <|
    (prependRLCTarget pp oSpec).append <|
    (secondSumcheckReduction pp oSpec).append <|
  (finalCheck R pp oSpec).append <|
  (prependClaim pp oSpec)

/-- **`composedPIOPResidual` discharged.** The composed reduction `composedPIOP_Rc` witnesses the
typed existence. -/
theorem composedPIOPResidual_holds_proof : composedPIOPResidual R pp oSpec :=
  composedPIOPResidual_of_reduction R pp oSpec (composedPIOP_Rc pp oSpec)

/-- **`composedPIOPWithClaimResidual` discharged.** The target-carrying composed reduction
`composedPIOPWithClaim_Rc` witnesses the typed existence with the terminal `CheckClaim` endpoint. -/
theorem composedPIOPWithClaimResidual_holds_proof : composedPIOPWithClaimResidual R pp oSpec :=
  composedPIOPWithClaimResidual_of_reduction R pp oSpec (composedPIOPWithClaim_Rc pp oSpec)

#print axioms composedPIOP_Rc
#print axioms composedPIOPWithClaim_Rc
#print axioms composedPIOPResidual_holds_proof
#print axioms composedPIOPWithClaimResidual_holds_proof

end Bricks

end

end Spartan.Spec
