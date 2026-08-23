/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessProof

/-!
# Perfect completeness of sequential composition for **oracle** reductions (message seam)

`AppendPerfectCompletenessProof.lean` proves the genuine `Reduction`-level keystone
`Reduction.append_perfectCompleteness_msg_proof`: for a message seam, perfect completeness of
`R₁.append R₂` follows from the two component perfect-completenesses. That keystone is on *plain*
reductions.

The ring-switching / BCS consumers compose **oracle** reductions (`OracleReduction.append`, which
appends the underlying `OracleVerifier`s via the routing of `OracleVerifier.Append.verify`). This
file bridges the keystone to the oracle setting.

`OracleReduction.perfectCompleteness oR` is *definitionally* `Reduction.perfectCompleteness
oR.toReduction` (`Security/Basic.lean`). The provers of `(R₁.append R₂).toReduction` and
`R₁.toReduction.append R₂.toReduction` are definitionally equal (both are
`Prover.append R₁.prover R₂.prover`). The *only* remaining content is the **verifier**-side
equality

  `(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`,

i.e. that running the appended oracle-verifier's combined `simOracle2` over the joint transcript
factors as the two component `toVerifier` runs over the split transcript (the verifier analogue of
`Prover.append_run`). We expose this as the single named residual
`OracleReduction.appendToReductionResidual` and discharge the oracle-level keystone modulo it. This
isolates the exact deep dependency as one concrete equation rather than an opaque probabilistic
completeness claim.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {m n : ℕ}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Named residual** isolating the verifier-side `toVerifier`/`append` fusion.

The `Verifier` image of an appended oracle reduction equals the append of the `Verifier` images.
The provers are definitionally equal, so this single equation is the entire remaining content of the
oracle-level append perfect-completeness (the verifier analogue of `Prover.append_run`). Honest
verifiers route their oracle queries faithfully, so for concrete protocols this is expected to hold
on the nose; we keep it named so downstream code can supply it as a small, concrete obligation. -/
def appendToReductionResidual
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) : Prop :=
  (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction

omit Oₛ₃ in
/-- **Oracle-level perfect-completeness keystone (message seam).**

Perfect completeness of `R₁.append R₂` for oracle reductions, from the two component
perfect-completenesses, the message-seam direction facts, `NeverFail`/support-faithfulness, and the
single named verifier bridge `appendToReductionResidual`. Pure pass-through to the proven
`Reduction.append_perfectCompleteness_msg_proof` once the bridge collapses `(R₁.append R₂).toReduction`
to `R₁.toReduction.append R₂.toReduction`. -/
theorem append_perfectCompleteness_msg_proof
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftM q : OracleComp oSpec β))
    (hBridge : appendToReductionResidual R₁ R₂)
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change Reduction.perfectCompleteness init impl rel₁ rel₃ (R₁.append R₂).toReduction
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from hBridge]
  exact Reduction.append_perfectCompleteness_msg_proof
    R₁.toReduction R₂.toReduction h₁ h₂ hn hDir hDir₂ hInit hImplSupp

/-! ## Sharpening the residual: it is exactly a per-input `verify` factoring

The named residual `appendToReductionResidual` is stated as an equation between two `Reduction`s.
The two lemmas below peel that down to its irreducible content. Since `toReduction` packages the
(identical) appended prover with `verifier.toVerifier`, the residual is equivalent to the pure
verifier-fusion equation, which in turn is equivalent to a per-input/per-transcript `verify`
equality. The latter is precisely the `simulateQ`-factoring obligation — the verifier analogue of
`Prover.append_run` — so any consumer can discharge the keystone by proving that one equation. -/

omit [oSpec.Fintype] [oSpec.Inhabited] Oₛ₃
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **The append keystone residual reduces to the pure verifier-fusion equation.** Since
`toReduction R = ⟨R.prover, R.verifier.toVerifier⟩` and the appended provers are *identical*
(`Prover.append R₁.prover R₂.prover` on both sides), `appendToReductionResidual` is logically
equivalent to the single equation
`(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`. This
strips the reduction-packaging noise, isolating the exact remaining content as a `Verifier`-only
equation. -/
theorem appendToReductionResidual_iff_verifier
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
    appendToReductionResidual R₁ R₂ ↔
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁)
          R₁.verifier R₂.verifier).toVerifier
        = Verifier.append R₁.verifier.toVerifier R₂.verifier.toVerifier := by
  unfold appendToReductionResidual OracleReduction.toReduction OracleReduction.append
    Reduction.append
  constructor
  · intro h
    exact (Reduction.mk.injEq _ _ _ _).mp h |>.2
  · intro h
    rw [Reduction.mk.injEq]
    exact ⟨rfl, h⟩

omit [oSpec.Fintype] [oSpec.Inhabited] Oₛ₃
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **The verifier-fusion equation reduces to a per-input `verify` equation.** Combined with
`appendToReductionResidual_iff_verifier`, this pins the *entire* remaining content of the
oracle-level append perfect-completeness keystone to: for every input `(stmt, oStmt)` and every
`transcript`, the appended oracle-verifier's `toVerifier.verify` (one `simulateQ` over the combined
`simOracle2` of `oStmt` and the joint messages) equals the two-stage composite `V₁.toVerifier` then
`V₂.toVerifier` (two `simulateQ`s over the split messages). That `simulateQ`-factoring is the sole
deep obligation — the verifier analogue of `Prover.append_run`. -/
theorem verifier_append_eq_iff_verify
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
    (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).toVerifier
        = Verifier.append V₁.toVerifier V₂.toVerifier ↔
      ∀ (x : Stmt₁ × ∀ i, OStmt₁ i) (t : FullTranscript (pSpec₁ ++ₚ pSpec₂)),
        (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).toVerifier.verify x t
          = (Verifier.append V₁.toVerifier V₂.toVerifier).verify x t := by
  constructor
  · intro h x t; rw [h]
  · intro h
    cases hL : (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).toVerifier
    cases hR : Verifier.append V₁.toVerifier V₂.toVerifier
    congr 1
    funext x t
    have := h x t
    rw [hL, hR] at this
    exact this

end OracleReduction
