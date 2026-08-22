/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.OracleCompleteness
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracle

/-!
# Discharging the `hBridge` / `hAppend` keystones for LogUp / Sumcheck (#13, #25, #433)

This file attacks the generic verifier-fusion keystone that sits under the `hBridge` hypothesis of
`Sumcheck.Spec.oracleReduction_perfectCompleteness` (in `Sumcheck/Spec/OracleCompleteness.lean`) and
under the `appendToReductionResidual` (`hBridge`) of
`OracleReduction.append_perfectCompleteness_msg_proof`.

## The reduction chain

`Sumcheck.Spec.oracleReductionToReductionResidual` is the single equation

  `(oracleReduction R deg D n oSpec).toReduction = reduction R deg D n oSpec`.

Both sides are `seqCompose`s of the per-round components, with *definitionally equal provers*. So the
whole content is the verifier-side fusion

  `(OracleVerifier.seqCompose … V).toVerifier
      = Verifier.seqCompose … (fun i => (V i).toVerifier)`.

`OracleVerifier.seqCompose` is, by `seqCompose_succ`, an iterated binary `OracleVerifier.append`.
The binary fusion law

  `(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`     (★)

is the verifier analogue of `Prover.append_run`; its per-input/per-transcript content is exactly the
`simulateQ`-factoring isolated by `OracleReduction.verifier_append_eq_iff_verify`. We **prove the
inductive reduction**: given (★) at every round (as the explicit named hypothesis `hBinaryFusion`),
the full `seqCompose` fusion holds for all round counts — by induction over the round count `m`,
mirroring the proven `OracleVerifier.seqCompose'_appendCoherent` skeleton. The base case is closed by
`OracleVerifier.id_toVerifier`; the successor case glues `(★)` for the head with the induction
hypothesis for the tail.

This turns the genuinely-deep, *unbounded-round* keystone into the genuinely-deep, *single-binary*
keystone `(★)` — which is itself fully isolated to a per-query `simulateQ` equation by the upstream
brick. Downstream, the Sumcheck bridge `oracleReductionToReductionResidual` and the oracle-level
`appendToReductionResidual` are derived from `(★)` with no further obligation.

## What is proven vs. left as a named hypothesis

* `OracleVerifier.seqCompose_toVerifier_of_binary` — **PROVEN** by induction: the unbounded-round
  verifier fusion from the binary fusion `BinaryVerifierFusion`.
* `OracleReduction.seqCompose_toReduction_of_verifier` — **PROVEN**: the `Reduction`-level fusion
  (`(OracleReduction.seqCompose …).toReduction = Reduction.seqCompose …`) from the verifier fusion
  (the prover side is `rfl`).
* `Sumcheck.Spec.oracleReductionToReductionResidual_of_binary` — **PROVEN**: the concrete Sumcheck
  `hBridge`, from `BinaryVerifierFusion` together with the per-round single-round bridge
  `(SingleRound.oracleReduction i).toReduction = SingleRound.reduction i`.
* `OracleVerifier.BinaryVerifierFusion` — the single remaining **named hypothesis** `(★)`: the binary
  verifier-fusion law. By `OracleReduction.appendToReductionResidual_iff_verifier` /
  `verifier_append_eq_iff_verify`, it is exactly the per-input `simulateQ`-factoring — the verifier
  analogue of `Prover.append_run`. This is the irreducible deep core; we keep it named.
* `hPerRound` — the per-round single-round bridge, a `liftContext`-commutation fact orthogonal to the
  seqCompose fusion; kept as a named hypothesis of the Sumcheck theorem.
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
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface.{0, 0} (OStmt₃ i)]
    {p q : ℕ} {pSpec₁ : ProtocolSpec p} {pSpec₂ : ProtocolSpec q}
    [Oₘ₁ : ∀ i, OracleInterface.{0, 0} (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface.{0, 0} (pSpec₂.Message i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [c₁ : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
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
        [Oₛ₃ : ∀ i, OracleInterface.{0, 0} (OStmt₃ i)]
        {p q : ℕ} {pSpec₁ : ProtocolSpec p} {pSpec₂ : ProtocolSpec q}
        [Oₘ₁ : ∀ i, OracleInterface.{0, 0} (pSpec₁.Message i)]
        [Oₘ₂ : ∀ i, OracleInterface.{0, 0} (pSpec₂.Message i)]
        (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
        [c₁ : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
        (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
        (x : Stmt₁ × ∀ i, OStmt₁ i) (t : FullTranscript (pSpec₁ ++ₚ pSpec₂)),
        (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).toVerifier.verify x t
          = (Verifier.append V₁.toVerifier V₂.toVerifier).verify x t) :
    BinaryVerifierFusion oSpec := by
  intro Stmt₁ ιₛ₁ OStmt₁ Oₛ₁ Stmt₂ ιₛ₂ OStmt₂ Oₛ₂ Stmt₃ ιₛ₃ OStmt₃ Oₛ₃
    p q pSpec₁ pSpec₂ Oₘ₁ Oₘ₂ V₁ c₁ V₂
  exact (OracleReduction.verifier_append_eq_iff_verify (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁)
    V₁ V₂).mpr (fun x t => hVerify V₁ V₂ x t)

/-- **The unbounded-round verifier fusion from the binary fusion.**

By induction over the round count `m`: at `m = 0` the `seqCompose` is `OracleVerifier.id`, closed by
`OracleVerifier.id_toVerifier`; at `m + 1` the `seqCompose` unfolds (`seqCompose_succ`) to a binary
`append` of the head `V 0` with the tail's `seqCompose`, and we glue the head binary fusion (an
instance of `hBinaryFusion`) with the induction hypothesis applied to the tail. -/
theorem seqCompose_toVerifier_of_binary (hBinaryFusion : BinaryVerifierFusion oSpec) {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Oₛ : ∀ i, ∀ j, OracleInterface.{0, 0} (OStmt i j))
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (Oₘ : ∀ i, ∀ j, OracleInterface.{0, 0} ((pSpec i).Message j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)) :
    (OracleVerifier.seqCompose (Oₛ := Oₛ) (Oₘ := Oₘ) Stmt OStmt V (coh := coh)).toVerifier =
      Verifier.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier) := by
  induction m with
  | zero =>
    -- `seqCompose = OracleVerifier.id`, `Verifier.seqCompose = Verifier.id`.
    show (OracleVerifier.seqCompose Stmt OStmt V).toVerifier = Verifier.id
    rw [OracleVerifier.seqCompose_zero Stmt OStmt V]
    exact OracleVerifier.id_toVerifier
  | succ m ih =>
    -- Tail coherence (re-indexed leaf coherences).
    letI tailCoh :
        ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := (fun i => Oₛ (Fin.succ i)) i.castSucc)
          (Oₛ₂ := (fun i => Oₛ (Fin.succ i)) i.succ) (Oₘ₁ := (fun i => Oₘ (Fin.succ i)) i)
          (V (Fin.succ i)) := fun i => coh i.succ
    -- Head coherence for the binary append of `V 0` onto the tail's `seqCompose`.
    letI headCoh :
        OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₘ₁ := Oₘ 0) (V 0) :=
      coh 0
    -- Induction hypothesis on the tail.
    have ihTail := ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (fun i => Oₛ (Fin.succ i))
      (fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i)) tailCoh
    -- The head binary fusion against the tail's `seqCompose`.
    have hHead := hBinaryFusion (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₛ₃ := Oₛ (Fin.last (m + 1)))
      (Oₘ₁ := Oₘ 0)
      (V 0) (c₁ := headCoh)
      (OracleVerifier.seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
        (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i))
        (fun i => V (Fin.succ i)) (coh := tailCoh))
    -- Unfold both `seqCompose`s to their head/tail `append`s, then glue.
    rw [OracleVerifier.seqCompose_succ Stmt OStmt (Oₛ := Oₛ) (Oₘ := Oₘ) V (coh := coh),
        Verifier.seqCompose_succ (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier)]
    -- LHS = `((V 0).append tail).toVerifier`; chain the head binary fusion (`hHead`, matched up to
    -- the defeq `letI` coherence instances) with the tail IH (`ihTail`) under `(V 0).toVerifier ▸ ·`.
    exact hHead.trans (congrArg (Verifier.append (V 0).toVerifier) ihTail)

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
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (R i).verifier]
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
  {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]

omit [Fintype R] [Inhabited R] [oSpec.Fintype] [oSpec.Inhabited] in
/-- **The Sumcheck `hBridge` from the per-round binary verifier fusion + per-round bridge.**

`oracleReductionToReductionResidual` is `(oracleReduction).toReduction = reduction`. Both are
`seqCompose`s of the per-round Sumcheck components; the prover side is `rfl`. The residual factors as:

1. the verifier-side `seqCompose` fusion `(OracleReduction.seqCompose …).toReduction =
   Reduction.seqCompose (fun i => (oracleReduction i).toReduction)`, supplied by
   `OracleReduction.seqCompose_toReduction_of_verifier` ∘ `seqCompose_toVerifier_of_binary` from the
   binary fusion `hBinaryFusion` (this is the deep, unbounded-round verifier-fusion content); and
2. the per-round bridge `(SingleRound.oracleReduction i).toReduction = SingleRound.reduction i`,
   taken as `hPerRound` — this is the *single-round* `liftContext`-commutation fact (separate from
   the seqCompose fusion: it relates the per-round oracle reduction's `toReduction` to the per-round
   plain reduction `Simple.reduction.liftContext`). -/
theorem oracleReductionToReductionResidual_of_binary
    (hBinaryFusion : OracleVerifier.BinaryVerifierFusion oSpec)
    (hPerRound : ∀ i, (SingleRound.oracleReduction R n deg D oSpec i).toReduction =
      SingleRound.reduction R n deg D oSpec i) :
    oracleReductionToReductionResidual R deg D n oSpec := by
  -- Unfold the residual to the reduction equation, then to the verifier `seqCompose` fusion.
  show (oracleReduction R deg D n oSpec).toReduction = reduction R deg D n oSpec
  -- Both `oracleReduction` and `reduction` are `seqCompose`s of the per-round components.
  rw [show oracleReduction R deg D n oSpec =
        OracleReduction.seqCompose (Stmt := StatementRound R n)
          (OStmt := fun _ => OracleStatement R n deg) (Wit := fun _ => Unit)
          (pSpec := fun _ => SingleRound.pSpec R deg)
          (SingleRound.oracleReduction R n deg D oSpec) from rfl]
  rw [show reduction R deg D n oSpec =
        Reduction.seqCompose (Stmt := fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j))
          (Wit := fun _ => Unit) (pSpec := fun _ => SingleRound.pSpec R deg)
          (SingleRound.reduction R n deg D oSpec) from rfl]
  -- (1) Fuse the oracle `seqCompose`'s `toReduction` into a per-round `toReduction` `seqCompose`.
  rw [OracleReduction.seqCompose_toReduction_of_verifier
        (Stmt := StatementRound R n) (OStmt := fun _ => OracleStatement R n deg)
        (Wit := fun _ => Unit) (pSpec := fun _ => SingleRound.pSpec R deg)
        (SingleRound.oracleReduction R n deg D oSpec)
        (OracleVerifier.seqCompose_toVerifier_of_binary hBinaryFusion
          (Stmt := StatementRound R n) (OStmt := fun _ => OracleStatement R n deg)
          (Oₛ := fun _ _ => inferInstance) (Oₘ := fun _ _ => inferInstance)
          (fun i => (SingleRound.oracleReduction R n deg D oSpec i).verifier)
          (fun _ => inferInstance))]
  -- (2) Rewrite each per-round `toReduction` to the per-round plain `reduction` via `hPerRound`.
  congr 1
  funext i
  exact hPerRound i

end Sumcheck.Spec

#print axioms OracleVerifier.binaryVerifierFusion_of_verify
#print axioms OracleVerifier.seqCompose_toVerifier_of_binary
#print axioms OracleReduction.seqCompose_toReduction_of_verifier
#print axioms Sumcheck.Spec.oracleReductionToReductionResidual_of_binary
