/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Component.SendClaim

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.OracleZeroKnowledge
import ArkLib.ToVCVio.Lemmas

/-!
  # Simple Oracle Reduction - SendClaim

  The prover sends a claim to the verifier.

    - There is no witness (e.g. `Witness = Unit`), and there is a single `OStatement`.
   - The prover sends a message of the same type as `OStatement` to the verifier.
   - The verifier performs the check for `rel`, which can be expressed as an oracle computation.
   - The output data has no `Statement`, only two `OStatement`s: one from the beginning data,
     and the other is the message from the prover.
   - The output relation checks whether the two `OStatement`s are the same.

   Note: Generalize
-/

open OracleSpec OracleComp OracleQuery OracleInterface ProtocolSpec

namespace SendClaim.ForwardedClaim

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)
  {ιₛᵢ : Type} [Unique ιₛᵢ] (OStatement : ιₛᵢ → Type) [inst : ∀ i, OracleInterface (OStatement i)]

/-! The canonical `SendClaim` computes an arbitrary claim and retains the statement. This
namespace preserves the distinct forwarding component: its sole message is the unique input
oracle, its statement output is Unit, and its public Unit-valued computation may perform queries.
That computation is lossless in the canonical OracleComp semantics; it is not a rejecting test. -/

@[reducible]
def pSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[OStatement default]⟩

instance instMessageOracleInterface : ∀ i, OracleInterface ((pSpec OStatement).Message i)
  | ⟨0, _⟩ => inst default

instance instOutputOracleInterface :
    ∀ i : ιₛᵢ ⊕ ιₛᵢ, OracleInterface (Sum.elim OStatement OStatement i) :=
  fun i => OracleInterface.instRecType i

/--
The prover takes in the old oracle statement as input, and sends it as the protocol message.
-/
def oracleProver : OracleProver oSpec
    Statement OStatement Unit
    Unit (OStatement ⊕ᵥ OStatement) Unit
    (pSpec OStatement) where
  PrvState := fun _ => OStatement default

  input := fun ⟨⟨_, oStmt⟩, _⟩ => oStmt default

  sendMessage | ⟨0, _⟩ => fun st => pure (st, st)

  receiveChallenge | ⟨0, h⟩ => nomatch h

  output := fun st => pure
    (⟨(), fun x => match x with
      | .inl _ => by simpa [Unique.uniq] using st
      | .inr default => by simpa [Unique.uniq] using st⟩,
     ())

instance : ∀ i, SampleableType ((pSpec OStatement).Challenge i)
  | ⟨0, h⟩ => nomatch h

variable (relIn : Set ((Statement × (∀ i, OStatement i)) × Unit))
  (relComp : Statement → OracleComp [OStatement]ₒ Unit)
  -- (rel_eq : ∀ stmt oStmt, rel stmt oStmt ↔
  --   (OracleInterface.simOracle []ₒ (OracleInterface.oracle oStmt)).run = oStmt)

/-- The public Unit-valued oracle computation is executed before returning the output. -/
def oracleVerifier : OracleVerifier oSpec Statement OStatement Unit (OStatement ⊕ᵥ OStatement)
    (pSpec OStatement) where
  verify := fun stmt _ => OptionT.lift
    ((relComp stmt).liftComp (oSpec + ([OStatement]ₒ + [(pSpec OStatement).Message]ₒ)))
  outputOracle := .inl {
    embed := {
      toFun := fun
        | .inl i => .inl i
        | .inr _ => .inr ⟨0, by simp [pSpec]⟩
      inj' := by
        intro a b h
        match a, b with
        | .inl _, .inl _ => simpa using h
        | .inl _, .inr _ => simp at h
        | .inr _, .inl _ => simp at h
        | .inr _, .inr _ => congr 1; exact Subsingleton.elim _ _ }
    hEq := fun i => by
      match i with
      | .inl _ => rfl
      | .inr j =>
        simp only [ProtocolSpec.Message]
        exact congrArg OStatement (Unique.uniq _ j)
    outputInterface_heq := fun i => by
      match i with
      | .inl _ => rfl
      | .inr j =>
        have hj : j = default := Subsingleton.elim _ _
        subst j
        rfl }

/--
Combine the prover and verifier into an oracle reduction.
The input has no statement or witness, but one `OStatement`.
The output is also no statement or witness, but two `OStatement`s.
-/
def oracleReduction : OracleReduction oSpec
    Statement OStatement Unit
      Unit (OStatement ⊕ᵥ OStatement) Unit (pSpec OStatement) where
  prover := oracleProver oSpec Statement OStatement
  verifier := oracleVerifier oSpec Statement OStatement relComp

def relOut : Set ((Unit × (∀ i, (Sum.elim OStatement OStatement) i)) × Unit) :=
  setOf (fun ⟨⟨(), oracles⟩, _⟩ => oracles (.inl default) = oracles (.inr default))

local instance : MeasurableSpace (FullTranscript (pSpec OStatement)) := ⊤

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/--
Proof of perfect completeness: if `rel old new` holds in the real setting,
it also holds in the ideal setting, etc.
-/
instance : ProverOnly (pSpec OStatement) where
  prover_first' := by simp

theorem completeness [Nonempty σ] :
    (oracleReduction oSpec Statement OStatement relComp).perfectCompleteness
    init impl relIn (relOut OStatement) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ wit hRel value hvalue
  cases wit
  simp only [OracleReduction.toReduction, oracleReduction, Reduction.run_of_prover_first,
    oracleProver, oracleVerifier, OracleVerifier.toVerifier] at hvalue
  have hpure {α : Type} (a : α) :
      (liftM (pure a : OracleComp oSpec α) :
        OptionT (OracleComp (oSpec + [(pSpec OStatement).Challenge]ₒ'ProtocolSpec.challengeOracleInterface)) α) = pure a := by
    rfl
  simp only [hpure, pure_bind] at hvalue
  simp only [liftM_OptionT_eq, OptionT.bind, OptionT.lift, OptionT.pure,
    OptionT.run, OptionT.mk, Option.elimM, simulateQ_bind, simulateQ_map, simulateQ_pure,
    map_bind, Functor.map_map, bind_map_left, bind_assoc, pure_bind, map_pure,
    monadLift_self, support_bind, support_map, support_pure, Set.mem_iUnion,
    Set.mem_image, Prod.exists, exists_prop, Option.elim_some, Option.elim_none,
    Option.map_some, Option.map_none, Set.mem_singleton_iff, exists_eq_left,
    exists_eq_right] at hvalue
  obtain ⟨ctxOut, hctx, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
  have hctxEq := OracleComp.eq_of_mem_support_pure _ hctx
  subst ctxOut
  obtain ⟨stmtOut, hstmt, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
  erw [liftM_bind] at hstmt
  obtain ⟨u, hu, hstmt⟩ := OracleComp.mem_support_bind_peel _ _ hstmt
  have hcross {α : Type} (mx : OracleComp oSpec α) :
      (liftM mx : OptionT (OracleComp (oSpec + [(pSpec OStatement).Challenge]ₒ'ProtocolSpec.challengeOracleInterface)) α).run =
        some <$> (liftM mx : OracleComp (oSpec + [(pSpec OStatement).Challenge]ₒ'ProtocolSpec.challengeOracleInterface) α) := by
    let handler : QueryImpl oSpec (OracleComp
        (oSpec + [(pSpec OStatement).Challenge]ₒ'ProtocolSpec.challengeOracleInterface)) :=
      fun t => liftM (OracleSpec.query t)
    change simulateQ handler (mx >>= fun x => pure (some x)) =
      some <$> simulateQ handler mx
    rw [simulateQ_bind, map_eq_bind_pure_comp]
    simp only [simulateQ_pure]
    rfl
  generalize hm : (simulateQ (spec := oSpec + ([OStatement]ₒ + [(pSpec OStatement).Message]ₒ))
    (r := OracleComp oSpec) _ _ : OracleComp oSpec Unit) = mx at hu
  change u ∈ support ((liftM mx : OptionT (OracleComp
    (oSpec + [(pSpec OStatement).Challenge]ₒ'ProtocolSpec.challengeOracleInterface)) Unit).run) at hu
  rw [hcross] at hu
  obtain ⟨u₀, hu₀, huEq⟩ := OracleComp.mem_support_map_peel _ _ hu
  subst u
  have hstmtEq := OracleComp.eq_of_mem_support_pure _ hstmt
  subst stmtOut
  cases u₀
  have hvalueEq := OracleComp.eq_of_mem_support_pure _ hvalue
  subst value
  simp only [relOut, Set.mem_setOf_eq]
  refine ⟨_, rfl, ?_, ?_⟩
  · rfl
  · apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext i
      cases i with
      | inl i =>
        have hi : i = default := Subsingleton.elim _ _
        subst i
        rfl
      | inr i =>
        have hi : i = default := Subsingleton.elim _ _
        subst i
        rfl

/-- The simulator for `SendClaim`: the component has no private witness, so the simulator can run
the honest public execution on the input statement and the unique `Unit` witness. -/
def transcriptSimulator :
    OracleReduction.TranscriptSimulator oSpec Statement OStatement (pSpec OStatement) :=
  fun stmtIn =>
    Reduction.honestTranscriptDist init impl
      (oracleReduction oSpec Statement OStatement relComp).toReduction stmtIn ()

/-- The honest transcript distribution for `SendClaim` is exactly the simulator distribution,
because the protocol has no private witness. -/
theorem honestTranscriptDist_oracleReduction_evalDist
    (stmt : Statement) (oStmt : ∀ i, OStatement i) :
    evalDist (Reduction.honestTranscriptDist init impl
        (oracleReduction oSpec Statement OStatement relComp).toReduction (stmt, oStmt) ()) =
      evalDist (transcriptSimulator (oSpec := oSpec) (Statement := Statement)
        (OStatement := OStatement) (relComp := relComp) (init := init) (impl := impl)
        (stmt, oStmt)) := rfl

/-- `SendClaim` is perfectly HVZK as an oracle reduction for any input relation: the protocol has
no private witness, so the simulator can reproduce the honest transcript from public input. -/
theorem oracleReduction_perfectHVZK :
    OracleReduction.perfectHVZK init impl relIn
      (oracleReduction oSpec Statement OStatement relComp)
      (transcriptSimulator (oSpec := oSpec) (Statement := Statement)
        (OStatement := OStatement) (relComp := relComp) (init := init) (impl := impl)) := by
  intro ⟨stmt, oStmt⟩ () _
  exact (honestTranscriptDist_oracleReduction_evalDist (oSpec := oSpec)
    (Statement := Statement) (OStatement := OStatement) (init := init)
    (impl := impl) (relComp := relComp) stmt oStmt).symm

/-- Perfect HVZK implies statistical HVZK for `SendClaim` at every error budget. -/
theorem oracleReduction_statisticalHVZK (ε : NNReal) :
    OracleReduction.statisticalHVZK init impl relIn
      (oracleReduction oSpec Statement OStatement relComp)
      (transcriptSimulator (oSpec := oSpec) (Statement := Statement)
        (OStatement := OStatement) (relComp := relComp) (init := init) (impl := impl)) ε :=
  (oracleReduction_perfectHVZK (oSpec := oSpec) (Statement := Statement)
    (OStatement := OStatement) (relIn := relIn) (relComp := relComp)
    (init := init) (impl := impl)).statisticalHVZK ε

/-- `SendClaim` has an explicit perfect-HVZK simulator as an oracle reduction. -/
theorem oracleReduction_isHVZK :
    OracleReduction.isHVZK init impl relIn
      (oracleReduction oSpec Statement OStatement relComp) :=
  ⟨transcriptSimulator (oSpec := oSpec) (Statement := Statement) (OStatement := OStatement)
      (relComp := relComp) (init := init) (impl := impl),
    oracleReduction_perfectHVZK (oSpec := oSpec) (Statement := Statement)
      (OStatement := OStatement) (relIn := relIn) (relComp := relComp)
      (init := init) (impl := impl)⟩

/-- `SendClaim` has statistical HVZK at every error budget as an oracle reduction. -/
theorem oracleReduction_isStatHVZK (ε : NNReal) :
    OracleReduction.isStatHVZK init impl relIn
      (oracleReduction oSpec Statement OStatement relComp) ε :=
  (oracleReduction_isHVZK (oSpec := oSpec) (Statement := Statement)
    (OStatement := OStatement) (relIn := relIn) (relComp := relComp)
    (init := init) (impl := impl)).isStatHVZK ε

#print axioms SendClaim.ForwardedClaim.transcriptSimulator
#print axioms SendClaim.ForwardedClaim.honestTranscriptDist_oracleReduction_evalDist
#print axioms SendClaim.ForwardedClaim.oracleReduction_perfectHVZK
#print axioms SendClaim.ForwardedClaim.oracleReduction_statisticalHVZK
#print axioms SendClaim.ForwardedClaim.oracleReduction_isHVZK
#print axioms SendClaim.ForwardedClaim.oracleReduction_isStatHVZK

end SendClaim.ForwardedClaim

#print axioms SendClaim.ForwardedClaim.completeness
