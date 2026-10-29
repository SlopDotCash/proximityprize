/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Cast

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec.Cast
import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound

/-!
  # Casting for structures of oracle reductions

  We define custom dependent casts (registered as `DCast` instances) for the following structures:
  - `(Oracle)Prover`
  - `(Oracle)Verifier`
  - `(Oracle)Reduction`

  Note that casting for `ProtocolSpec`s and related structures are defined in
  `OracleReduction/ProtocolSpec/Cast.lean`.

  We also show that casting preserves execution (up to casting of the transcripts) and thus security
  properties.
-/

open OracleComp

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n₁ n₂ : ℕ} {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂}
  (hn : n₁ = n₂) (hSpec : pSpec₁.cast hn = pSpec₂)

open ProtocolSpec

namespace Prover

end Prover

namespace OracleProver

end OracleProver

namespace Verifier

end Verifier

namespace OracleVerifier

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]

/-- Transport a query to the message oracle `[pSpec₁.Message]ₒ` into an `OracleComp` over the
casted spec, given that the underlying oracle interface `O₁` agrees with the casted message
interface `Oₘ₂ i₂` up to the type equality `hMsg`. This is the per-query body used to assemble
`castMessageImpl`. -/
private def castMessageQuery
    {T₁ : Type} (O₁ : OracleInterface T₁)
    (i₂ : pSpec₂.MessageIdx) (hMsg : pSpec₂.Message i₂ = T₁)
    (hO : O₁ = _root_.cast (congrArg OracleInterface hMsg) (Oₘ₂ i₂))
    (q : O₁.Query) :
    OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec₂.Message]ₒ)) (O₁.Response q) := by
  subst hMsg
  subst hO
  -- now `O₁ = Oₘ₂ i₂`, so the query to the message oracle at `i₂` has the right response type
  exact query (spec := oSpec + ([OStmtIn]ₒ + [pSpec₂.Message]ₒ)) (Sum.inr (Sum.inr ⟨i₂, q⟩))

/-- The translation of a query to the prover messages `[pSpec₁.Message]ₒ` into a query to the
casted prover messages `[pSpec₂.Message]ₒ`. Given a query `⟨i, q⟩` to message `i`, we cast the
message index to `pSpec₂` via `MessageIdx.cast`, transport the query along the equality of oracle
interfaces `hOₘ`, query the corresponding `pSpec₂` message, and transport the response back. -/
def castMessageImpl
    (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec))) :
    QueryImpl [pSpec₁.Message]ₒ (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec₂.Message]ₒ))) :=
  fun q =>
    castMessageQuery (oSpec := oSpec) (OStmtIn := OStmtIn) (Oₘ₂ := Oₘ₂)
      (Oₘ₁ q.1) (q.1.cast hn hSpec) (Message.cast_idx hSpec)
      (by rw [hOₘ q.1, dcast_eq_root_cast]) q.2

variable (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))

/-- Helper for `cast_toVerifier`: the output oracle-statement function produced by
`OracleVerifier.toVerifier` depends only on the embedding pointwise. If two embeddings `e` and `emb`
agree pointwise, the resulting (dependent) `match` functions are equal, up to the proof-irrelevant
`hEq`/discriminant transports. This is stated generically to keep the `split`/transport reasoning
away from the heterogeneous-cast normalization in `cast_toVerifier`, which keeps the proof term
free of `sorryAx`. -/
private theorem toVerifier_oStmtOut_congr
    {emb : ιₛₒ → ιₛᵢ ⊕ pSpec₁.MessageIdx}
    (hEqEmb : ∀ i, OStmtOut i =
      match emb i with | Sum.inl j => OStmtIn j | Sum.inr j => pSpec₁.Message j)
    (oStmt : (i : ιₛᵢ) → OStmtIn i) (transcript : pSpec₁.FullTranscript)
    (e : ιₛₒ → ιₛᵢ ⊕ pSpec₁.MessageIdx) (he : ∀ i, e i = emb i)
    (hEqE : ∀ i, OStmtOut i =
      match e i with | Sum.inl j => OStmtIn j | Sum.inr j => pSpec₁.Message j) :
    ∀ i,
    (match h : e i with
      | Sum.inl j => (hEqE i ▸ h ▸ oStmt j : OStmtOut i)
      | Sum.inr j => (hEqE i ▸ h ▸ transcript.messages j : OStmtOut i))
    = (match h : emb i with
      | Sum.inl j => (hEqEmb i ▸ h ▸ oStmt j : OStmtOut i)
      | Sum.inr j => (hEqEmb i ▸ h ▸ transcript.messages j : OStmtOut i)) := by
  intro i
  have hei := he i
  split <;> rename_i j heq <;> rw [hei] at heq <;>
    (split <;> rename_i j' heq' <;> rw [heq] at heq')
  · have hjj : j = j' := Sum.inl.inj heq'
    simp only [eqRec_eq_cast, cast_cast]
    apply eq_of_heq
    refine (cast_heq _ (oStmt j)).trans (HEq.trans ?_ (cast_heq _ (oStmt j')).symm)
    rw [hjj]
  · exact absurd heq' (by simp)
  · exact absurd heq' (by simp)
  · have hjj : j = j' := Sum.inr.inj heq'
    simp only [eqRec_eq_cast, cast_cast]
    apply eq_of_heq
    refine (cast_heq _ (transcript.messages j)).trans
      (HEq.trans ?_ (cast_heq _ (transcript.messages j')).symm)
    rw [hjj]

end OracleVerifier

namespace Reduction

end Reduction

namespace OracleReduction

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))

end OracleReduction

section Execution

-- Future work: show that the execution of everything is the same, modulo casting of transcripts
variable {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂} (hSpec : pSpec₁.cast hn = pSpec₂)

namespace Prover

-- Future work: need to cast [pSpec₁.Challenge]ₒ to [pSpec₂.Challenge]ₒ, where they have the default
-- instance `challengeOracleInterface`

end Prover

namespace Verifier

variable (V : Verifier oSpec StmtIn StmtOut pSpec₁)

end Verifier

namespace Reduction

variable (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁)

end Reduction

end Execution

section Security

open NNReal

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  [inst₁ : ∀ i, SampleableType (pSpec₁.Challenge i)]
  [inst₂ : ∀ i, SampleableType (pSpec₂.Challenge i)]
  (hChallenge : ∀ i, inst₁ i = dcast (by simp) (inst₂ (i.cast hn hSpec)))

section Protocol

variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}

namespace Reduction

variable (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁)

end Reduction

namespace Verifier

variable (V : Verifier oSpec StmtIn StmtOut pSpec₁)

end Verifier

end Protocol

section OracleProtocol

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))
  {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
  {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}

namespace OracleReduction

variable (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁)



end OracleReduction

namespace OracleVerifier

variable (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁)

end OracleVerifier

end OracleProtocol

end Security
