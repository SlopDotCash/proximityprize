/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.Data.Hash.DuplexSponge
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Preliminaries
import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.SingleSalt

/-!
# Duplex Sponge Fiat-Shamir

We define the (multi-round) Fiat-Shamir transformation using duplex sponges.

This file contains both:

- the unsalted DSFS core,
- the paper-native salted wrapper with fresh uniform salt when the ambient oracle supports lifting
  `ProbComp`,
- and a generalized salted wrapper parameterized by an explicit salt source.
-/

/-- Result type for three-valued algorithm outcomes: paper-`err`, paper-`none`, success.

Used for BackTrack (§5.2) and LookAhead (§5.3), which have two distinct failure modes at the type
level. Other Section 5 algorithms (D2SQuery, D2SAlgo, StdTrace, D2STrace) have only binary
abort/success and continue to use `OptionT`. -/
inductive ExperimentOutput.{u} (Out : Type u) : Type u where
  /-- Paper-`err`: e.g., multiple elements in `Outs` (BackTrack) or multiple chains (LookAhead). -/
  | err : ExperimentOutput Out
  /-- Paper-`none`: e.g., zero elements found, empty lookahead family. -/
  | noResult : ExperimentOutput Out
  /-- Success case: unique paper tuple recovered. -/
  | some : Out → ExperimentOutput Out
  deriving Repr

namespace ProtocolSpec

/-- Type class for protocol specifications to specify the size of each message as a natural number
  (to be interpreted as a vector of units `U` of the given size for some sponge unit `U`) -/
class HasMessageSize {n : ℕ} (pSpec : ProtocolSpec n) where
  messageSize : pSpec.MessageIdx → Nat

export HasMessageSize (messageSize)

/-- Type class for protocol specifications to specify the size of each challenge as a natural number
  (to be interpreted as a vector of units `U` of the given size for some sponge unit `U`) -/
class HasChallengeSize {n : ℕ} (pSpec : ProtocolSpec n) where
  challengeSize : pSpec.ChallengeIdx → Nat

export HasChallengeSize (challengeSize)

/-- Message indices in rounds strictly before `k`. -/
abbrev MessageIdxBefore {n : ℕ} (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  {j : pSpec.MessageIdx // j.1.1 < k.1}

/-- Challenge indices in rounds strictly before `k`. -/
abbrev ChallengeIdxBefore {n : ℕ} (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  {j : pSpec.ChallengeIdx // j.1.1 < k.1}

/-- CO25 §5.2 — Encoded prover messages `(α̂_1, …, α̂_i)` for message rounds strictly before `k`.
`f j h` gives the `U`-vector encoding of message `j` whenever the round of `j` is before `k`. -/
abbrev EncodedMessagesBefore {n : ℕ} (pSpec : ProtocolSpec n) (U : Type) [HasMessageSize pSpec]
    (k : Fin (n + 1)) : Type :=
  (j : MessageIdxBefore k pSpec) → Vector U (messageSize j.val)

/-- Challenge analogue of `EncodedMessagesBefore`. -/
abbrev EncodedChallengesBefore {n : ℕ} (pSpec : ProtocolSpec n) (U : Type) [HasChallengeSize pSpec]
    (k : Fin (n + 1)) : Type :=
  (j : ChallengeIdxBefore k pSpec) → Vector U (challengeSize j.val)

namespace EncodedMessagesBefore

/-- Flatten to a sigma-list for consumers still expecting `List (Sigma ...)`. -/
noncomputable def toList {n : ℕ} {pSpec : ProtocolSpec n} {U : Type} [HasMessageSize pSpec]
    {k : Fin (n + 1)} (f : pSpec.EncodedMessagesBefore U k) :
    List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)) :=
  (Finset.univ : Finset (pSpec.MessageIdx)).toList.filterMap fun j =>
    if h : j.1.1 < k.1 then some ⟨j, f ⟨j, h⟩⟩ else none

end EncodedMessagesBefore

/-- Codec class for CO25 Definition 4.1.

`Codec pSpec U` is the generic-parameter carrier for everything DSFS needs about a
protocol's per-round encoder/decoder: per-round vector sizes, the encoder, its injectivity proof,
the decoder, the per-round decoder bias `ε_cdc`, and the per-round preimage sampler.

It extends the `U`-independent size classes `HasMessageSize` / `HasChallengeSize`, and projects
to per-index `Serialize` / `Deserialize` / `Serialize.IsInjective` instances via the projection
instances below. Downstream consumers (the Section 5 trace/prover transforms) take a single
`[Codec pSpec U]` instance; the projection instances discharge incidental `[Serialize ...]` /
`[Deserialize ...]` requirements at use sites with a *named* index.

We account for decoding imperfection by tracking **decoding biases**: a codec has bias `ε_cdc` if,
for every challenge round `i`, `ψ_i : Σ^{ℓ_V(i)} → M_{V, i}` is `ε_{cdc, i}`-biased. -/
class Codec {n : ℕ} (pSpec : ProtocolSpec n) (U : Type)
    extends HasMessageSize pSpec, HasChallengeSize pSpec where
  /-- `φᵢ : Message i → Σ^{ℓ_P(i)}` — message encoder (CO25 Def. 4.1). -/
  encode : (i : pSpec.MessageIdx) → pSpec.Message i → Vector U (messageSize i)
  encode_injective : ∀ i, Function.Injective (encode i) -- `φᵢ` is injective
  /-- `ψᵢ : Σ^{ℓ_V(i)} → Challenge i` — challenge decoder (CO25 Def. 4.1). -/
  decode : (i : pSpec.ChallengeIdx) → Vector U (challengeSize i) → pSpec.Challenge i
  decodingBias : pSpec.ChallengeIdx → NNReal -- `ε_cdc`
  /-- For every `i`, `decode i` is ε-biased: `dist (𝒰 Challenge_i) (decode_i <$> 𝒰 Domain_i)`
    ≤ `decodingBias i`. Matches `Deserialize.CloseToUniform.ε_close` (CO25 Definition 4.1). -/
  decode_isBiased : ∀ (i : pSpec.ChallengeIdx)
      [Fintype (Vector U (challengeSize i))] [Nonempty (Vector U (challengeSize i))]
      [Fintype (pSpec.Challenge i)] [Nonempty (pSpec.Challenge i)],
      dist (PMF.uniformOfFintype (pSpec.Challenge i))
        (decode i <$> PMF.uniformOfFintype (Vector U (challengeSize i))) ≤ decodingBias i
  /-- For every `i`, `decode i` is surjective: every challenge has at least one encoded preimage.
    Required for the `ψ⁻¹` sampler in the Section 5.8 reduction. -/
  decode_surjective : ∀ i, Function.Surjective (decode i)
  /-- `ψᵢ⁻¹ : Challenge i → ProbComp (Σ^{ℓ_V(i)})` — preimage sampler (CO25 Def. 4.1). -/
  sampleChallengePreimage :
    (i : pSpec.ChallengeIdx) → pSpec.Challenge i → ProbComp (Vector U (challengeSize i))

namespace Codec

variable {n : ℕ} {pSpec : ProtocolSpec n} {U : Type}

instance (priority := high) instSerializeMessage [c : Codec pSpec U] (i : pSpec.MessageIdx) :
    Serialize (pSpec.Message i) (Vector U (messageSize i)) where
  serialize := c.encode i

instance (priority := high) instSerializeMessageInjective [c : Codec pSpec U]
    (i : pSpec.MessageIdx) :
    Serialize.IsInjective (pSpec.Message i) (Vector U (messageSize i)) where
  serialize_inj := c.encode_injective i

instance (priority := high) instDeserializeChallenge [c : Codec pSpec U] (i : pSpec.ChallengeIdx) :
    Deserialize (pSpec.Challenge i) (Vector U (challengeSize i)) where
  deserialize := c.decode i

/-- hax-pipeline constructor: assemble a `Codec` from external `Serialize`/`Deserialize`
    instances supplied by Rust→hax extraction, plus the math-side metadata. `decodingBias` is
    derived from `[decChalUniform]`'s `ε` field; no separate bias parameter is needed. -/
def mk' {n : ℕ} (pSpec : ProtocolSpec n) (U : Type)
    (mSize : pSpec.MessageIdx → Nat) (cSize : pSpec.ChallengeIdx → Nat)
    [∀ i, Fintype (Vector U (cSize i))] [∀ i, Nonempty (Vector U (cSize i))]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Nonempty (pSpec.Challenge i)]
    [serMsg : ∀ i, Serialize (pSpec.Message i) (Vector U (mSize i))]
    [serMsgInj : ∀ i, Serialize.IsInjective (pSpec.Message i) (Vector U (mSize i))]
    [decChal : ∀ i, Deserialize (pSpec.Challenge i) (Vector U (cSize i))]
    [decChalUniform : ∀ i, Deserialize.CloseToUniform (pSpec.Challenge i) (Vector U (cSize i))]
    (dechalSurj : ∀ i, Function.Surjective ((decChal i).deserialize))
    (sampler : (i : pSpec.ChallengeIdx) → pSpec.Challenge i → ProbComp (Vector U (cSize i))) :
    Codec pSpec U where
  messageSize := mSize
  challengeSize := cSize
  encode := fun i => (serMsg i).serialize
  encode_injective := fun i => (serMsgInj i).serialize_inj
  decode := fun i => (decChal i).deserialize
  decodingBias := fun i => (decChalUniform i).ε
  decode_isBiased := fun i [_h1 : Fintype (Vector U (cSize i))]
      [_h2 : Nonempty (Vector U (cSize i))]
      [_h3 : Fintype (pSpec.Challenge i)]
      [_h4 : Nonempty (pSpec.Challenge i)] => by
    convert (decChalUniform i).ε_close using 4
  decode_surjective := dechalSurj
  sampleChallengePreimage := sampler

/-- Backwards-compatible wrapper class for the codec semantic laws (CO25 Definition 4.1).

The semantic obligations now live directly inside the `Codec` class fields (`decode_isBiased`,
`decode_surjective`), so `IsLawful` is satisfied automatically for any `Codec`. It is retained as a
`Prop` alias so the paper-facing `LawfulCodec` alias in `DuplexSponge/Basic.lean` keeps
resolving. -/
class IsLawful [c : Codec pSpec U] : Prop where
  decode_surjective : ∀ i, Function.Surjective (c.decode i) := c.decode_surjective

instance instIsLawful [c : Codec pSpec U] : ProtocolSpec.Codec.IsLawful (c := c) where
  decode_surjective := c.decode_surjective

/-- A lawful codec's decoder is close to uniform with bias `decodingBias`, derived from the
`decode_isBiased` field. Provides `Deserialize.CloseToUniform` at use sites needing it. -/
instance instDeserializeCloseToUniform [c : Codec pSpec U]
    [∀ i, Fintype (Vector U (c.challengeSize i))] [∀ i, Nonempty (Vector U (c.challengeSize i))]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Nonempty (pSpec.Challenge i)] :
    ∀ i, Deserialize.CloseToUniform (pSpec.Challenge i) (Vector U (c.challengeSize i)) := by
  intro i
  refine ⟨c.decodingBias i, ?_⟩
  exact c.decode_isBiased i

end Codec

variable (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    {U : Type} [SpongeUnit U] [SpongeSize]
    [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
    [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- Number of queries to the permutation oracle needed to absorb the `i`-th message of the
  protocol specification. This is `Lₚ(i)` in the paper (Equation 7). -/
def numPermQueriesMessage (i : pSpec.MessageIdx) : Nat :=
  Nat.ceil ((messageSize i : ℚ) / SpongeSize.R)

alias Lₚᵢ := numPermQueriesMessage

/-- Total number of queries to the permutation oracle needed to absorb all messages of the
  protocol specification. This is `Lₚ` in the paper (Equation 8). -/
def totalNumPermQueriesMessage : Nat :=
  ∑ i, pSpec.Lₚᵢ i

/-- Number of queries to the permutation oracle needed to absorb the `i`-th challenge of the
  protocol specification. This is `Lᵥ(i)` in the paper (Equation 7). -/
def numPermQueriesChallenge (i : pSpec.ChallengeIdx) : Nat :=
  Nat.ceil ((challengeSize i : ℚ) / SpongeSize.R)

alias Lᵥᵢ := numPermQueriesChallenge

/-- Total number of queries to the permutation oracle needed to absorb all challenges of the
  protocol specification. This is `Lᵥ` in the paper (Equation 8). -/
def totalNumPermQueriesChallenge : Nat :=
  ∑ i, pSpec.Lᵥᵢ i

/-- Total number of queries to the permutation oracle needed to absorb all messages and challenges
  of the protocol specification. This is `L` in the paper (Equation 8). -/
def totalNumPermQueries : Nat :=
  pSpec.totalNumPermQueriesMessage + pSpec.totalNumPermQueriesChallenge

/-- Number of permutation queries needed to absorb a salt of length `δ`. This is `L_δ` in CO25
  Equation 6. -/
def numPermQueriesSalt (δ : Nat) : Nat :=
  Nat.ceil ((δ : ℚ) / SpongeSize.R)

/-- Total number of permutation queries needed by the salted DSFS construction, including the salt
  absorption phase. -/
def totalNumPermQueriesSalted (δ : Nat) : Nat :=
  Nat.ceil ((δ : ℚ) / SpongeSize.R) + pSpec.totalNumPermQueries

/-- The oracle specification for duplex sponge Fiat-Shamir (Equation 16, written as `𝒟_Σ`).
It is indexed over the challenge rounds of the protocol specification, and for each such round `i`:
- The input is the input statement `stmtIn` and, for each `j < i` that is a message round,
  a vector of units of size `Lₚ(j)` (the number of queries to the permutation oracle needed to
  absorb the `j`-th message)
- The output is a vector of units of size `Lᵥ(i)` (the number of queries to the permutation oracle
  needed to absorb the `i`-th challenge) -/
def duplexSpongeHybridOracle : OracleSpec
    ((i : pSpec.ChallengeIdx) × StmtIn ×
      ((j : pSpec.MessageIdx) → (hj : j.1 < i.1) → Vector U (pSpec.Lₚᵢ j))) :=
  fun i => Vector U (pSpec.Lᵥᵢ i.1)

alias «𝒟_Σ» := duplexSpongeHybridOracle

section Section58Oracles

/-- Section 5.8 `Hyb₁` challenge-oracle surface: encoded prover-prefix queries, encoded verifier
responses.

Per CO25 Eq. 15: `dom_i = {0,1}^≤n × Σ^δ × Σ^{ℓ_P(1)} × … × Σ^{ℓ_P(i)}` — the prover prefix is
*exactly* `i` encoded messages, not an unbounded list. We model this as
`pSpec.EncodedMessagesBefore U i.1.castSucc`, the dependent function indexed by message rounds
strictly before `i`. -/
@[inline, reducible]
def gSpecInterface
    {U : Type} [SpongeUnit U] [SpongeSize]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    ∀ i, OracleInterface (Vector U (challengeSize (pSpec := pSpec) i)) := fun i =>
  { Query :=
      StmtIn × Vector U δ ×
        pSpec.EncodedMessagesBefore U i.1.castSucc
    toOC.spec := fun _ => Vector U (challengeSize (pSpec := pSpec) i)
    toOC.impl := fun _ => read }

/-- Oracle family for the `gᵢ` queries in Section 5.8 `Hyb₁`. -/
@[inline, reducible]
def gSpec
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query)) :=
  [fun i => Vector U (challengeSize (pSpec := pSpec) i)]ₒ'
    (gSpecInterface (U := U) StmtIn pSpec δ)

/-- Section 5.8 `Hyb₂` challenge-oracle surface: encoded prover-prefix queries, decoded verifier
responses.

Same CO25 Eq. 52 prefix shape as `gSpecInterface` (encoded messages
indexed by rounds `< i`); only the response type differs (decoded `pSpec.Challenge i`). -/
@[inline, reducible]
def eSpecInterface
    {U : Type} [SpongeUnit U] [SpongeSize]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) (δ : Nat) [HasMessageSize pSpec] :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query :=
      StmtIn × Vector U δ ×
        pSpec.EncodedMessagesBefore U i.1.castSucc
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => read }

/-- Oracle family for the `eᵢ` queries in Section 5.8 `Hyb₂`. -/
@[inline, reducible]
def eSpec
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) (δ : Nat) [HasMessageSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (eSpecInterface (U := U) StmtIn pSpec δ i).Query)) :=
  [pSpec.Challenge]ₒ'
    (eSpecInterface (U := U) StmtIn pSpec δ)

end Section58Oracles

end ProtocolSpec

/-!
## Salt codec (CO25 line 1188, line 1729)

The paper distinguishes two views of a single salt:

- **On-sponge view** (CO25 Construction 4.3): the salt lives in `Σ^δ` and is absorbed into the
  duplex sponge directly. In Lean this is `Vector U δ`.
- **FS-standard view** (CO25 Construction 3.17 + §5.8 hybrids `Hyb₃`, `Hyb₄`): the salt is a
  binary string `{0,1}^{δ★}` used as part of the FS-standard oracle key, modeled as `Salt`.

The two views are bridged by an injective encoding `bin : Σ^δ → {0,1}^{δ★}` (paper line 1188).
-/

/-- Bridge between on-sponge salts (`Σ^δ = Vector U δ`) and the pre-encoded abstract salt type
`Salt` (paper's `{0,1}^{δ★}`). `encode = bin` per CO25 line 1188. -/
class SaltCodec (U : Type) (δ : Nat) (Salt : Type) where
  /-- `bin : Σ^δ → {0,1}^{δ★}` — inject `Σ^δ` salt into the FS-standard pre-encoded salt type. -/
  encode : Vector U δ → Salt
  /-- Left inverse of `encode`. Exists because `encode = bin` is injective (paper line 1729). -/
  decode : Salt → Vector U δ
  /-- `decode ∘ encode = id`. Gives **injectivity** of `encode` (CO25 line 1729). -/
  decode_encode : ∀ τ, decode (encode τ) = τ

namespace SaltCodec

variable {U : Type} {δ : Nat} {Salt : Type}

/-- `encode` is injective, derived from `decode_encode`. Matches CO25 line 1729. -/
theorem encode_injective [SaltCodec U δ Salt] :
    Function.Injective (encode (U := U) (δ := δ) (Salt := Salt)) := by
  intro a b h
  have := congrArg (decode (U := U) (δ := δ) (Salt := Salt)) h
  rw [decode_encode, decode_encode] at this
  exact this

end SaltCodec

namespace OracleSpec

/-- The oracle specification for duplex sponge Fiat-Shamir (Definition 4.2, written as `𝒟_𝔖`).
The index consists of `(h, p, p⁻¹)`, where:
- `h : ByteArray → Vector U SpongeSize.C`
is the hash function (assumed to be random oracle)
(Note: input could be different from `ByteArray`)
- `p : Vector U SpongeSize.N → Vector U SpongeSize.N`
is the forward direction of the random permutation
- `p⁻¹ : Vector U SpongeSize.N → Vector U SpongeSize.N`
is the backward direction of the random permutation
-/
@[reducible]
def duplexSpongeChallengeOracle (StartType : Type) (U : Type) [SpongeUnit U] [SpongeSize] :
    OracleSpec (StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U) :=
  (StartType →ₒ Vector U SpongeSize.C) + permutationOracle (CanonicalSpongeState U)

alias 𝒟_𝔖 := duplexSpongeChallengeOracle

/-- The type of a single entry in a duplex sponge query trace. Implicit-parameter companion to
`DSTraceStorage.duplexSpongeTraceEntry`; used by the §5.2 BackTrack scan where the start/unit
types are inferred from the surrounding trace. -/
abbrev duplexSpongeTraceEntry {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  := Sigma (α := StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U)
      (β := duplexSpongeChallengeOracle StartType U)

/-! ### Smart constructors for the three `(h, p, p⁻¹)` `𝒟_𝔖` query flavors

CO25 §5.4 paper notation `('h', 𝕩, …)` / `('p', s_in, …)` / `('p⁻¹', s_out, …)` corresponds to
three nested-`Sum` injections into `(duplexSpongeChallengeOracle StartType U).Domain`. The wrappers
below tag each injection with the paper query name. `@[match_pattern]` keeps them usable as match
patterns; `@[reducible]` lets the elaborator unfold them where the bare `Sum`-form is expected. -/

/-- CO25 §5.4 paper `h(𝕩)` — hash query index. -/
@[match_pattern, reducible]
def dsHashQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
    (stmt : StartType) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inl stmt

/-- CO25 §5.4 paper `p(s_in)` — forward permutation query index. -/
@[match_pattern, reducible]
def dsPermQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
    (stateIn : CanonicalSpongeState U) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inr (Sum.inl stateIn)

/-- CO25 §5.4 paper `p⁻¹(s_out)` — inverse permutation query index. -/
@[match_pattern, reducible]
def dsPermInvQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
    (stateOut : CanonicalSpongeState U) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inr (Sum.inr stateOut)

end OracleSpec

open OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  -- All messages are serializable to an array of units
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  -- All challenges are deserializable from an array of units
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- Fresh uniform salt sampler for the paper-native salted DSFS wrapper. This requires that the
ambient oracle context can faithfully lift `ProbComp` queries. -/
def uniformSalt {δ : Nat}
    [SampleableType U]
    [unifSpec ⊂ₒ oSpec] [OracleSpec.LawfulSubSpec unifSpec oSpec] :
    OracleComp oSpec (Vector U δ) :=
  ($ᵗ Vector U δ : ProbComp (Vector U δ)).liftComp oSpec

namespace ProtocolSpec.Messages

/-- The proof object for the salted duplex-sponge Fiat-Shamir transform from CO25 Construction 4.3.
-/
abbrev SaltedProof (δ : Nat) := Vector U δ × pSpec.Messages

/-- Auxiliary function for deriving the transcript up to round `k` from the (full) messages, via
  querying the permutation oracle for the challenges.

  This is used to define `deriveTranscriptDSFS`. -/
def deriveTranscriptDSFSAux {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (sponge : CanonicalDuplexSponge U)
    (messages : pSpec.Messages) (i : Fin (n + 1)) :
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (CanonicalDuplexSponge U × pSpec.Transcript i) :=
  Fin.induction
    (pure (sponge, fun i => i.elim0))
    (fun i ih => do
      let ⟨curSponge, prevTranscript⟩ ← ih
      match hDir : pSpec.dir i with
      | .V_to_P =>
        let ⟨challenge, newSponge⟩ ← liftM (curSponge.squeeze (challengeSize ⟨i, hDir⟩))
        let deserializedChallenge : pSpec.Challenge ⟨i, hDir⟩ :=
          Deserialize.deserialize challenge
        return (newSponge, prevTranscript.concat deserializedChallenge)
      | .P_to_V =>
        let serializedMessage : Vector U (messageSize ⟨i, hDir⟩) :=
          Serialize.serialize (messages ⟨i, hDir⟩)
        let newSponge ← liftM (DuplexSponge.absorb curSponge serializedMessage.toList)
        return (newSponge, prevTranscript.concat (messages ⟨i, hDir⟩)))
    i

/-- Derive the full transcript from the (full) messages, via doing absorb / squeeze operations on
    the duplex sponge.

  Returns the final state of the duplex sponge and the full transcript -/
def deriveTranscriptDSFS {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmtIn : StmtIn) (messages : pSpec.Messages) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (CanonicalDuplexSponge U × pSpec.FullTranscript) := do
  let sponge ← liftM (DuplexSponge.start stmtIn)
  deriveTranscriptDSFSAux sponge messages (Fin.last n)

/-- Derive the full transcript for the salted DSFS wrapper from CO25 Construction 4.3.

This keeps the existing unsalted DSFS core unchanged and models the paper's single salt as an
initial absorb step performed once before processing the protocol messages. -/
def deriveTranscriptDSFSSalted {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type} {δ : Nat}
    (stmtIn : StmtIn) (salt : Vector U δ) (messages : pSpec.Messages) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (CanonicalDuplexSponge U × pSpec.FullTranscript) := do
  let sponge ← liftM (DuplexSponge.start stmtIn)
  let saltedSponge ← liftM (DuplexSponge.absorb sponge salt.toList)
  deriveTranscriptDSFSAux saltedSponge messages (Fin.last n)

end Messages

end ProtocolSpec

open ProtocolSpec

/--
Prover's function for processing the next round, given the current result of the previous round.

This is modified for Fiat-Shamir, where we only accumulate the messages and not the challenges.
-/
@[inline, specialize]
def Prover.processRoundDSFS [∀ i, VCVCompatible (pSpec.Challenge i)]
    (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (pSpec.MessagesUpTo j.castSucc ×
        CanonicalDuplexSponge U × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (pSpec.MessagesUpTo j.succ ×
          CanonicalDuplexSponge U × prover.PrvState j.succ) := do
  let ⟨messages, sponge, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let f ← prover.receiveChallenge ⟨j, hDir⟩ state
    let (challenge, newSponge) ←
      liftM (m := OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
        (DuplexSponge.squeeze sponge (challengeSize ⟨j, hDir⟩))
    -- Deserialize the challenge
    let deserializedChallenge : pSpec.Challenge ⟨j, hDir⟩ := Deserialize.deserialize challenge
    return ⟨messages.extend hDir, newSponge, f deserializedChallenge⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    let serializedMessage : Vector U (messageSize ⟨j, hDir⟩) := Serialize.serialize msg
    let newSponge ←
      liftM (m := OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
        (DuplexSponge.absorb sponge serializedMessage.toList)
    return ⟨messages.concat hDir msg, newSponge, newState⟩

/--
Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def Prover.runToRoundDSFS [∀ i, VCVCompatible (pSpec.Challenge i)] (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (pSpec.MessagesUpTo i ×
            DuplexSponge U (Vector U SpongeSize.N) × prover.PrvState i) :=
  Fin.induction
    (do
      -- Initialize the sponge with the input statement
      let sponge ← liftM (DuplexSponge.start stmt)
      return ⟨default, sponge, state⟩
    )
    (prover.processRoundDSFS)
    i

/-- Run the prover up to round `i` for the salted DSFS wrapper from CO25 Construction 4.3. -/
@[inline, specialize]
def Prover.runToRoundDSFSSalted [∀ i, VCVCompatible (pSpec.Challenge i)] {δ : Nat}
    (i : Fin (n + 1)) (stmt : StmtIn) (salt : Vector U δ)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (state : prover.PrvState 0) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (pSpec.MessagesUpTo i ×
            DuplexSponge U (Vector U SpongeSize.N) × prover.PrvState i) :=
  Fin.induction
    (do
      let sponge ← liftM (DuplexSponge.start stmt)
      let saltedSponge ← liftM (DuplexSponge.absorb sponge salt.toList)
      return ⟨default, saltedSponge, state⟩
    )
    (prover.processRoundDSFS)
    i

/-- The duplex sponge Fiat-Shamir transformation for the prover. -/
def Prover.duplexSpongeFiatShamir (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveProver (∀ i, pSpec.Message i) (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  -- Compute the messages to send via the modified `runToRoundFS`
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let ⟨messages, _, state⟩ ← P.runToRoundDSFS (Fin.last n) stmtIn state
    return ⟨messages, state⟩
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/-- The paper-facing salted duplex-sponge Fiat-Shamir transformation for the prover.

ArkLib honest provers do not have first-class local probabilistic effects, so the salt source is
made explicit as an oracle computation in the ambient oracle interface. -/
def Prover.duplexSpongeFiatShamirSalted {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveProver (ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U) StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let salt ← sampleSalt.liftComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    let ⟨messages, _, state⟩ ← P.runToRoundDSFSSalted (i := Fin.last n) stmtIn salt state
    return ⟨(salt, messages), state⟩
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/-- The paper-native salted duplex-sponge Fiat-Shamir prover wrapper from CO25 Construction 4.3,
sampling a fresh uniform salt internally whenever the ambient oracle supports lifting `ProbComp`. -/
def Prover.duplexSpongeFiatShamirSaltedRandom {δ : Nat}
    [SampleableType U]
    [unifSpec ⊂ₒ oSpec] [OracleSpec.LawfulSubSpec unifSpec oSpec]
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveProver (ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U) StmtIn WitIn StmtOut WitOut :=
  P.duplexSpongeFiatShamirSalted (U := U) (uniformSalt (oSpec := oSpec) (U := U) (δ := δ))

/-- The duplex sponge Fiat-Shamir transformation for the verifier. -/
def Verifier.duplexSpongeFiatShamir (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    -- Get the messages from the non-interactive proof
    let messages : pSpec.Messages := proof 0
    -- Derive the full transcript based on the messages and the sponge
    let ⟨_, transcript⟩ ← (messages.deriveTranscriptDSFS (oSpec := oSpec) (U := U) stmtIn)
    let v ← (V.verify stmtIn transcript).run
    v.getM

/-- The paper-facing salted duplex-sponge Fiat-Shamir transformation for the verifier. -/
def Verifier.duplexSpongeFiatShamirSalted {δ : Nat}
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U) StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let ⟨salt, messages⟩ : ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ := proof 0
    let ⟨_, transcript⟩ ←
      messages.deriveTranscriptDSFSSalted (oSpec := oSpec) (U := U) stmtIn salt
    let v ← (V.verify stmtIn transcript).run
    v.getM

/-- The duplex sponge Fiat-Shamir transformation for an (interactive) reduction, which consists of
  applying the duplex sponge Fiat-Shamir transformation to both the prover and the verifier. -/
def Reduction.duplexSpongeFiatShamir (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (∀ i, pSpec.Message i) (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.duplexSpongeFiatShamir
  verifier := R.verifier.duplexSpongeFiatShamir

/-- The paper-facing salted duplex-sponge Fiat-Shamir transformation from CO25 Construction 4.3.

The salt source is an explicit parameter because ArkLib does not currently model local prover
randomness directly. -/
def Reduction.duplexSpongeFiatShamirSalted {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U) StmtIn WitIn StmtOut WitOut where
  prover := R.prover.duplexSpongeFiatShamirSalted (U := U) sampleSalt
  verifier := R.verifier.duplexSpongeFiatShamirSalted (U := U)

/-- The paper-native salted duplex-sponge Fiat-Shamir transformation from CO25 Construction 4.3,
sampling a fresh uniform salt internally whenever the ambient oracle supports lifting `ProbComp`. -/
def Reduction.duplexSpongeFiatShamirSaltedRandom {δ : Nat}
    [SampleableType U]
    [unifSpec ⊂ₒ oSpec] [OracleSpec.LawfulSubSpec unifSpec oSpec]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U) StmtIn WitIn StmtOut WitOut where
  prover := R.prover.duplexSpongeFiatShamirSaltedRandom (U := U) (δ := δ)
  verifier := R.verifier.duplexSpongeFiatShamirSalted (U := U)

/-! ### Section 5 transform surfaces and monad stacks

These top-level types feed CO25 §5.4–5.8 (the trace/prover transforms). They are kept here, next
to the salted DSFS surfaces above, because the Section 5 files (`TraceTransform`, `ProverTransform`)
all take `[Codec pSpec U]` and reuse the same `gSpec`/`UnitSampleM` shapes. -/

/-- Proof-string format for the salted DSFS surface (`τ` plus prover messages). -/
abbrev DSSaltedProof {n : ℕ} (pSpec : ProtocolSpec n) (U : Type) (δ : Nat) :=
  Vector U δ × pSpec.Messages

/-- Paper-faithful type of the malicious DSFS prover `𝒫̃` (CO25 §5.4): queries
`(h, p, p⁻¹) = duplexSpongeChallengeOracle` plus an ambient `oSpec`, and outputs a salted proof
`(x, (τ, messages))` with on-sponge salt `τ : Vector U δ`. -/
abbrev MaliciousProver {n : ℕ} {ι : Type} (oSpec : OracleSpec ι) (pSpec : ProtocolSpec n)
    (StmtIn U : Type) [SpongeUnit U] [SpongeSize] (δ : ℕ) :=
  OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)

/-- `OracleComp σ` paired with a paper-faithful abort layer (`OptionT`).

`OracleComp σ` queries `σ`; `OptionT` adds `none = abort` (CO25 §5 `err` outcome). Section 5
simulators all live in this stack with various choices of `σ`. -/
abbrev AbortComp {ι : Type} (σ : OracleSpec ι) := OptionT (OracleComp σ)

/-- Shared abort/randomness monad stack used by Section 5 algorithms.

`OptionT` provides paper-binary `abort`/`success`; the inner `OracleComp (Unit →ₒ U)` provides the
fresh `𝒰(Σ)` sampling oracle. This is `AbortComp (Unit →ₒ U)`. -/
abbrev UnitSampleM (U : Type) [SpongeUnit U] := AbortComp (Unit →ₒ U)

section TransformTypes

variable {ι : Type} {oSpec : OracleSpec ι}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  {δ : Nat}
  [codec : Codec pSpec U]

/-- CO25 §5.4 — External challenge-oracle family augmented with the auxiliary sampling oracles.

`D2SChallengePlusUnitOracle challengeSpec` is `challengeSpec + (Unit →ₒ U) + unifSpec`. -/
abbrev D2SChallengePlusUnitOracle {κ : Type} (challengeSpec : OracleSpec κ) :=
  challengeSpec + ((Unit →ₒ U) + unifSpec)

/-- CO25 §5.4 Eq. 16 — shorthand for the recurring `gᵢ`-realization shape: a `QueryImpl`
from the `gSpec` source into `StateT M (OptionT (OracleComp …))` over the basic-FS-style
outer spec `D2SChallengePlusUnitOracle challengeSpec`. -/
abbrev GImpl {κ : Type} (challengeSpec : OracleSpec κ) (M : Type) :=
  QueryImpl (gSpec (U := U) StmtIn pSpec δ)
    (StateT M
      (OptionT (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec))))

end TransformTypes
