# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 1552 files, 21672 declarations

## Same short-name across multiple files (861 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `reduction` (13 declarations, 12 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:115](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L115) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CheckClaim.reduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:56](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L56) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib/ProofSystem/Component/DoNothing.lean:44](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L44) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib/ProofSystem/Component/NoInteraction.lean:62](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L62) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → OracleC
- `def ReduceClaim.reduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:56](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L56) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib/ProofSystem/Component/SendWitness.lean:78](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L78) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib/ProofSystem/Fri/Spec/General.lean:107](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L107) — (no docstring)
- `inductive reduction` [ArkLib/ProofSystem/Logup/Security/BridgeAndAppendResiduals.lean:36](../../../ArkLib/ProofSystem/Logup/Security/BridgeAndAppendResiduals.lean#L36) — (no docstring)
- `def Sumcheck.Spec.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:168](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L168) — The sum-check protocol as a reduction
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:642](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L642) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1377](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1377) — The sum-check reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Spec.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:499](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L499) — Honest reduction for Construction 6.2: the package `{prover, verifier}` over the bundled-input `Redu
- `def ToyProblem.SimplifiedIOR.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:168](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L168) — Honest reduction for Construction 6.9.

### `pSpec` (13 declarations, 11 files)

- `def RandomQuery.pSpec` [ArkLib/ProofSystem/Component/RandomQuery.lean:56](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L56) — (no docstring)
- `def SendClaim.pSpec` [ArkLib/ProofSystem/Component/SendClaim.lean:32](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L32) — (no docstring)
- `def SendWitness.pSpec` [ArkLib/ProofSystem/Component/SendWitness.lean:54](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L54) — (no docstring)
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:349](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L349) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:666](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L666) — The final folding round of the FRI protocol begins with the verifier sending a random field element
- `def Fri.Spec.QueryRound.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:977](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L977) — (no docstring)
- `def Logup.pSpec` [ArkLib/ProofSystem/Logup/Protocol.lean:80](../../../ArkLib/ProofSystem/Logup/Protocol.lean#L80) — Protocol 2 transcript shape: the outer LogUp messages followed by ArkLib's generic sumcheck.
- `def StirIOP.Round.pSpec` [ArkLib/ProofSystem/Stir/RoundProtocol.lean:60](../../../ArkLib/ProofSystem/Stir/RoundProtocol.lean#L60) — The protocol spec of one STIR fold round: the verifier first sends a folding challenge in `F` (`V_to
- `def Sumcheck.Spec.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:125](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L125) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L149) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[
- `def ToyProblem.Spec.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:132](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L132) — Protocol specification for Construction 6.2: three rounds, in the order V → P  (γ : F)            --
- `def ToyProblem.SimplifiedIOR.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:108](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L108) — Protocol specification for Construction 6.9: a single `V → P` round sending the combination randomne
- `def WhirIOP.FoldRound.pSpec` [ArkLib/ProofSystem/Whir/FoldRound.lean:149](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L149) — Protocol spec: the verifier sends a fold challenge `α : F`, then the prover sends the folded oracle

### `oracleVerifier` (11 declarations, 10 files)

- `def CheckClaim.oracleVerifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:250](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L250) — The oracle verifier for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleVerifier` [ArkLib/ProofSystem/Component/DoNothing.lean:106](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L106) — The oracle verifier for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleVerifier` [ArkLib/ProofSystem/Component/RandomQuery.lean:88](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L88) — The oracle verifier simply returns the challenge, and performs no checks.
- `def ReduceClaim.oracleVerifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:197](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L197) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleVerifier` [ArkLib/ProofSystem/Component/SendClaim.lean:67](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L67) — The verifier checks that the relationship `rel oldStmt newStmt` holds. It has access to the original
- `def SendSingleWitness.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:353](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L353) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:196](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L196) — (no docstring)
- `def Sumcheck.Spec.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:158](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L158) — The oracle verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:702](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L702) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1358](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1358) — The oracle verifier for the `i`-th round of the sum-check protocol. Migrated to the new `OracleState
- `def ToyProblem.Spec.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:576](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L576) — Oracle verifier for Construction 6.2. Queries the prover's message `g` once and the two oracle codew

### `OracleStatement` (10 declarations, 10 files)

- `abbrev Interaction.OracleStatement` [ArkLib/Interaction/Oracle/Core.lean:100](../../../ArkLib/Interaction/Oracle/Core.lean#L100) — (no docstring)
- `def BatchedFri.Spec.OracleStatement` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:46](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L46) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:861](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L861) — For the `i`-th round of the protocol, there will be oracle statements corresponding to all committed
- `def R1CS.OracleStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:48](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L48) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:89](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L89) — For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the beginning
- `abbrev Spartan.Spec.OracleStatement` [ArkLib/ProofSystem/Spartan/Basic.lean:60](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L60) — This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R`
- `def StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:84](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L84) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:136](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L136) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual
- `def ToyProblem.Spec.OracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:99](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L99) — Oracle statements of Construction 6.2: the two purported codewords `f₁, f₂ : ι → F`. The verifier on
- `def WhirIOP.OracleStatement` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:146](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L146) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type

### `oracleReduction` (11 declarations, 9 files)

- `def CheckClaim.oracleReduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:258](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L258) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib/ProofSystem/Component/DoNothing.lean:116](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L116) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def RandomQuery.oracleReduction` [ArkLib/ProofSystem/Component/RandomQuery.lean:106](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L106) — Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction: the input o
- `def ReduceClaim.oracleReduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:203](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L203) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleReduction` [ArkLib/ProofSystem/Component/SendClaim.lean:96](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L96) — Combine the prover and verifier into an oracle reduction. The input has no statement or witness, but
- `def SendSingleWitness.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:366](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L366) — (no docstring)
- `def Sumcheck.Spec.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:180](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L180) — The sum-check protocol as an oracle reduction
- `def Sumcheck.Spec.SingleRound.Simpler.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:566](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L566) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:721](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L721) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1387](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1387) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol. Migrated to the new `
- `def ToyProblem.Spec.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:608](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L608) — Honest oracle reduction for Construction 6.2: the `OracleProver` / `OracleVerifier` pair packaged as

### `verifier` (11 declarations, 9 files)

- `def CheckClaim.verifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:51](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L51) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib/ProofSystem/Component/DoNothing.lean:35](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L35) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib/ProofSystem/Component/NoInteraction.lean:53](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L53) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a function
- `def ReduceClaim.verifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:52](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L52) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib/ProofSystem/Component/SendWitness.lean:74](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L74) — (no docstring)
- `def Sumcheck.Spec.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L149) — The verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:633](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L633) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1348](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1348) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1896](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1896) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`
- `def ToyProblem.Spec.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:485](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L485) — Honest verifier for Construction 6.2. Takes the bundled input `(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂
- `def ToyProblem.SimplifiedIOR.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:157](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L157) — Honest verifier for Construction 6.9. Reads `γ` from the transcript and produces the new statement `

### `inputRelation` (11 declarations, 8 files)

- `def BatchedFri.Spec.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/General.lean:67](../../../ArkLib/ProofSystem/BatchedFri/Spec/General.lean#L67) — (no docstring)
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:69](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L69) — (no docstring)
- `def Fri.Spec.inputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:46](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L46) — (no docstring)
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:283](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L283) — The FRI non-final folding round input relation, with proximity parameter `0 < δ`, for the `i`-th rou
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:604](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L604) — Input relation for the final folding round, with proximity parameter `0 < δ`. Two conditions (mirror
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:956](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L956) — (no docstring)
- `def Logup.inputRelation` [ArkLib/ProofSystem/Logup/Common.lean:264](../../../ArkLib/ProofSystem/Logup/Common.lean#L264) — Semantic input relation for Protocol 2: every lookup-column value occurs in the table range.
- `def Sumcheck.Spec.SingleRound.Simpler.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:338](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L338) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:596](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L596) — (no docstring)
- `def ToyProblem.Spec.inputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:187](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L187) — The IOR-shaped input relation derived from `ToyProblem.relation` (Definition 6.1). `((v, μ₁, μ₂), (f
- `def WhirIOP.FoldRound.inputRelation` [ArkLib/ProofSystem/Whir/FoldRound.lean:210](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L210) — Input relation: the committed oracle is a codeword of the level-`j` smooth code of degree-budget `M

### `oracleProver` (9 declarations, 8 files)

- `def CheckClaim.oracleProver` [ArkLib/ProofSystem/Component/CheckClaim.lean:237](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L237) — The oracle prover for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleProver` [ArkLib/ProofSystem/Component/DoNothing.lean:101](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L101) — The oracle prover for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleProver` [ArkLib/ProofSystem/Component/RandomQuery.lean:68](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L68) — The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`, a
- `def ReduceClaim.oracleProver` [ArkLib/ProofSystem/Component/ReduceClaim.lean:187](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L187) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleProver` [ArkLib/ProofSystem/Component/SendClaim.lean:40](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L40) — The prover takes in the old oracle statement as input, and sends it as the protocol message.
- `def SendWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:269](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L269) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:337](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L337) — The oracle prover for the `SendSingleWitness` oracle reduction. The prover sends the witness `wit` t
- `def RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:148](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L148) — (no docstring)
- `def ToyProblem.Spec.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:528](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L528) — Same as `prover` but exposed at the `OracleProver` signature. The underlying `Prover` is identical (

### `prover` (9 declarations, 8 files)

- `def CheckClaim.prover` [ArkLib/ProofSystem/Component/CheckClaim.lean:40](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L40) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib/ProofSystem/Component/DoNothing.lean:31](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L31) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib/ProofSystem/Component/NoInteraction.lean:43](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L43) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib/ProofSystem/Component/ReduceClaim.lean:44](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L44) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib/ProofSystem/Component/SendWitness.lean:64](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L64) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:611](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L611) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1886](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1886) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-
- `def ToyProblem.Spec.prover` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:441](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L441) — Honest prover for Construction 6.2. After receiving the combination randomness `γ`, the prover sends
- `def ToyProblem.SimplifiedIOR.prover` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:126](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L126) — Honest prover for Construction 6.9. After receiving `γ`, sets the new witness `M_new := M₀ + γ·M₁` a

### `relation` (9 declarations, 8 files)

- `def ArkLib.Lattices.ModuleSIS.relation` [ArkLib/Data/Lattices/ModuleSIS.lean:85](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L85) — The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short, and lies in the k
- `def ConstraintSystem.relation` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:68](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L68) — The underlying set-theoretic relation at a given index.
- `def Lookup.relation` [ArkLib/ProofSystem/ConstraintSystem/Lookup.lean:25](../../../ArkLib/ProofSystem/ConstraintSystem/Lookup.lean#L25) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:128](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L128) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L161) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:193](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L193) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:61](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L61) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise
- `abbrev Spartan.Spec.relation` [ArkLib/ProofSystem/Spartan/Basic.lean:68](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L68) — This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨`
- `def ToyProblem.relation` [ArkLib/ProofSystem/ToyProblem/Definitions.lean:78](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean#L78) — **Definition 6.1 of [ABF26]** (toy problem relation `R_C^ℓ`). Given a base code `C ⊆ (ι → F)` (the p

### `outputRelation` (10 declarations, 7 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:85](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L85) — (no docstring)
- `def Fri.Spec.outputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:56](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L56) — (no docstring)
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:312](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L312) — The FRI non-final folding round output relation, with proximity parameter `0 < δ`, for the `i`-th ro
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:634](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L634) — Output relation for the final folding round. After the final round the prover sends a polynomial in
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:964](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L964) — (no docstring)
- `def Logup.outputRelation` [ArkLib/ProofSystem/Logup/Common.lean:299](../../../ArkLib/ProofSystem/Logup/Common.lean#L299) — The full protocol has a trivial final relation: successful verification returns `Unit`.
- `def Sumcheck.Spec.SingleRound.Simpler.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:367](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L367) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:599](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L599) — (no docstring)
- `def ToyProblem.Spec.outputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:266](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L266) — The IOR-shaped *relaxed* output relation derived from `ToyProblem.relaxedRelation` (Definition 6.3).
- `def WhirIOP.FoldRound.outputRelation` [ArkLib/ProofSystem/Whir/FoldRound.lean:216](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L216) — Output relation: the folded oracle is a codeword of the level-`(j+1)` smooth code of degree-budget `

### `getElem` (7 declarations, 7 files)

- `theorem Array.getElem` [ArkLib/Data/Array/Lemmas.lean:63](../../../ArkLib/Data/Array/Lemmas.lean#L63) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:88](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L88) — Shifting a tracked slot through `eraseIdx` of a different index.
- `theorem DuplexSpongeFS.EagerLazyDS.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:959](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L959) — The `getElem?` position map of `eraseIdx`: deleting index `i` shifts later positions by one, for all
- `lemma DuplexSpongeFS.Sponge316.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:137](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L137) — Shifting a tracked slot through `eraseIdx` of a different index.
- `lemma DuplexSpongeFS.Sponge316.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:88](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L88) — Shifting a tracked slot through `eraseIdx` of a different index.
- `lemma DuplexSpongeFS.Sponge316.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:137](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L137) — Shifting a tracked slot through `eraseIdx` of a different index.
- `theorem DuplexSpongeFS.EagerLazyDS.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:959](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L959) — The `getElem?` position map of `eraseIdx`: deleting index `i` shifts later positions by one, for all

### `Witness` (6 declarations, 6 files)

- `def BatchedFri.Spec.Witness` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:54](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L54) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:924](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L924) — The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and `Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁'
- `def R1CS.Witness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:51](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L51) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:110](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L110) — The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in the
- `abbrev Spartan.Spec.Witness` [ArkLib/ProofSystem/Spartan/Basic.lean:64](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L64) — This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R`
- `def ToyProblem.Spec.Witness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:107](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L107) — Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose encodings are the oracle codeword

### `append` (6 declarations, 5 files)

- `def AGM.GroupRepresentation.append` [ArkLib/AGM/RepresentationLemmas.lean:164](../../../ArkLib/AGM/RepresentationLemmas.lean#L164) — **Representations compose multiplicatively.** Concatenating the bases and exponent vectors of two al
- `def Interaction.Oracle.Spec.append` [ArkLib/Interaction/Oracle/Spec.lean:216](../../../ArkLib/Interaction/Oracle/Spec.lean#L216) — (no docstring)
- `abbrev ProtocolSpec.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:36](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L36) — Appending two `ProtocolSpec`s
- `def ProtocolSpec.FullTranscript.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:147](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L147) — Appending two transcripts for two `ProtocolSpec`s
- `def CWSSStructure.append` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean:84](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean#L84) — Binary append of coordinate-wise special-soundness structures. On left challenge rounds this is `D₁`
- `def ProtocolSpec.ChallengeTreeShape.append` [ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean:96](../../../ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean#L96) — Append two protocol-generic tree shapes along sequential protocol append.

### `Statement` (5 declarations, 5 files)

- `def R1CS.Statement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:45](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L45) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:80](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L80) — For the `i`-th round of the protocol, the input statement is equal to the challenges sent from round
- `abbrev Spartan.Spec.Statement` [ArkLib/ProofSystem/Spartan/Basic.lean:56](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L56) — This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R`
- `structure Sumcheck.Structured.Statement` [ArkLib/ProofSystem/Sumcheck/Structured.lean:197](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L197) — Statement per iterated sumcheck round
- `def ToyProblem.Spec.Statement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:93](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L93) — Input (explicit) statement of Construction 6.2: the linear-constraint vector `v ∈ F^k` and the two c

### `liftComp_optionT_pure` (5 declarations, 5 files)

- `lemma StirIOP.Round3.liftComp_optionT_pure` [ArkLib/ProofSystem/Stir/CheckedFinalBlock.lean:277](../../../ArkLib/ProofSystem/Stir/CheckedFinalBlock.lean#L277) — Spec-lifting an `OptionT`-level `pure` is `pure` (definitional; the WHIR `CheckedVerifier` helper).
- `lemma Whir302Checked.liftComp_optionT_pure` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:913](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L913) — Spec-lifting an `OptionT`-level `pure` is `pure` (definitional).
- `lemma Whir302.liftComp_optionT_pure` [ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean:66](../../../ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean#L66) — Spec-lifting an `OptionT`-level `pure` is `pure` (definitional).
- `lemma Whir302RBR.liftComp_optionT_pure` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:413](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L413) — Spec-lifting an `OptionT`-level `pure` is `pure` (definitional).
- `lemma Fri.Spec.Completeness.liftComp_optionT_pure` [ArkLib/ToMathlib/FriCompletePerRound.lean:112](../../../ArkLib/ToMathlib/FriCompletePerRound.lean#L112) — Spec-lifting an `OptionT`-level `pure` is `pure` (definitional); cf. the WHIR sibling `liftComp_opti

### `oracleVerifier_rbrKnowledgeSoundness` (5 declarations, 5 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:132](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L132) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:351](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L351) — The `RandomQuery` oracle reduction is round-by-round knowledge sound. The key fact governing the sou
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:326](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L326) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/RbrKnowledgeSoundnessOracle.lean:168](../../../ArkLib/ProofSystem/Sumcheck/Spec/RbrKnowledgeSoundnessOracle.lean#L168) — **The full multi-round sum-check ORACLE verifier is round-by-round knowledge sound** on the canonica
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1220](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1220) — Round-by-round knowledge soundness for the oracle verifier

### `OStmtIn` (5 declarations, 4 files)

- `def RandomQuery.OStmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:36](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L36) — (no docstring)
- `def Logup.OStmtIn` [ArkLib/ProofSystem/Logup/Common.lean:241](../../../ArkLib/ProofSystem/Logup/Common.lean#L241) — Input oracle statements: the table `t` and lookup columns `fᵢ`, as multilinear oracles.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:336](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L336) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:591](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L591) — (no docstring)
- `def WhirIOP.FoldRound.OStmtIn` [ArkLib/ProofSystem/Whir/FoldRound.lean:135](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L135) — The oracle message type for this round: the single committed codeword as a function on the relevant

### `OStmtOut` (5 declarations, 4 files)

- `def RandomQuery.OStmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:37](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L37) — (no docstring)
- `def Logup.OStmtOut` [ArkLib/ProofSystem/Logup/Common.lean:290](../../../ArkLib/ProofSystem/Logup/Common.lean#L290) — Output oracle statements for the full LogUp protocol.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:365](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L365) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:594](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L594) — (no docstring)
- `def WhirIOP.FoldRound.OStmtOut` [ArkLib/ProofSystem/Whir/FoldRound.lean:138](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L138) — (no docstring)

### `StmtIn` (5 declarations, 4 files)

- `def RandomQuery.StmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:33](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L33) — (no docstring)
- `structure Logup.StmtIn` [ArkLib/ProofSystem/Logup/Common.lean:233](../../../ArkLib/ProofSystem/Logup/Common.lean#L233) — Public parameter assumptions for Protocol 2. The paper fixes a finite field with characteristic larg
- `def Sumcheck.Spec.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:137](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L137) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simpler.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:335](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L335) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:585](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L585) — (no docstring)

### `oracleReduction_perfectCompleteness` (5 declarations, 4 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:126](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L126) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/OracleCompletenessThreaded.lean:80](../../../ArkLib/ProofSystem/Sumcheck/Spec/OracleCompletenessThreaded.lean#L80) — **Per-round oracle perfect completeness.** The `i`-th-round oracle reduction `SingleRound.oracleRedu
- `theorem Sumcheck.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/OracleCompletenessThreaded.lean:117](../../../ArkLib/ProofSystem/Sumcheck/Spec/OracleCompletenessThreaded.lean#L117) — **Full multi-round sum-check perfect completeness (oracle level) — without the false bridge.** Assem
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1033](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1033) — Perfect completeness for the oracle reduction
- `theorem ToyProblem.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:945](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L945) — **Honest completeness for Construction 6.2** (protocol-level form). The honest oracle reduction is p

### `reduction_perfectCompleteness` (5 declarations, 4 files)

- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:52](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L52) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem Fri.Spec.Completeness.reduction_perfectCompleteness` [ArkLib/ProofSystem/Fri/Spec/Completeness.lean:128](../../../ArkLib/ProofSystem/Fri/Spec/Completeness.lean#L128) — **Brick D — composed FRI reduction perfect completeness.** The honest FRI protocol is perfectly comp
- `theorem Sumcheck.Spec.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/Completeness.lean:87](../../../ArkLib/ProofSystem/Sumcheck/Spec/Completeness.lean#L87) — **Full multi-round sum-check perfect completeness (`Reduction` level).** Assembled from the per-roun
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:742](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L742) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1785](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1785) — (no docstring)

### `disagreementSet` (4 declarations, 4 files)

- `def disagreementSet` [ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean#L63) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁. Specialisation of the canonical `Code.disagr
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean:464](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean#L464) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i) and g^(i),
- `def Quotienting.disagreementSet` [ArkLib/ProofSystem/Stir/Quotienting.lean:121](../../../ArkLib/ProofSystem/Stir/Quotienting.lean#L121) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S such that
- `def BlockRelDistance.disagreementSet` [ArkLib/ProofSystem/Whir/BlockRelDistance.lean:104](../../../ArkLib/ProofSystem/Whir/BlockRelDistance.lean#L104) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)

### `instOracleVerifierAppendCoherent` (4 declarations, 4 files)

- `instance RandomQuery.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/Component/RandomQuery.lean:112](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L112) — (no docstring)
- `instance SendSingleWitness.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/Component/SendWitness.lean:372](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L372) — (no docstring)
- `instance RingSwitching.BatchingPhase.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:239](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L239) — The batching-phase oracle verifier passes every output oracle through to the unchanged input oracle
- `instance Sumcheck.Spec.SingleRound.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1365](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1365) — The `i`-th-round oracle verifier routes its (single) output oracle to the (unchanged) input oracle (

### `reduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:71](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L71) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib/ProofSystem/Component/NoInteraction.lean:93](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L93) — Completeness of a no-interaction reduction. **Faithfulness of the hypothesis `hRel`.** `Reduction.ru
- `theorem ReduceClaim.reduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:66](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L66) — The `ReduceClaim` reduction satisfies perfect completeness for any relation.
- `theorem SendWitness.reduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:174](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L174) — The `SendWitness` reduction satisfies perfect completeness.

### `Entry` (4 declarations, 4 files)

- `abbrev DuplexSpongeFS.Sponge316.ForkCounter.Entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L67) — Entry type at `StmtIn := Unit`, `U := UInt8` (sponge geometry `{N := 2, R := 1}` inherited from `Tim
- `abbrev DuplexSpongeFS.Sponge316.ForkCounter.Entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L67) — Entry type at `StmtIn := Unit`, `U := UInt8` (sponge geometry `{N := 2, R := 1}` inherited from `Tim
- `abbrev DuplexSpongeFS.Sponge316.TimePCounter.Entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:73](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L73) — (no docstring)
- `abbrev DuplexSpongeFS.Sponge316.TimePCounter.Entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:73](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L73) — (no docstring)

### `dedup_eq` (4 declarations, 4 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:307](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L307) — The dedup fixpoint of `trcF` is `trcD`: classical choice first erases slot 2 or slot 4, and both bra
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:307](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L307) — The dedup fixpoint of `trcF` is `trcD`: classical choice first erases slot 2 or slot 4, and both bra
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:244](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L244) — The dedup fixpoint of the countermodel trace is `trc'` (erase slot 3, then stop).
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:244](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L244) — The dedup fixpoint of the countermodel trace is `trc'` (erase slot 3, then stop).

### `dedup_eq'` (4 declarations, 4 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L354) — Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L354) — Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L263) — Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L263) — Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.

### `foldl_add_eq_sum` (4 declarations, 4 files)

- `theorem Spartan.Spec.foldl_add_eq_sum` [ArkLib/ProofSystem/Spartan/FirstSumcheckMulVec.lean:36](../../../ArkLib/ProofSystem/Spartan/FirstSumcheckMulVec.lean#L36) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- `theorem Spartan.Spec.foldl_add_eq_sum` [ArkLib/ProofSystem/Spartan/FirstSumcheckZeroEval.lean:39](../../../ArkLib/ProofSystem/Spartan/FirstSumcheckZeroEval.lean#L39) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- `theorem Sumcheck.Spec.SingleRound.foldl_add_eq_sum` [ArkLib/ProofSystem/Sumcheck/Spec/SimpleRoundCoherent.lean:78](../../../ArkLib/ProofSystem/Sumcheck/Spec/SimpleRoundCoherent.lean#L78) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- `theorem Sumcheck.Spec.SingleRound.foldl_add_eq_sum` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRoundFaithful.lean:56](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRoundFaithful.lean#L56) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`. (Local c

### `smallSponge` (4 declarations, 4 files)

- `instance DuplexSpongeFS.Sponge314.K1.smallSponge` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:51](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L51) — Tiny sponge geometry: width 2, rate 1, capacity 1 (same as `Lemma516TimePFalse`).
- `instance DuplexSpongeFS.Sponge316.TimePCounter.smallSponge` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:60](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L60) — Tiny sponge geometry: width 2, rate 1, capacity 1 — capacities are single `UInt8`s.
- `instance DuplexSpongeFS.Sponge314.K1.smallSponge` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:51](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L51) — Tiny sponge geometry: width 2, rate 1, capacity 1 (same as `Lemma516TimePFalse`).
- `instance DuplexSpongeFS.Sponge316.TimePCounter.smallSponge` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:60](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L60) — Tiny sponge geometry: width 2, rate 1, capacity 1 — capacities are single `UInt8`s.

### `vsum_two_pos` (4 declarations, 4 files)

- `theorem RingSwitching.vsum_two_pos` [ArkLib/ProofSystem/RingSwitching/WiringInstances.lean:81](../../../ArkLib/ProofSystem/RingSwitching/WiringInstances.lean#L81) — The sumcheck loop (over any `NeZero` number of rounds) has positive length.
- `theorem Spartan.Spec.Bricks.vsum_two_pos` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:291](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L291) — Positivity of two-step round counts.
- `theorem Spartan.Spec.Bricks.vsum_two_pos` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:84](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L84) — Positivity of two-step round counts.
- `theorem Spartan.Spec.Bricks.vsum_two_pos` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:34](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L34) — Positivity of two-step round counts.

### `seqCompose` (10 declarations, 3 files)

- `def Prover.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:37](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L37) — Sequential composition of provers, defined via iteration of the composition (append) of two provers.
- `def Verifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:75](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L75) — Sequential composition of verifiers, defined via iteration of the composition (append) of two verifi
- `def Reduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:104](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L104) — Sequential composition of reductions, defined via sequential composition of provers and verifiers (o
- `def OracleProver.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:135](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L135) — Sequential composition of provers in oracle reductions, defined via sequential composition of prover
- `def OracleVerifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:188](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L188) — Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the comp
- `def OracleReduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:310](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L310) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:342](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L342) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:400](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L400) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit
- `def ChallengeTreeShape.seqCompose` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean:53](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean#L53) — Sequential composition of a finite family of generic challenge-tree shapes.
- `def CWSSStructure.seqCompose` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean:191](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean#L191) — Sequential composition of a finite family of CWSS structures.

### `completeness` (6 declarations, 3 files)

- `abbrev DuplexSpongeFS.NARG.completeness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:59](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L59) — Paper-facing alias for CO25 Section 3.4 completeness.
- `def Reduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:117](../../../ArkLib/OracleReduction/Security/Basic.lean#L117) — A reduction satisfies **completeness** with regards to: - an initialization function `init : ProbCom
- `def OracleReduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:463](../../../ArkLib/OracleReduction/Security/Basic.lean#L463) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:517](../../../ArkLib/OracleReduction/Security/Basic.lean#L517) — (no docstring)
- `def OracleProof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:546](../../../ArkLib/OracleReduction/Security/Basic.lean#L546) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `theorem SendClaim.completeness` [ArkLib/ProofSystem/Component/SendClaim.lean:114](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L114) — (no docstring)

### `soundness` (6 declarations, 3 files)

- `abbrev DuplexSpongeFS.NARG.soundness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:72](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L72) — Paper-facing alias for CO25 Section 3.4 soundness.
- `def Verifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:295](../../../ArkLib/OracleReduction/Security/Basic.lean#L295) — A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input langua
- `def OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:484](../../../ArkLib/OracleReduction/Security/Basic.lean#L484) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:527](../../../ArkLib/OracleReduction/Security/Basic.lean#L527) — (no docstring)
- `def OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:563](../../../ArkLib/OracleReduction/Security/Basic.lean#L563) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.soundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:127](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L127) — State-restoration soundness

### `ratchet` (5 declarations, 3 files)

- `def DomainSeparator.ratchet` [ArkLib/Data/Hash/DomainSep.lean:255](../../../ArkLib/Data/Hash/DomainSep.lean#L255) — Ratchet the state. Rust interface: ```rust pub fn ratchet(self) -> Self ```
- `def DuplexSponge.ratchet` [ArkLib/Data/Hash/DuplexSponge.lean:612](../../../ArkLib/Data/Hash/DuplexSponge.lean#L612) — ### Ratchet the sponge state for domain separation Algorithm (from Rust implementation): 1. Permute
- `def HashStateWithInstructions.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:217](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L217) — Perform a ratchet operation. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainS
- `def FSVerifierState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:348](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L348) — Signal the end of statement with ratcheting. Rust interface: ```rust pub fn ratchet(&mut self) -> Re
- `def FSProverState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:459](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L459) — Ratchet the protocol state. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainSe

### `Adversary` (4 declarations, 3 files)

- `def AGM.Adversary` [ArkLib/AGM/Basic.lean:468](../../../ArkLib/AGM/Basic.lean#L468) — An adversary in the Algebraic Group Model (AGM) is defined as follows: - It is given knowledge of th
- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.Adversary` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:92](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L92) — A weak-binding adversary outputs two weak openings for the same commitment.
- `abbrev ArkLib.Lattices.SIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:57](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L57) — A search adversary for a SIS-style problem.
- `abbrev ArkLib.Lattices.ModuleSIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:100](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L100) — A Module-SIS adversary.

### `StmtOut` (4 declarations, 3 files)

- `def RandomQuery.StmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:34](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L34) — (no docstring)
- `def Logup.StmtOut` [ArkLib/ProofSystem/Logup/Common.lean:280](../../../ArkLib/ProofSystem/Logup/Common.lean#L280) — The full LogUp protocol returns no additional public data on success.
- `def Sumcheck.Spec.SingleRound.Simpler.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:364](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L364) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:588](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L588) — (no docstring)

### `correctness` (4 declarations, 3 files)

- `def Commitment.correctness` [ArkLib/Commitments/Functional/Basic.lean:89](../../../ArkLib/Commitments/Functional/Basic.lean#L89) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `def CommitmentScheme.correctness` [ArkLib/Commitments/Functional/CommitmentScheme.lean:64](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L64) — A commitment scheme satisfies **correctness** with error `correctnessError` if, for every message, t
- `theorem KZG.correctness` [ArkLib/Commitments/Functional/KZG/Correctness.lean:51](../../../ArkLib/Commitments/Functional/KZG/Correctness.lean#L51) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib/Commitments/Functional/KZG/Correctness.lean:161](../../../ArkLib/Commitments/Functional/KZG/Correctness.lean#L161) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `drop` (4 declarations, 3 files)

- `def Fin.drop` [ArkLib/Data/Fin/Tuple/Defs.lean:60](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L60) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:129](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L129) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:186](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L186) — (no docstring)
- `def SumcheckDomain.drop` [ArkLib/ProofSystem/Sumcheck/Domain.lean:116](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L116) — Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates: coordinate

### `toFinset` (4 declarations, 3 files)

- `def ReedSolomon.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon.lean:97](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L97) — (no docstring)
- `def Domain.CosetFftDomainClass.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:242](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L242) — (no docstring)
- `abbrev Domain.CosetFftDomain.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:258](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L258) — (no docstring)
- `abbrev Domain.FftDomain.toFinset` [ArkLib/Data/Domain/FftDomain/Defs.lean:126](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L126) — (no docstring)

### `Message` (3 declarations, 3 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Message` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:122](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L122) — Messages: block vectors over the message row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Message` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:32](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L32) — Messages: column vectors over `Rq Φ`.
- `def ProtocolSpec.Message` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:78](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L78) — The type of the `i`-th message in a protocol specification. This does not distinguish between messag

### `Opening` (3 declarations, 3 files)

- `structure Commitment.Opening` [ArkLib/Commitments/Functional/Basic.lean:59](../../../ArkLib/Commitments/Functional/Basic.lean#L59) — The opening protocol used to prove a claimed oracle response for committed data.
- `structure ArkLib.Lattices.Ajtai.InnerOuter.Opening` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:98](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L98) — A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)` (`Decomp`) ext
- `abbrev ArkLib.Lattices.Ajtai.Simple.Opening` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:43](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L43) — The simple Ajtai commitment has no auxiliary opening data.

### `OutputStatement` (3 declarations, 3 files)

- `abbrev Sumcheck.Spec.OutputStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:131](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L131) — (no docstring)
- `def ToyProblem.Spec.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:112](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L112) — Output statement: the IOR is a yes/no test — accept (return `()`) or short-circuit to `none` via `Op
- `def ToyProblem.SimplifiedIOR.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:72](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L72) — Output statement for C6.9: the new `(v, μ_new)` pair. The constraint count drops from 2 to 1 (a sing

### `Params` (3 declarations, 3 files)

- `structure Poseidon2.Params` [ArkLib/Data/Hash/Poseidon2.lean:412](../../../ArkLib/Data/Hash/Poseidon2.lean#L412) — The parameters determining a Poseidon2 permutation (over the KoalaBear field)
- `structure StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:35](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L35) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
- `structure WhirIOP.Params` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:54](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L54) — ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro

### `Prover` (4 declarations, 3 files)

- `abbrev Interaction.Oracle.Prover` [ArkLib/Interaction/Oracle/Core.lean:1140](../../../ArkLib/Interaction/Oracle/Core.lean#L1140) — (no docstring)
- `abbrev Interaction.Prover` [ArkLib/Interaction/Reduction.lean:115](../../../ArkLib/Interaction/Reduction.lean#L115) — (no docstring)
- `structure Prover` [ArkLib/OracleReduction/Basic.lean:168](../../../ArkLib/OracleReduction/Basic.lean#L168) — (no docstring)
- `structure Prover` [ArkLib/OracleReduction/Basic.lean:413](../../../ArkLib/OracleReduction/Basic.lean#L413) — The type of honest provers for an interactive reduction with `n` messages. This consists of: - `PrvS

### `PublicParams` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.PublicParams` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:77](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L77) — Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`.
- `abbrev ArkLib.Lattices.Ajtai.Simple.PublicParams` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:29](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L29) — Public parameters: the Ajtai matrix `A`.
- `structure Spartan.PublicParams` [ArkLib/ProofSystem/Spartan/Basic.lean:26](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L26) — The public parameters of the (padded) Spartan protocol. Consists of the number of bits of the R1CS d

### `Reduction` (3 declarations, 3 files)

- `structure Interaction.Oracle.Reduction` [ArkLib/Interaction/Oracle/Core.lean:1217](../../../ArkLib/Interaction/Oracle/Core.lean#L1217) — (no docstring)
- `structure Interaction.Reduction` [ArkLib/Interaction/Reduction.lean:187](../../../ArkLib/Interaction/Reduction.lean#L187) — (no docstring)
- `structure Reduction` [ArkLib/OracleReduction/Basic.lean:760](../../../ArkLib/OracleReduction/Basic.lean#L760) — An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles def

### `StraightlineExtractor` (3 declarations, 3 files)

- `abbrev Commitment.StraightlineExtractor` [ArkLib/Commitments/Functional/Basic.lean:174](../../../ArkLib/Commitments/Functional/Basic.lean#L174) — A **straightline extractor** for a commitment scheme takes in the commitment, the log of queries mad
- `def CommitmentScheme.StraightlineExtractor` [ArkLib/Commitments/Functional/CommitmentScheme.lean:123](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L123) — A **straightline extractor** for a standard commitment scheme takes the commitment and the log of qu
- `abbrev DuplexSpongeFS.NARG.StraightlineExtractor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:86](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L86) — Paper-facing alias for the straightline extractor interface used in Section 3.4.

### `Verifier` (3 declarations, 3 files)

- `structure Interaction.Oracle.Verifier` [ArkLib/Interaction/Oracle/Core.lean:1180](../../../ArkLib/Interaction/Oracle/Core.lean#L1180) — (no docstring)
- `abbrev Interaction.Verifier` [ArkLib/Interaction/Reduction.lean:130](../../../ArkLib/Interaction/Reduction.lean#L130) — (no docstring)
- `structure Verifier` [ArkLib/OracleReduction/Basic.lean:438](../../../ArkLib/OracleReduction/Basic.lean#L438) — A verifier of an interactive protocol is a function that takes in the input statement and the transc

### `absorb` (3 declarations, 3 files)

- `def DomainSeparator.absorb` [ArkLib/Data/Hash/DomainSep.lean:216](../../../ArkLib/Data/Hash/DomainSep.lean#L216) — Absorb `count` native elements. Rust interface: ```rust pub fn absorb(self, count: usize, label: &st
- `def DuplexSponge.absorb` [ArkLib/Data/Hash/DuplexSponge.lean:416](../../../ArkLib/Data/Hash/DuplexSponge.lean#L416) — ### Absorb a list of units into the sponge (paper version) Paper algorithm (process one element at a
- `def HashStateWithInstructions.absorb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:110](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L110) — Perform secure absorption of elements into the sponge. Rust interface: ```rust pub fn absorb(&mut se

### `agree` (3 declarations, 3 files)

- `def CodeGeometry.agree` [ArkLib/Data/CodingTheory/CodeGeometry.lean:38](../../../ArkLib/Data/CodingTheory/CodeGeometry.lean#L38) — (no docstring)
- `def ArkLib.JohnsonBound.agree` [ArkLib/Data/CodingTheory/JohnsonBound/ListSize.lean:54](../../../ArkLib/Data/CodingTheory/JohnsonBound/ListSize.lean#L54) — The number of coordinates on which `c` and `w` agree.
- `def ProximityGap.WeightedAgreement.agree` [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean:236](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean#L236) — Relative `μ`-agreement between words `u` and `v`.

### `binding` (3 declarations, 3 files)

- `def Commitment.binding` [ArkLib/Commitments/Functional/Basic.lean:167](../../../ArkLib/Commitments/Functional/Basic.lean#L167) — A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all adversar
- `def CommitmentScheme.binding` [ArkLib/Commitments/Functional/CommitmentScheme.lean:104](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L104) — A commitment scheme satisfies **binding** with error `bindingError` if every adversary's probability
- `theorem KZG.CommitmentScheme.binding` [ArkLib/Commitments/Functional/KZG/Binding.lean:737](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L737) — The KZG scheme satisfies evaluation binding provided `t`-SDH holds.

### `coeffHom` (3 declarations, 3 files)

- `def ProximityPrize.BCIKS20.GammaGenuine.coeffHom` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean:87](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean#L87) — The per-`Y`-coefficient ring hom `F[X][Y] → (𝕃 H)⟦X⟧`: recenter the `X`-layer at `x₀` (`taylorAlgHom
- `def ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:244](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L244) — Reading off the `k`-th coefficient of the underlying polynomial, as an additive homomorphism `Rq Φ →
- `def CompPoly.CPolynomial.coeffHom` [ArkLib/ToCompPoly/Univariate/Basic.lean:291](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L291) — Extracting the `k`-th coefficient as an additive homomorphism.

### `coeff_pow_sub_at` (3 declarations, 3 files)

- `theorem ProximityPrize.HenselExistence.coeff_pow_sub_at` [ArkLib/Data/Polynomial/HenselExistence.lean:89](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L89) — Local copy of `NewtonLinearization.coeff_pow_sub_at` (order-`t` Newton linearization).
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_pow_sub_at` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:94](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L94) — **LEMMA B (Newton power linearization).** Local copy of `NewtonLinearization.coeff_pow_sub_at`.
- `theorem ProximityPrize.NewtonLinearization.coeff_pow_sub_at` [ArkLib/Data/Polynomial/NewtonLinearization.lean:98](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L98) — **Newton linearization at order `t`.** Under the below-`t` agreement hypothesis with `0 < t`, writin

### `coeff_pow_sub_below` (3 declarations, 3 files)

- `theorem ProximityPrize.HenselExistence.coeff_pow_sub_below` [ArkLib/Data/Polynomial/HenselExistence.lean:72](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L72) — Local copy of `NewtonLinearization.coeff_pow_sub_below` (truncation propagation).
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_pow_sub_below` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:76](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L76) — **LEMMA A (truncation propagation).** Agreement below order `t` propagates to every power. Local cop
- `theorem ProximityPrize.NewtonLinearization.coeff_pow_sub_below` [ArkLib/Data/Polynomial/NewtonLinearization.lean:62](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L62) — **Truncation propagation.** If `γ₁ γ₂ : R⟦X⟧` agree at every coefficient `j < t`, then so do `γ₁^i`

### `commit` (3 declarations, 3 files)

- `def KZG.commit` [ArkLib/Commitments/Functional/KZG/Basic.lean:55](../../../ArkLib/Commitments/Functional/KZG/Basic.lean#L55) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def ArkLib.Lattices.Ajtai.Simple.commit` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:38](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L38) — Deterministically commit by multiplying the public matrix by the message vector.
- `def SimpleRO.commit` [ArkLib/Commitments/Ordinary/SimpleRO.lean:48](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L48) — Commit to message `v` under the random oracle `ro` and randomness `r` by hashing `(v, r)`.

### `commitmentScheme` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commitmentScheme` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:200](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L200) — The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound weak ver
- `def ArkLib.Lattices.Ajtai.Simple.commitmentScheme` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:56](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L56) — The simple Ajtai commitment as a `CommitmentScheme`. An opening is accepted only when the message sa
- `def SimpleRO.commitmentScheme` [ArkLib/Commitments/Ordinary/SimpleRO.lean:58](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L58) — The simple random-oracle commitment as an (ordinary) `CommitmentScheme`. Setup samples a uniformly r

### `coreInteractionOracleReduction` (3 declarations, 3 files)

- `def coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1109](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1109) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1666](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1666) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1809](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1809) — Large-field reduction: Sumcheck seqCompose, then append FinalSum

### `coreInteractionOracleVerifier` (3 declarations, 3 files)

- `def coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1093](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1093) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1647](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1647) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1773](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1773) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum

### `evalDist_map_bijective_uniformSample` (3 declarations, 3 files)

- `theorem ArkLib.SeamChallengeRestriction.evalDist_map_bijective_uniformSample` [ArkLib/OracleReduction/Composition/Sequential/SeamChallengeRestriction.lean:49](../../../ArkLib/OracleReduction/Composition/Sequential/SeamChallengeRestriction.lean#L49) — **Uniform sampling pushed along a bijection.** For a bijection `f : α → β`, the pushforward of the u
- `theorem OptionTStateT.evalDist_map_bijective_uniformSample` [ArkLib/OracleReduction/RunUnroll.lean:384](../../../ArkLib/OracleReduction/RunUnroll.lean#L384) — **Uniform sampling pushed along a bijection.** Generalizes `evalDist_cast_uniformSample` from a type
- `lemma evalDist_map_bijective_uniformSample` [ArkLib/ToVCVio/UniformFamilyComap.lean:58](../../../ArkLib/ToVCVio/UniformFamilyComap.lean#L58) — **Pushing a uniform sample through a bijection is uniform.** `evalDist` form of `probOutput_map_bije

### `finalSumcheckOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:127](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L127) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:668](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L668) — The oracle reduction for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1307](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1307) — The oracle reduction for the final sumcheck step

### `finalSumcheckOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:141](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L141) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1129](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1129) — Perfect completeness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1450](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1450) — **Final-sumcheck perfect completeness — proven.** The single-message final sumcheck reduction is per

### `finalSumcheckProver` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckProver` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:67](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L67) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L610) — The prover for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1210](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1210) — The prover for the final sumcheck step

### `finalSumcheckVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:101](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L101) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:644](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L644) — The verifier for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1246](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1246) — The verifier for the final sumcheck step

### `foldOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean:117](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean#L117) — (no docstring)
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:534](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L534) — The oracle reduction that is the `i`-th round of the FRI protocol.
- `def WhirIOP.FoldRound.foldOracleReduction` [ArkLib/ProofSystem/Whir/FoldRound.lean:201](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L201) — The honest WHIR fold round as an oracle reduction.

### `fullOracleProof` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:98](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L98) — The full Binary Basefold protocol as a Proof
- `def Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:173](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L173) — The full Binary Basefold protocol as a Proof
- `def RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:114](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L114) — The full Binary Basefold protocol as a Proof

### `fullOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:70](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L70) — The reduction for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:142](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L142) — The reduction for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:101](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L101) — The reduction for the full Binary Basefold protocol, using the strict-track batching/core relation n

### `fullOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:113](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L113) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:193](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L193) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/General.lean:516](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L516) — **Issue #29: end-to-end RingSwitching perfect completeness (unconditional core).** The former five a

### `fullOracleVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:47](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L47) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:116](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L116) — The oracle verifier for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:63](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L63) — The oracle verifier for the full Binary Basefold protocol

### `fullOracleVerifier_rbrKnowledgeSoundness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:145](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L145) — Round-by-round knowledge soundness for the full Binary Basefold oracle verifier
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:239](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L239) — Round-by-round knowledge soundness for the full FRI-Binius oracle verifier.
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/General.lean:215](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L215) — Round-by-round knowledge soundness for the full ring-switching oracle verifier. `IsDomain K` (with t

### `fullOracleVerifier_rbrKnowledgeSoundness_wired` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness_wired` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:255](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L255) — **Round-by-round knowledge soundness of the full Binary Basefold oracle verifier, wired** (stateless
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness_wired` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:608](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L608) — **Round-by-round knowledge soundness of the full FRI-Binius oracle verifier, wired (issue #313, stat
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness_wired` [ArkLib/ProofSystem/RingSwitching/RbrKnowledgeWiringFull.lean:119](../../../ArkLib/ProofSystem/RingSwitching/RbrKnowledgeWiringFull.lean#L119) — **Round-by-round knowledge soundness of the full ring-switching oracle verifier, wired** — no append

### `fullRbrKnowledgeError` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:135](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L135) — Combined RBR knowledge soundness error for the full protocol
- `def Binius.FRIBinius.FullFRIBinius.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:229](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L229) — Combined RBR knowledge error for full FRI-Binius.
- `def RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/General.lean:199](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L199) — (no docstring)

### `honestTranscriptDist_oracleReduction_evalDist` (3 declarations, 3 files)

- `theorem RandomQuery.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/RandomQuery.lean:212](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L212) — The honest transcript distribution for `RandomQuery` is definitionally the simulator distribution.
- `theorem SendClaim.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/SendClaim.lean:254](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L254) — The honest transcript distribution for `SendClaim` is exactly the simulator distribution, because th
- `theorem SendSingleWitness.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/SendWitness.lean:438](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L438) — The honest transcript distribution for `SendSingleWitness` is the deterministic one-message transcri

### `knowledgeStateFunction` (3 declarations, 3 files)

- `def CheckClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/CheckClaim.lean:174](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L174) — The knowledge state function for the `CheckClaim` reduction. Since there is no challenge round, the
- `def RandomQuery.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomQuery.lean:306](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L306) — The knowledge state function for the `RandomQuery` oracle reduction.
- `def ReduceClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:135](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L135) — The knowledge state function for the `ReduceClaim` reduction.

### `oracleReduction_completeness` (3 declarations, 3 files)

- `theorem RandomQuery.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomQuery.lean:130](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L130) — The `RandomQuery` oracle reduction is perfectly complete.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:219](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L219) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. Proof strategy m
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:514](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L514) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.

### `oracleReduction_isHVZK` (3 declarations, 3 files)

- `theorem DoNothing.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:194](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L194) — The `DoNothing` oracle reduction has an explicit perfect-HVZK simulator for any oracle-input relatio
- `theorem RandomQuery.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:240](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L240) — `RandomQuery` has an explicit perfect-HVZK simulator as an oracle reduction.
- `theorem SendClaim.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:285](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L285) — `SendClaim` has an explicit perfect-HVZK simulator as an oracle reduction.

### `oracleReduction_isStatHVZK` (3 declarations, 3 files)

- `theorem DoNothing.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:202](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L202) — The `DoNothing` oracle reduction has statistical HVZK for any oracle-input relation and error budget
- `theorem RandomQuery.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:248](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L248) — `RandomQuery` has statistical HVZK at every error budget as an oracle reduction.
- `theorem SendClaim.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:295](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L295) — `SendClaim` has statistical HVZK at every error budget as an oracle reduction.

### `oracleReduction_perfectHVZK` (3 declarations, 3 files)

- `theorem DoNothing.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:176](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L176) — The `DoNothing` oracle reduction is perfectly HVZK for any oracle-input relation.
- `theorem RandomQuery.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:221](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L221) — `RandomQuery` is perfectly HVZK as an oracle reduction: it has no private witness, and the single ve
- `theorem SendClaim.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:264](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L264) — `SendClaim` is perfectly HVZK as an oracle reduction for any input relation: the protocol has no pri

### `oracleReduction_statisticalHVZK` (3 declarations, 3 files)

- `theorem DoNothing.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:185](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L185) — The `DoNothing` oracle reduction is statistically HVZK for any oracle-input relation and error budge
- `theorem RandomQuery.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:231](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L231) — Perfect HVZK implies statistical HVZK for `RandomQuery` at every error budget.
- `theorem SendClaim.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:275](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L275) — Perfect HVZK implies statistical HVZK for `SendClaim` at every error budget.

### `rbrExtractionFailureEvent` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.rbrExtractionFailureEvent` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:320](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L320) — **RBR Extraction Failure Event**: Generic predicate for round-by-round knowledge soundness. This cap
- `def RingSwitching.BatchingPhase.rbrExtractionFailureEvent` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:911](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L911) — Extraction-failure/doom-escape event for the batching phase RBR proof.
- `def RingSwitching.SumcheckPhase.rbrExtractionFailureEvent` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:894](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L894) — Extraction failure implies a witness-dependent bad sumcheck event. The extracted `witMid` also carri

### `relOut` (3 declarations, 3 files)

- `def CheckClaim.relOut` [ArkLib/ProofSystem/Component/CheckClaim.lean:64](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L64) — (no docstring)
- `def RandomQuery.relOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:52](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L52) — The output relation states that if the verifier's single query was `q`, then `a` and `b` agree on th
- `def SendClaim.relOut` [ArkLib/ProofSystem/Component/SendClaim.lean:102](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L102) — (no docstring)

### `rename_finCongr_heq` (3 declarations, 3 files)

- `lemma RingSwitching.SumcheckPhase.rename_finCongr_heq` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:317](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L317) — Renaming a polynomial along the canonical index `finCongr` of a (propositional) dimension equality `
- `lemma Sumcheck.Structured.rename_finCongr_heq` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:140](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L140) — Renaming a polynomial along the canonical index `finCongr` of a dimension equality is heterogeneousl
- `theorem MvPolynomial.rename_finCongr_heq` [ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean:46](../../../ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean#L46) — Renaming along the canonical `finCongr` of a dimension equality is heterogeneously equal to the orig

### `seqComposeError_eq_append` (3 declarations, 3 files)

- `theorem Verifier.seqComposeError_eq_append` [ArkLib/OracleReduction/Composition/Sequential/General.lean:608](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L608) — The RBR error of a sequential composition, expressed via `seqComposeChallengeIdxToSigma` over the *g
- `theorem ArkLib.SeqComposeRbrKnowledge.seqComposeError_eq_append` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:130](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L130) — **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global challenge inde
- `theorem ArkLib.SeqComposeRbrSoundness.seqComposeError_eq_append` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:152](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L152) — **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global challenge inde

### `simulateQ_simOracle2_messageQuery` (3 declarations, 3 files)

- `lemma RingSwitching.BatchingPhase.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:71](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L71) — Local message-query collapse for `OracleInterface.simOracle2`.
- `lemma RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1521](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1521) — **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
- `lemma ToyProblem.Spec.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:718](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L718) — `simOracle2` message-query collapse (`OracleComp` form), RIGHT (message) family.

### `squeeze` (3 declarations, 3 files)

- `def DomainSeparator.squeeze` [ArkLib/Data/Hash/DomainSep.lean:241](../../../ArkLib/Data/Hash/DomainSep.lean#L241) — Squeeze `count` native elements. Rust interface: ```rust pub fn squeeze(self, count: usize, label: &
- `def DuplexSponge.squeeze` [ArkLib/Data/Hash/DuplexSponge.lean:512](../../../ArkLib/Data/Hash/DuplexSponge.lean#L512) — ### Squeeze out a vector of units from the sponge (paper version) We differ from the paper version i
- `def HashStateWithInstructions.squeeze` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:149](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L149) — Perform a secure squeeze operation. Rust interface: ```rust pub fn squeeze(&mut self, output: &mut [

### `toVerifier` (3 declarations, 3 files)

- `def Interaction.OracleDecoration.OracleReduction.toVerifier` [ArkLib/Interaction/Oracle/Core.lean:1096](../../../ArkLib/Interaction/Oracle/Core.lean#L1096) — (no docstring)
- `def Interaction.PublicCoinVerifier.toVerifier` [ArkLib/Interaction/Reduction.lean:162](../../../ArkLib/Interaction/Reduction.lean#L162) — (no docstring)
- `def OracleVerifier.toVerifier` [ArkLib/OracleReduction/Basic.lean:553](../../../ArkLib/OracleReduction/Basic.lean#L553) — An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface using it

### `transcriptSimulator` (3 declarations, 3 files)

- `def RandomQuery.transcriptSimulator` [ArkLib/ProofSystem/Component/RandomQuery.lean:203](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L203) — The simulator for `RandomQuery`: the protocol is witness-free, so the simulator can rerun the honest
- `def SendClaim.transcriptSimulator` [ArkLib/ProofSystem/Component/SendClaim.lean:246](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L246) — The simulator for `SendClaim`: the component has no private witness, so the simulator can run the ho
- `def SendWitness.transcriptSimulator` [ArkLib/ProofSystem/Component/SendWitness.lean:103](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L103) — The simulator for the `SendWitness` reduction when the relation's witness is determined by the input

### `verify` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.Simple.verify` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:46](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L46) — Verify a simple Ajtai opening by checking the matrix product.
- `def SimpleRO.verify` [ArkLib/Commitments/Ordinary/SimpleRO.lean:51](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L51) — Verify an opening `r` of the commitment `cm` to message `v` by recomputing the hash.
- `def OracleVerifier.Append.verify` [ArkLib/OracleReduction/Composition/Sequential/Append.lean:374](../../../ArkLib/OracleReduction/Composition/Sequential/Append.lean#L374) — The composite `verify`: run `V₁` (routed by `router₁`) to obtain the intermediate statement, then ru

### `uniform_event_mass` (3 declarations, 3 files)

- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:55](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L55) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly
- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:166](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L166) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly
- `theorem uniform_event_mass` [ArkLib/ToMathlib/CountingAgreementBricks.lean:109](../../../ArkLib/ToMathlib/CountingAgreementBricks.lean#L109) — The mass of a finite event under the uniform distribution is its cardinality divided by the sample-s

### `audit` (3 declarations, 3 files)

- `axiom audit` [ArkLib/ProofSystem/Logup/Security/LogupCompletenessUncond.lean:84](../../../ArkLib/ProofSystem/Logup/Security/LogupCompletenessUncond.lean#L84) — (no docstring)
- `axiom audit` [ArkLib/ProofSystem/Logup/Security/LogupProtocol2Status.lean:95](../../../ArkLib/ProofSystem/Logup/Security/LogupProtocol2Status.lean#L95) — (no docstring)
- `axiom audit` [ArkLib/ProofSystem/Logup/Security/LogupSoundnessUncond.lean:84](../../../ArkLib/ProofSystem/Logup/Security/LogupSoundnessUncond.lean#L84) — (no docstring)

### `composedPSpec_dir_seam` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.composedPSpec_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:428](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L428) — Seam-direction fact for `firstMessage ▷ sfx1`: the combined spec (= `composedPSpec`) at the seam ind
- `theorem Spartan.Spec.Bricks.composedPSpec_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:223](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L223) — Seam-direction fact for `firstMessage ▷ sfx1`: the combined spec (= `composedPSpec`) at the seam ind
- `theorem Spartan.Spec.Bricks.composedPSpec_dir_seam` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:171](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L171) — Seam-direction fact for `firstMessage ▷ sfx1`: the combined spec (= `composedPSpec`) at the seam ind

### `mem_of_getElem` (3 declarations, 3 files)

- `lemma DuplexSpongeFS.Sponge316.mem_of_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L54) — Membership from an `getElem?`-hit.
- `lemma DuplexSpongeFS.Sponge316.mem_of_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:157](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L157) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.mem_of_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:157](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L157) — (no docstring)

### `secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` [ArkLib/ProofSystem/Spartan/TightComposedComplete.lean:278](../../../ArkLib/ProofSystem/Spartan/TightComposedComplete.lean#L278) — **Leaf `h₇` (tight chain): the binding strengthening of the carried second sum-check completeness.**
- `theorem Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:264](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L264) — **The binding strengthening of the carried second sum-check completeness** (#329, B7): the enriched
- `theorem Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` [ArkLib/ProofSystem/Spartan/TightSecondBinding.lean:47](../../../ArkLib/ProofSystem/Spartan/TightSecondBinding.lean#L47) — **The binding strengthening of the carried second sum-check completeness** (#329, B7): the enriched

### `sfx1_dir_seam` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx1_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:412](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L412) — Seam-direction fact for `firstChallenge ▷ sfx2`: the combined spec (= `sfx1`) at the seam index `1`
- `theorem Spartan.Spec.Bricks.sfx1_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:207](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L207) — Seam-direction fact for `firstChallenge ▷ sfx2`: the combined spec (= `sfx1`) at the seam index `1`
- `theorem Spartan.Spec.Bricks.sfx1_dir_seam` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:155](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L155) — Seam-direction fact for `firstChallenge ▷ sfx2`: the combined spec (= `sfx1`) at the seam index `1`

### `sfx1_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx1_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:400](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L400) — `sfx1 = ⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2` opens `V_to_P`.
- `theorem Spartan.Spec.Bricks.sfx1_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:195](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L195) — `sfx1 = ⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2` opens `V_to_P`.
- `theorem Spartan.Spec.Bricks.sfx1_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:143](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L143) — `sfx1 = ⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2` opens `V_to_P`.

### `sfx2_dir_seam` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx2_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:386](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L386) — Seam-direction fact for `firstSumcheck ▷ sfx3`: the combined spec (= `sfx2`) at the seam index `vsum
- `theorem Spartan.Spec.Bricks.sfx2_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:181](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L181) — Seam-direction fact for `firstSumcheck ▷ sfx3`: the combined spec (= `sfx2`) at the seam index `vsum
- `theorem Spartan.Spec.Bricks.sfx2_dir_seam` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:129](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L129) — Seam-direction fact for `firstSumcheck ▷ sfx3`: the combined spec (= `sfx2`) at the seam index `vsum

### `sfx2_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx2_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:372](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L372) — `sfx2 = sumcheck₃ ++ₚ sfx3` opens `P_to_V` (first sum-check's leading message).
- `theorem Spartan.Spec.Bricks.sfx2_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:167](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L167) — `sfx2 = sumcheck₃ ++ₚ sfx3` opens `P_to_V` (first sum-check's leading message).
- `theorem Spartan.Spec.Bricks.sfx2_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:115](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L115) — `sfx2 = sumcheck₃ ++ₚ sfx3` opens `P_to_V` (first sum-check's leading message).

### `sfx3_dir_seam` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx3_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:361](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L361) — Seam-direction fact for `sendEvalClaim ▷ sfx4`: the combined spec (= `sfx3`) at the seam index `1` i
- `theorem Spartan.Spec.Bricks.sfx3_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:156](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L156) — Seam-direction fact for `sendEvalClaim ▷ sfx4`: the combined spec (= `sfx3`) at the seam index `1` i
- `theorem Spartan.Spec.Bricks.sfx3_dir_seam` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:104](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L104) — Seam-direction fact for `sendEvalClaim ▷ sfx4`: the combined spec (= `sfx3`) at the seam index `1` i

### `sfx3_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx3_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:351](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L351) — `sfx3 = ⟨P_to_V, EvalClaim⟩ ++ₚ sfx4` opens `P_to_V` (the bundled eval-claim message).
- `theorem Spartan.Spec.Bricks.sfx3_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:146](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L146) — `sfx3 = ⟨P_to_V, EvalClaim⟩ ++ₚ sfx4` opens `P_to_V` (the bundled eval-claim message).
- `theorem Spartan.Spec.Bricks.sfx3_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:94](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L94) — `sfx3 = ⟨P_to_V, EvalClaim⟩ ++ₚ sfx4` opens `P_to_V` (the bundled eval-claim message).

### `sfx4_dir_seam` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx4_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:340](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L340) — Seam-direction fact for `linearCombination ▷ sfx5`: the combined spec (= `sfx4`) at the seam index `
- `theorem Spartan.Spec.Bricks.sfx4_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:135](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L135) — Seam-direction fact for `linearCombination ▷ sfx5`: the combined spec (= `sfx4`) at the seam index `
- `theorem Spartan.Spec.Bricks.sfx4_dir_seam` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:83](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L83) — Seam-direction fact for `linearCombination ▷ sfx5`: the combined spec (= `sfx4`) at the seam index `

### `sfx4_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx4_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:330](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L330) — `sfx4 = ⟨V_to_P, LinComb⟩ ++ₚ sfx5` opens `V_to_P` (the linear-combination challenge).
- `theorem Spartan.Spec.Bricks.sfx4_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:125](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L125) — `sfx4 = ⟨V_to_P, LinComb⟩ ++ₚ sfx5` opens `V_to_P` (the linear-combination challenge).
- `theorem Spartan.Spec.Bricks.sfx4_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:73](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L73) — `sfx4 = ⟨V_to_P, LinComb⟩ ++ₚ sfx5` opens `V_to_P` (the linear-combination challenge).

### `sfx5_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx5_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:319](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L319) — `sfx5 = !p[] ++ₚ sfx6` opens `P_to_V`. (Also the seam-direction fact for the `prependRLCTarget ▷ …`
- `theorem Spartan.Spec.Bricks.sfx5_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:112](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L112) — `sfx5 = !p[] ++ₚ sfx6` opens `P_to_V`. (Also the seam-direction fact for the `prependRLCTarget ▷ …`
- `theorem Spartan.Spec.Bricks.sfx5_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:62](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L62) — `sfx5 = !p[] ++ₚ sfx6` opens `P_to_V`. (Also the seam-direction fact for the `prependRLCTarget ▷ …`

### `sfx6_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx6_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:307](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L307) — `sfx6 = sumcheck₂ ++ₚ !p[]` opens `P_to_V` (second sum-check's leading message).
- `theorem Spartan.Spec.Bricks.sfx6_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:100](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L100) — `sfx6 = sumcheck₂ ++ₚ !p[]` opens `P_to_V` (second sum-check's leading message).
- `theorem Spartan.Spec.Bricks.sfx6_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:50](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L50) — `sfx6 = sumcheck₂ ++ₚ !p[]` opens `P_to_V` (second sum-check's leading message).

### `sumcheckPSpec_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sumcheckPSpec_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:297](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L297) — The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message.
- `theorem Spartan.Spec.Bricks.sumcheckPSpec_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:90](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L90) — The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message.
- `theorem Spartan.Spec.Bricks.sumcheckPSpec_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:40](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L40) — The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message.

### `cast_id` (9 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib/OracleReduction/Cast.lean:53](../../../ArkLib/OracleReduction/Cast.lean#L53) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib/OracleReduction/Cast.lean:77](../../../ArkLib/OracleReduction/Cast.lean#L77) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib/OracleReduction/Cast.lean:99](../../../ArkLib/OracleReduction/Cast.lean#L99) — (no docstring)
- `theorem Reduction.cast_id` [ArkLib/OracleReduction/Cast.lean:272](../../../ArkLib/OracleReduction/Cast.lean#L272) — (no docstring)
- `theorem ProtocolSpec.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:35](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L35) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:79](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L79) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:118](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L118) — (no docstring)
- `theorem ProtocolSpec.Transcript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:162](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L162) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:188](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L188) — (no docstring)

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:48](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L48) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:83](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L83) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:113](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L113) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:204](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L204) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:347](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L347) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:358](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L358) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:405](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L405) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:416](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L416) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:465](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L465) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:504](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L504) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:31](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L31) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:155](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L155) — Adding a message with a given direction and type to the end of a `Transcript`

### `knowledgeSoundness` (5 declarations, 2 files)

- `def Verifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:357](../../../ArkLib/OracleReduction/Security/Basic.lean#L357) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:492](../../../ArkLib/OracleReduction/Security/Basic.lean#L492) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:533](../../../ArkLib/OracleReduction/Security/Basic.lean#L533) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:571](../../../ArkLib/OracleReduction/Security/Basic.lean#L571) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.knowledgeSoundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:195](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L195) — State-restoration knowledge soundness (w/ straightline extractor).

### `new` (5 declarations, 2 files)

- `def DomainSeparator.Op.new` [ArkLib/Data/Hash/DomainSep.lean:138](../../../ArkLib/Data/Hash/DomainSep.lean#L138) — Construct a new `Op` from a character `id` and a count number `count : Option Nat`. Returns error if
- `def DomainSeparator.new` [ArkLib/Data/Hash/DomainSep.lean:193](../../../ArkLib/Data/Hash/DomainSep.lean#L193) — Create a new DomainSeparator with the domain separator. Rust interface: ```rust pub fn new(session_i
- `def HashStateWithInstructions.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:98](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L98) — Initialize a stateful hash object from a domain separator. Rust interface: ```rust pub fn new(domain
- `def FSVerifierState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:275](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L275) — Create a new VerifierState from a domain separator and NARG string. Rust interface: ```rust pub fn n
- `def FSProverState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:416](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L416) — Create a new `FSProverState` from a domain separator and RNG. Rust interface: ```rust pub fn new(dom

### `perfectCompleteness` (5 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.perfectCompleteness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:66](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L66) — Paper-facing alias for CO25 Section 3.4 perfect completeness.
- `def Reduction.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:126](../../../ArkLib/OracleReduction/Security/Basic.lean#L126) — A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`.
- `def OracleReduction.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:472](../../../ArkLib/OracleReduction/Security/Basic.lean#L472) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:522](../../../ArkLib/OracleReduction/Security/Basic.lean#L522) — (no docstring)
- `def OracleProof.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:555](../../../ArkLib/OracleReduction/Security/Basic.lean#L555) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.

### `cast_eq_dcast₂` (4 declarations, 2 files)

- `theorem Verifier.cast_eq_dcast₂` [ArkLib/OracleReduction/Cast.lean:107](../../../ArkLib/OracleReduction/Cast.lean#L107) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:91](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L91) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:130](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L130) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:194](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L194) — (no docstring)

### `instDCast₂` (4 declarations, 2 files)

- `instance Prover.instDCast₂` [ArkLib/OracleReduction/Cast.lean:60](../../../ArkLib/OracleReduction/Cast.lean#L60) — (no docstring)
- `instance ProtocolSpec.MessageIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:87](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L87) — (no docstring)
- `instance ProtocolSpec.ChallengeIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:126](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L126) — (no docstring)
- `instance ProtocolSpec.FullTranscript.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:190](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L190) — (no docstring)

### `subdomain` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:88](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L88) — Given a smooth coset FFT domain `ω` of log-order `n` this function returns its subdomain of log-orde
- `abbrev Domain.CosetFftDomain.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:449](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L449) — (no docstring)
- `def Domain.FftDomainClass.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:44](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L44) — (no docstring)
- `abbrev Domain.FftDomain.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:134](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L134) — (no docstring)

### `toList` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:37](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L37) — (no docstring)
- `def Domain.CosetFftDomain.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:52](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L52) — Convert a coset FFT domain into a list of all its members with proofs the members belong to the FFT
- `def Domain.FftDomain.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:63](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L63) — Convert a FFT domain into a list of all its members with proofs the members belong to the FFT domain
- `def ProtocolSpec.EncodedMessagesBefore.toList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L77) — Flatten to a sigma-list for consumers still expecting `List (Sigma ...)`.

### `accepts` (3 declarations, 2 files)

- `def Plonk.Gate.accepts` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:58](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L58) — A gate accepts an input vector `x` if its evaluation at `x` is zero.
- `def Plonk.ConstraintSystem.accepts` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:129](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L129) — A constraint system accepts an input vector `x` if all of its gates accept `x`.
- `def ToyProblem.Spec.accepts` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:176](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L176) — The §6.1 decision predicate, factored out so completeness proofs and the verifier object share the s

### `advantage` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:409](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L409) — Weak-binding advantage.
- `def ArkLib.Lattices.SIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:66](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L66) — Search advantage for a SIS-style problem.
- `def ArkLib.Lattices.ModuleSIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:112](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L112) — The Module-SIS advantage.

### `domain` (3 declarations, 2 files)

- `def ArkLib.BoundaryCardResidualRefutation.domain` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean:53](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean#L53) — Four distinct evaluation points in `ZMod 5`.
- `def Fri.Domain.domain` [ArkLib/ProofSystem/Fri/Domain.lean:41](../../../ArkLib/ProofSystem/Fri/Domain.lean#L41) — Allows us to enumerate the elements of the subgroup defined above.
- `def Fri.CosetDomain.domain` [ArkLib/ProofSystem/Fri/Domain.lean:451](../../../ArkLib/ProofSystem/Fri/Domain.lean#L451) — (no docstring)

### `experiment` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.experiment` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:396](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L396) — The Hachi/Greyhound weak-binding experiment. ## Ordinary vs. weak binding *Ordinary (exact) binding*
- `def ArkLib.Lattices.SIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:60](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L60) — The SIS experiment: sample a challenge, run the adversary, check validity.
- `def ArkLib.Lattices.ModuleSIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:106](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L106) — The Module-SIS experiment.

### `extract` (3 declarations, 2 files)

- `def Fin.extract` [ArkLib/Data/Fin/Tuple/Defs.lean:73](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L73) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:137](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L137) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:194](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L194) — (no docstring)

### `fst` (3 declarations, 2 files)

- `def Prover.fst` [ArkLib/OracleReduction/Composition/Sequential/SeamDecomposition.lean:52](../../../ArkLib/OracleReduction/Composition/Sequential/SeamDecomposition.lean#L52) — **Phase-1 seam restriction of a (malicious) prover** over `pSpec₁ ++ₚ pSpec₂`. Runs rounds `0 .. m-1
- `def ProtocolSpec.Transcript.fst` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:119](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L119) — The first half of a partial transcript for a concatenated protocol, up to round `k < m + n + 1`. Thi
- `def ProtocolSpec.FullTranscript.fst` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:214](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L214) — The first half of a transcript for a concatenated protocol

### `mem_toFinset_iff_mem` (3 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:71](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L71) — (no docstring)
- `lemma Domain.CosetFftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:117](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L117) — (no docstring)
- `lemma Domain.FftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/FftDomain/Mem.lean:69](../../../ArkLib/Data/Domain/FftDomain/Mem.lean#L69) — (no docstring)

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib/Data/Fin/Tuple/Defs.lean:68](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L68) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:133](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L133) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:190](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L190) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib/Data/Fin/Tuple/Defs.lean:55](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L55) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:125](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L125) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:182](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L182) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `snd` (3 declarations, 2 files)

- `def Prover.snd` [ArkLib/OracleReduction/Composition/Sequential/SeamDecomposition.lean:90](../../../ArkLib/OracleReduction/Composition/Sequential/SeamDecomposition.lean#L90) — **Phase-2 seam restriction of a (malicious) prover** over `pSpec₁ ++ₚ pSpec₂`. Resumes from `P`'s se
- `def ProtocolSpec.Transcript.snd` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:128](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L128) — The second half of a partial transcript for a concatenated protocol.
- `def ProtocolSpec.FullTranscript.snd` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:220](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L220) — The second half of a transcript for a concatenated protocol

### `BindingAdversary` (2 declarations, 2 files)

- `structure Commitment.BindingAdversary` [ArkLib/Commitments/Functional/Basic.lean:115](../../../ArkLib/Commitments/Functional/Basic.lean#L115) — An adversary in the (evaluation) binding game returns a commitment `cm`, a query `q`, two purported
- `structure CommitmentScheme.BindingAdversary` [ArkLib/Commitments/Functional/CommitmentScheme.lean:89](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L89) — An adversary in the binding game returns a commitment and two purported openings to possibly differe

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:66](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L66) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib/OracleReduction/VectorIOR.lean:54](../../../ArkLib/OracleReduction/VectorIOR.lean#L54) — The type of indices for challenges in a `VectorSpec`.

### `Codec` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.Codec` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:204](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L204) — Paper-facing alias for CO25 Definition 4.1 codecs.
- `class ProtocolSpec.Codec` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L99) — Codec class for CO25 Definition 4.1. `Codec pSpec U` is the generic-parameter carrier for everything

### `Commit` (2 declarations, 2 files)

- `structure Commitment.Commit` [ArkLib/Commitments/Functional/Basic.lean:53](../../../ArkLib/Commitments/Functional/Basic.lean#L53) — The commitment algorithm, parameterized by the committer key and the data to commit.
- `structure CommitmentScheme.Commit` [ArkLib/Commitments/Functional/CommitmentScheme.lean:38](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L38) — The commitment algorithm, returning both the commitment and its opening value.

### `Commitment` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Commitment` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:126](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L126) — Inner-outer commitments live in the outer row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Commitment` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:35](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L35) — Commitments: row vectors over `Rq Φ`.

### `ConstraintSystem` (2 declarations, 2 files)

- `structure ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:49](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L49) — A **constraint system** packages a family of indexed relations into a single bundle. For each `i : I
- `def Plonk.ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:116](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L116) — A Plonk constraint system is a vector of `numGates` gates, each parametrized by the underlying ring

### `CurveCoeffPolys` (2 declarations, 2 files)

- `def ArkLib.BetaToCurveCoeffPolys.CurveCoeffPolys` [ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean:100](../../../ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean#L100) — Asserts that each coefficient of the decoded polynomial $P(z)$ at index $j < deg$ is interpolated by
- `def ArkLib.KeystoneCapstone.CurveCoeffPolys` [ArkLib/ToMathlib/KeystoneCapstone.lean:92](../../../ArkLib/ToMathlib/KeystoneCapstone.lean#L92) — (no docstring)

### `E_col_p` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_col_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:261](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L261) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_col_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:237](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L237) — (no docstring)

### `E_col_p_pinv` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_col_p_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:279](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L279) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_col_p_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:255](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L255) — (no docstring)

### `E_col_pinv` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_col_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:270](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L270) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_col_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:246](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L246) — (no docstring)

### `E_col_pinv_p` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_col_pinv_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:288](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L288) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_col_pinv_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:264](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L264) — (no docstring)

### `E_dup` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_dup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:211](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L211) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_dup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:187](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L187) — (no docstring)

### `E_func` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_func` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:223](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L223) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_func` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:199](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L199) — (no docstring)

### `E_h` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_h` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:166](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L166) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_h` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:142](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L142) — (no docstring)

### `E_p` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:185](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L185) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:161](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L161) — (no docstring)

### `E_pinv` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:204](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L204) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:180](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L180) — (no docstring)

### `E_prp` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_prp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:293](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L293) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_prp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:269](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L269) — (no docstring)

### `ExtractabilityAdversary` (2 declarations, 2 files)

- `abbrev Commitment.ExtractabilityAdversary` [ArkLib/Commitments/Functional/Basic.lean:179](../../../ArkLib/Commitments/Functional/Basic.lean#L179) — An adversary in the extractability game is an oracle computation that returns a commitment, a query,
- `structure CommitmentScheme.ExtractabilityAdversary` [ArkLib/Commitments/Functional/CommitmentScheme.lean:137](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L137) — An adversary in the extractability game returns a commitment, a claimed message/opening pair, and au

### `FinalOracleStatement` (2 declarations, 2 files)

- `def Fri.Spec.FinalOracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:97](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L97) — (no docstring)
- `def Spartan.Spec.Bricks.FinalOracleStatement` [ArkLib/ToMathlib/SpartanBricks.lean:102](../../../ArkLib/ToMathlib/SpartanBricks.lean#L102) — The terminal oracle-statement family: unchanged from after the second sum-check (`bundled (v_A,v_B,v

### `FinalStatement` (2 declarations, 2 files)

- `def Fri.Spec.FinalStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:83](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L83) — (no docstring)
- `def Spartan.Spec.Bricks.FinalStatement` [ArkLib/ToMathlib/SpartanBricks.lean:97](../../../ArkLib/ToMathlib/SpartanBricks.lean#L97) — The terminal claim statement type: the full Spartan statement after the second sum-check (`(r_y, (r_

### `GenMutualCorrParams` (2 declarations, 2 files)

- `class Fold.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/Folding.lean:683](../../../ArkLib/ProofSystem/Whir/Folding.lean#L683) — The `GenMutualCorrParams` class captures the necessary parameters and assumptions to model a sequenc
- `class WhirIOP.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:85](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L85) — `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes `C_{i : M + 1, j : foldingPar

### `KeyGen` (2 declarations, 2 files)

- `structure Commitment.KeyGen` [ArkLib/Commitments/Functional/Basic.lean:49](../../../ArkLib/Commitments/Functional/Basic.lean#L49) — Key generation for a commitment scheme, producing a committer key and a verifier key.
- `structure CommitmentScheme.KeyGen` [ArkLib/Commitments/Functional/CommitmentScheme.lean:34](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L34) — The key-generation algorithm, returning separate keys for the committer and verifier.

### `MLE_eval_eq_sum_eqTilde` (2 declarations, 2 files)

- `theorem MvPolynomial.MLE_eval_eq_sum_eqTilde` [ArkLib/Data/MvPolynomial/Multilinear.lean:319](../../../ArkLib/Data/MvPolynomial/Multilinear.lean#L319) — **MLE evaluation as an eq-weighted sum over the hypercube.**  Evaluating the multilinear extension a
- `lemma RingSwitching.MLE_eval_eq_sum_eqTilde` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1119](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1119) — **MLE evaluation as an `eq̃`-weighted hypercube sum.** Evaluating the multilinear extension `MLE f`

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:61](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L61) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib/OracleReduction/VectorIOR.lean:50](../../../ArkLib/OracleReduction/VectorIOR.lean#L50) — The type of indices for messages in a `VectorSpec`.

### `NoRedundantEntryDSPaper` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.NoRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:57](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L57) — A trace has no paper-redundant entries.
- `def DuplexSpongeFS.Paper.NoRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L67) — No entry of the trace is paper-redundant.

### `OStmt` (2 declarations, 2 files)

- `def StirIOP.Round.OStmt` [ArkLib/ProofSystem/Stir/RoundProtocol.lean:53](../../../ArkLib/ProofSystem/Stir/RoundProtocol.lean#L53) — The single-index oracle statement family for a STIR fold round: the prover holds one oracle function
- `def WhirIOP.Construction.OStmt` [ArkLib/ToMathlib/WhirBricksConstruction.lean:49](../../../ArkLib/ToMathlib/WhirBricksConstruction.lean#L49) — The single-index oracle statement family for the WHIR Vector IOPP: the prover holds one oracle funct

### `OracleProver` (2 declarations, 2 files)

- `abbrev Interaction.OracleDecoration.OracleProver` [ArkLib/Interaction/Oracle/Core.lean:898](../../../ArkLib/Interaction/Oracle/Core.lean#L898) — (no docstring)
- `def OracleProver` [ArkLib/OracleReduction/Basic.lean:446](../../../ArkLib/OracleReduction/Basic.lean#L446) — An **(oracle) prover** in an interactive **oracle** reduction is a prover in the non-oracle reductio

### `OracleReduction` (2 declarations, 2 files)

- `structure Interaction.OracleDecoration.OracleReduction` [ArkLib/Interaction/Oracle/Core.lean:928](../../../ArkLib/Interaction/Oracle/Core.lean#L928) — (no docstring)
- `structure OracleReduction` [ArkLib/OracleReduction/Basic.lean:768](../../../ArkLib/OracleReduction/Basic.lean#L768) — An **interactive oracle reduction** for a given protocol specification `pSpec`, and relative to orac

### `OracleVerifier` (3 declarations, 2 files)

- `structure Interaction.OracleVerifier` [ArkLib/Interaction/Oracle/Core.lean:1042](../../../ArkLib/Interaction/Oracle/Core.lean#L1042) — (no docstring)
- `structure OracleVerifier` [ArkLib/OracleReduction/Basic.lean:175](../../../ArkLib/OracleReduction/Basic.lean#L175) — (no docstring)
- `structure OracleVerifier` [ArkLib/OracleReduction/Basic.lean:466](../../../ArkLib/OracleReduction/Basic.lean#L466) — An **(oracle) verifier** of an interactive **oracle** reduction consists of: - an oracle computation

### `OuterRunSamplesChallenge` (2 declarations, 2 files)

- `def OuterRunSamplesChallenge` [ArkLib/ProofSystem/Logup/Security/OuterRunSamplesChallenge.lean:24](../../../ArkLib/ProofSystem/Logup/Security/OuterRunSamplesChallenge.lean#L24) — (no docstring)
- `def Logup.OuterRunSamplesChallenge` [ArkLib/ProofSystem/Logup/Security/OuterSoundnessReal.lean:224](../../../ArkLib/ProofSystem/Logup/Security/OuterSoundnessReal.lean#L224) — **The genuine residual interface: the outer run samples the challenge.** This is the *only* gap betw

### `OutputOracleStatement` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:116](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L116) — Output oracle statement: the IOR has no output oracle component.
- `def ToyProblem.SimplifiedIOR.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:77](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L77) — Output oracle statement: the single combined codeword `f_new := f₁ + γ·f₂ : ι → F`.

### `OutputWitness` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:120](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L120) — Output witness: empty.
- `def ToyProblem.SimplifiedIOR.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:81](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L81) — Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`.

### `ParamConditions` (2 declarations, 2 files)

- `structure StirIOP.ParamConditions` [ArkLib/ProofSystem/Stir/MainThm.lean:55](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L55) — **Conditions that protocol parameters must satisfy.** - `h_deg` : initial degree `deg` is a power of
- `structure WhirIOP.ParamConditions` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:66](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L66) — ** Conditions that protocol parameters must satisfy. ** h_m : m = varCount₀ h_sumkLt : ∑ i : Fin (M

### `PerRoundProximityGap` (2 declarations, 2 files)

- `def ArkLib.ProofSystem.Stir.ErrorAccumulation.PerRoundProximityGap` [ArkLib/ProofSystem/Stir/ErrorAccumulation.lean:307](../../../ArkLib/ProofSystem/Stir/ErrorAccumulation.lean#L307) — The keystone, abstracted. `PerRoundProximityGap e ProxGapBound` says the accounting per-round error
- `def Core2Keystone.PerRoundProximityGap` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:52](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L52) — Verbatim copy of `Issue24FRISTIR.PerRoundProximityGap` (`Stir/SoundnessAccumulation.lean:253`): the

### `Point` (2 declarations, 2 files)

- `abbrev Point` [ArkLib/Data/CodingTheory/ListDecoding/GuruswamiSudan/Basic.lean:14](../../../ArkLib/Data/CodingTheory/ListDecoding/GuruswamiSudan/Basic.lean#L14) — Represents an evaluation point (x, y)
- `abbrev Rudnev.Point` [ArkLib/ToMathlib/Combinatorics/Additive/RudnevIncidence.lean:81](../../../ArkLib/ToMathlib/Combinatorics/Additive/RudnevIncidence.lean#L81) — A **point** of affine `3`-space is a triple of field elements.

### `Proof` (2 declarations, 2 files)

- `abbrev Interaction.Proof` [ArkLib/Interaction/Reduction.lean:232](../../../ArkLib/Interaction/Reduction.lean#L232) — (no docstring)
- `def Proof` [ArkLib/OracleReduction/Basic.lean:792](../../../ArkLib/OracleReduction/Basic.lean#L792) — An **interactive proof (IP)** is an interactive reduction where the output statement is a boolean, t

### `RewindingExtractor` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.RewindingExtractor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:155](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L155) — Paper-facing alias for the rewinding extractor interface from CO25 Definition 3.8.
- `def Extractor.RewindingExtractor` [ArkLib/ToMathlib/RewindingExtractor.lean:115](../../../ArkLib/ToMathlib/RewindingExtractor.lean#L115) — A **rewinding extractor** for the 2-special-sound case: given the recorded prefix and **two** comple

### `Scheme` (2 declarations, 2 files)

- `structure Commitment.Scheme` [ArkLib/Commitments/Functional/Basic.lean:64](../../../ArkLib/Commitments/Functional/Basic.lean#L64) — A commitment scheme with key generation, commitment, and opening algorithms.
- `structure CommitmentScheme.Scheme` [ArkLib/Commitments/Functional/CommitmentScheme.lean:46](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L46) — An ordinary commitment scheme.

### `SpongeState` (2 declarations, 2 files)

- `class SpongeState` [ArkLib/Data/Hash/DuplexSponge.lean:255](../../../ArkLib/Data/Hash/DuplexSponge.lean#L255) — Type class for the state of a cryptographic permutation used in the duplex sponge construction. Rust
- `abbrev DuplexSpongeFS.SpongeState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:42](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L42) — Paper-facing alias for the canonical duplex-sponge state used in CO25 Section 3.3.

### `SumcheckLensProjComplete` (2 declarations, 2 files)

- `def Logup.SumcheckLensProjComplete` [ArkLib/ProofSystem/Logup/Security/SumcheckCompletenessClose.lean:100](../../../ArkLib/ProofSystem/Logup/Security/SumcheckCompletenessClose.lean#L100) — **The `proj_complete` half of `OracleContext.Lens.IsComplete` for the LogUp sum-check lens.** Every
- `def SumcheckLensProjComplete` [ArkLib/ProofSystem/Logup/Security/SumcheckLensProjComplete.lean:16](../../../ArkLib/ProofSystem/Logup/Security/SumcheckLensProjComplete.lean#L16) — (no docstring)

### `SumcheckMultiplierParam` (2 declarations, 2 files)

- `structure Sumcheck.Structured.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured.lean:85](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L85) — Parameters describing how the round polynomial `H` is built from the witness `t`: `H = P · Q(t)`, wh
- `structure Sumcheck.Structured.Prismalinear.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:50](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L50) — Parameters describing how a *prismalinear* round polynomial `H = P · Q(t)` is built from the witness

### `SumcheckWitness` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckWitness` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:237](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L237) — (no docstring)
- `structure Sumcheck.Structured.SumcheckWitness` [ArkLib/ProofSystem/Sumcheck/Structured.lean:231](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L231) — Witness for the structured sumcheck at round `i`: - `t'` — the original multilinear polynomial (the

### `TranscriptSimulator` (2 declarations, 2 files)

- `abbrev OracleReduction.TranscriptSimulator` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:38](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L38) — Transcript simulators for oracle reductions are simulators for the associated non-oracle reduction,
- `def Reduction.TranscriptSimulator` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:62](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L62) — A transcript simulator produces, from the input statement alone, a distribution over full transcript

### `UDRClose_of_fin_eq` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.UDRClose_of_fin_eq` [ArkLib/ProofSystem/Binius/BinaryBasefold/Reconstruct/UDRCongruence.lean:52](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Reconstruct/UDRCongruence.lean#L52) — **UDR-closeness congruence under domain-index equality.** If the domain indices `i, j : Fin r` are e
- `theorem Binius.BinaryBasefold.CoreInteraction.UDRClose_of_fin_eq` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:771](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L771) — Transport `UDRClose` across an index equality and a heterogeneous function equality.

### `Verifier.run` (2 declarations, 2 files)

- `def Interaction.Verifier.run` [ArkLib/Interaction/Reduction.lean:262](../../../ArkLib/Interaction/Reduction.lean#L262) — (no docstring)
- `def Verifier.run` [ArkLib/OracleReduction/Execution.lean:137](../../../ArkLib/OracleReduction/Execution.lean#L137) — Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and the t

### `WhirRbrKeystone` (2 declarations, 2 files)

- `def Core2Keystone.WhirRbrKeystone` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:80](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L80) — Verbatim copy of `Issue113WHIR.WhirRbrKeystone` (`Whir/RbrBudgetAccounting.lean:238`): the `SoundOk`
- `def Issue113WHIR.WhirRbrKeystone` [ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:253](../../../ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean#L253) — **Named residual (the genuine open per-round soundness math).** `WhirRbrKeystone` abstracts the per-

### `WitIn` (2 declarations, 2 files)

- `def RandomQuery.WitIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:39](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L39) — (no docstring)
- `def Logup.WitIn` [ArkLib/ProofSystem/Logup/Common.lean:368](../../../ArkLib/ProofSystem/Logup/Common.lean#L368) — Protocol 2 has no private witness beyond the input oracles at this layer.

### `agree_add_hammingDist` (2 declarations, 2 files)

- `theorem CodeGeometry.agree_add_hammingDist` [ArkLib/Data/CodingTheory/CodeGeometry.lean:42](../../../ArkLib/Data/CodingTheory/CodeGeometry.lean#L42) — Agreement and Hamming distance partition the coordinate set.
- `theorem ArkLib.JohnsonBound.agree_add_hammingDist` [ArkLib/Data/CodingTheory/JohnsonBound/ListSize.lean:57](../../../ArkLib/Data/CodingTheory/JohnsonBound/ListSize.lean#L57) — Agreement plus Hamming distance equals the block length.

### `answer_instDefault` (2 declarations, 2 files)

- `lemma RingSwitching.BatchingPhase.answer_instDefault` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:66](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L66) — The default oracle interface (`OracleInterface.instDefault`, used by the ring-switching message orac
- `lemma ToyProblem.Spec.answer_instDefault` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:628](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L628) — `answer` of the default oracle interface is the identity (the message itself).

### `answer_instDefault'` (2 declarations, 2 files)

- `lemma RingSwitching.SumcheckPhase.answer_instDefault'` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:87](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L87) — The `instDefault` oracle answer is the message itself (`answer m () = m`).
- `lemma Fri.Spec.Completeness.answer_instDefault'` [ArkLib/ToMathlib/FriCompleteFinalRound.lean:86](../../../ArkLib/ToMathlib/FriCompleteFinalRound.lean#L86) — The default oracle interface answers its only (unit) query with the message itself (local copy of `R

### `appendRbrKnowledgeSoundnessResidual_msg_subsingleton` (2 declarations, 2 files)

- `theorem OracleVerifier.appendRbrKnowledgeSoundnessResidual_msg_subsingleton` [ArkLib/OracleReduction/Composition/Sequential/AppendRbrKnowledgeOracleLift.lean:94](../../../ArkLib/OracleReduction/Composition/Sequential/AppendRbrKnowledgeOracleLift.lean#L94) — **Discharge of the named residual `OracleVerifier.appendRbrKnowledgeSoundnessResidual`** (`Append.le
- `theorem Verifier.appendRbrKnowledgeSoundnessResidual_msg_subsingleton` [ArkLib/OracleReduction/Composition/Sequential/AppendResidualDischarges.lean:93](../../../ArkLib/OracleReduction/Composition/Sequential/AppendResidualDischarges.lean#L93) — **Discharge of the named residual `Verifier.appendRbrKnowledgeSoundnessResidual`** (deterministic-`V

### `appendRbrSoundnessResidual_msg_subsingleton` (2 declarations, 2 files)

- `theorem OracleVerifier.appendRbrSoundnessResidual_msg_subsingleton` [ArkLib/OracleReduction/Composition/Sequential/AppendRbrSoundnessOracleLift.lean:91](../../../ArkLib/OracleReduction/Composition/Sequential/AppendRbrSoundnessOracleLift.lean#L91) — **Discharge of the named residual `OracleVerifier.appendRbrSoundnessResidual`** (`Append.lean`) in t
- `theorem Verifier.appendRbrSoundnessResidual_msg_subsingleton` [ArkLib/OracleReduction/Composition/Sequential/AppendRbrSoundnessPhase2Proof.lean:639](../../../ArkLib/OracleReduction/Composition/Sequential/AppendRbrSoundnessPhase2Proof.lean#L639) — **Discharge of the named residual `Verifier.appendRbrSoundnessResidual`** (`Append.lean`) in the det

### `appendRight` (2 declarations, 2 files)

- `def Interaction.OracleDecoration.QueryHandle.appendRight` [ArkLib/Interaction/Oracle/Core.lean:202](../../../ArkLib/Interaction/Oracle/Core.lean#L202) — (no docstring)
- `def ProtocolSpec.Transcript.appendRight` [ArkLib/OracleReduction/ProtocolSpec/TranscriptRecompose.lean:56](../../../ArkLib/OracleReduction/ProtocolSpec/TranscriptRecompose.lean#L56) — Append a full `pSpec₁` transcript and a *partial* `pSpec₂` transcript into a partial transcript for

### `append_completeness_msg` (3 declarations, 2 files)

- `theorem Reduction.append_completeness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean:211](../../../ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean#L211) — **The error-bearing message-seam append-completeness keystone — no residual hypothesis.** For a mess
- `theorem OracleReduction.append_completeness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean:262](../../../ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean#L262) — **Oracle-level error-bearing append completeness — UNCONDITIONAL (message seam).** Completeness (err
- `theorem Reduction.append_completeness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean:254](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean#L254) — **Non-perfect (error-bearing) message-seam append completeness — fully discharged.** From the compon

### `append_completeness_msg_proof` (2 declarations, 2 files)

- `theorem Reduction.append_completeness_msg_proof` [ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessNonPerfect.lean:133](../../../ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessNonPerfect.lean#L133) — **NON-PERFECT (error-bearing) message-seam append completeness — discharged modulo the named two-sta
- `theorem OracleReduction.append_completeness_msg_proof` [ArkLib/ProofSystem/Logup/Security/LogupCompletenessWired.lean:117](../../../ArkLib/ProofSystem/Logup/Security/LogupCompletenessWired.lean#L117) — **Oracle-level non-perfect append completeness keystone (message seam) — verifier bridge discharged

### `append_dir_seam` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.FullBinaryBasefold.append_dir_seam` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:200](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L200) — Left-boundary direction transport for appended protocols: the appended protocol's direction at the s
- `lemma Binius.FRIBinius.FullFRIBinius.append_dir_seam` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:555](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L555) — Left-boundary direction transport for appended protocols: the appended protocol's direction at the s

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib/Data/Fin/Basic.lean:262](../../../ArkLib/Data/Fin/Basic.lean#L262) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:55](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L55) — (no docstring)

### `append_perfectCompleteness_challenge` (2 declarations, 2 files)

- `theorem Reduction.append_perfectCompleteness_challenge` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessChallenge.lean:255](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessChallenge.lean#L255) — **Challenge-seam append perfect completeness.** The `V_to_P`-seam analogue of `append_perfectComplet
- `theorem OracleReduction.append_perfectCompleteness_challenge` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessOracleChallenge.lean:54](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessOracleChallenge.lean#L54) — **Oracle-level challenge-seam append perfect completeness.** The `V_to_P` analogue of `append_perfec

### `append_perfectCompleteness_msg_proof` (2 declarations, 2 files)

- `theorem OracleReduction.append_perfectCompleteness_msg_proof` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessOracle.lean:81](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessOracle.lean#L81) — **Oracle-level perfect-completeness keystone (message seam).** Perfect completeness of `R₁.append R₂
- `theorem Reduction.append_perfectCompleteness_msg_proof` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessProof.lean:108](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessProof.lean#L108) — (no docstring)

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib/Data/Fin/Basic.lean:270](../../../ArkLib/Data/Fin/Basic.lean#L270) — (no docstring)
- `theorem ProtocolSpec.append_right_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:65](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L65) — (no docstring)

### `append_soundness_challenge` (2 declarations, 2 files)

- `theorem Verifier.append_soundness_challenge` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessChallengeProof.lean:292](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessChallengeProof.lean#L292) — **Unconditional binary append-soundness, challenge-seam case** (the conclusion of `Verifier.append_s
- `theorem OracleVerifier.append_soundness_challenge` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessTotal.lean:130](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessTotal.lean#L130) — **OracleVerifier-level plain-soundness append keystone, challenge seam (unconditional).** The challe

### `append_soundness_msg` (2 declarations, 2 files)

- `theorem Verifier.append_soundness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean:464](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean#L464) — **Unconditional binary append-soundness, message-seam case** (the conclusion of `Verifier.append_sou
- `theorem OracleVerifier.append_soundness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessOracleMsg.lean:62](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessOracleMsg.lean#L62) — **OracleVerifier-level plain-soundness append keystone, message seam (unconditional).** The appended

### `askInput` (2 declarations, 2 files)

- `def StirIOP.MultiRound.askInput` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:141](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L141) — Query the input codeword oracle at a domain point.
- `def Whir302Checked.askInput` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:67](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L67) — Query the public WHIR input oracle at an outer-domain point.

### `askList` (2 declarations, 2 files)

- `def StirIOP.MultiRound.askList` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:157](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L157) — Monadic map over a list with definitional `nil`/`cons` equations (avoiding `List.mapM`'s tail-recurs
- `def Whir302Checked.askList` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:102](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L102) — Monadic map over a list with definitional `nil`/`cons` equations (avoiding `List.mapM`'s tail-recurs

### `askMsg` (2 declarations, 2 files)

- `def StirIOP.MultiRound.askMsg` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:148](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L148) — Query the `j`-th prover message oracle at a vector position.
- `def Whir302Checked.askMsg` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:56](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L56) — Query the `j`-th prover message oracle at a vector position.

### `badCount_udr_le` (2 declarations, 2 files)

- `theorem ProximityGap.UDRwire.badCount_udr_le` [ArkLib/Data/CodingTheory/ProximityGap/MCAUDRBound.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAUDRBound.lean#L51) — (no docstring)
- `theorem ProximityGap.UDR.badCount_udr_le` [ArkLib/Data/CodingTheory/ProximityGap/UDRBadCount.lean:86](../../../ArkLib/Data/CodingTheory/ProximityGap/UDRBadCount.lean#L86) — (no docstring)

### `badGamma_le` (2 declarations, 2 files)

- `theorem ProximityGap.UDRwire.badGamma_le` [ArkLib/Data/CodingTheory/ProximityGap/MCAUDRBound.lean:45](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAUDRBound.lean#L45) — (no docstring)
- `theorem ProximityGap.UDR.badGamma_le` [ArkLib/Data/CodingTheory/ProximityGap/UDRBadCount.lean:81](../../../ArkLib/Data/CodingTheory/ProximityGap/UDRBadCount.lean#L81) — Finite-field specialization of `badGammaOn_le`.

### `badPolyAgreement` (2 declarations, 2 files)

- `def Issue29Ring.badPolyAgreement` [ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean:39](../../../ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean#L39) — **Named per-round residual = the weakened-KState bad event.** The prover message `p` differs from th
- `def KStateWeaken.badPolyAgreement` [ArkLib/ToMathlib/KStateWeaken.lean:70](../../../ArkLib/ToMathlib/KStateWeaken.lean#L70) — **Named per-round residual (weakened KState surface).** `badPolyAgreement r p q` is the bad event to

### `badSumcheckEventProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.badSumcheckEventProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean:621](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean#L621) — The bad sumcheck event, stated at the **polynomial** level. Over `CharP L 2` with `\|L\| = 2`, two *di
- `def RingSwitching.SumcheckPhase.badSumcheckEventProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:258](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L258) — **Named weakened-KState bad event for one ring-switching sumcheck round.** The prover's degree-`≤ 2`

### `batchingCoreRbrKnowledgeError` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:219](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L219) — Combined RBR knowledge error for batching + core interaction.
- `def RingSwitching.FullRingSwitching.batchingCoreRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/General.lean:193](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L193) — (no docstring)

### `batchingCoreReduction` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:97](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L97) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:69](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L69) — (no docstring)

### `batchingCoreVerifier` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:79](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L79) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:45](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L45) — (no docstring)

### `c0_ne_c1` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c0_ne_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:39](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L39) — The three codewords are pairwise distinct.
- `theorem JohnsonBound.JqlRefutation.c0_ne_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:79](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L79) — The three codewords are pairwise distinct.

### `c0_ne_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c0_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:40](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L40) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.c0_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:80](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L80) — (no docstring)

### `c1_ne_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c1_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:41](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L41) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.c1_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:81](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L81) — (no docstring)

### `capacitySegmentDup` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.capacitySegmentDup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:208](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L208) — The combined capacity segment collision event. This occurs if there is any capacity segment collisio
- `def OracleSpec.QueryLog.BadEventDSPaper.capacitySegmentDup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L184) — The combined capacity segment collision event. This occurs if there is any capacity segment collisio

### `capacitySegmentDupHash` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.capacitySegmentDupHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:151](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L151) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.capacitySegmentDupHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:127](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L127) — (no docstring)

### `capacitySegmentDupPerm` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.capacitySegmentDupPerm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:168](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L168) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.capacitySegmentDupPerm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:144](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L144) — (no docstring)

### `capacitySegmentDupPermInv` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.capacitySegmentDupPermInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:187](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L187) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.capacitySegmentDupPermInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:163](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L163) — (no docstring)

### `card` (2 declarations, 2 files)

- `theorem Probability.SizeSubset.card` [ArkLib/Data/Probability/Combinatorial.lean:47](../../../ArkLib/Data/Probability/Combinatorial.lean#L47) — The number of size-`n` subsets of a finite type is `\|α\| choose n`.
- `theorem Probability.SizedSubset.card` [ArkLib/Data/Probability/UniformSubset.lean:43](../../../ArkLib/Data/Probability/UniformSubset.lean#L43) — (no docstring)

### `card_allQueriesIn` (2 declarations, 2 files)

- `theorem Issue14Scratch.card_allQueriesIn` [ArkLib/ProofSystem/BatchedFri/QueryRoundAnalysis.lean:35](../../../ArkLib/ProofSystem/BatchedFri/QueryRoundAnalysis.lean#L35) — (= `Fri.QueryRound.card_allQueriesIn`) The number of length-`t` query tuples landing entirely in `G`
- `theorem Fri.QueryRound.card_allQueriesIn` [ArkLib/ProofSystem/BatchedFri/Security.lean:353](../../../ArkLib/ProofSystem/BatchedFri/Security.lean#L353) — The number of length-`t` query tuples landing entirely in a set `G` is `\|G\| ^ t`. This counts the ac

### `card_filter_eval_eq_le_natDegree` (2 declarations, 2 files)

- `theorem Issue29Ring.card_filter_eval_eq_le_natDegree` [ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean:52](../../../ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean#L52) — **Root-counting core (Schwartz–Zippel, finite-field form).** For two distinct polynomials, the set o
- `theorem KStateWeaken.card_filter_eval_eq_le_natDegree` [ArkLib/ToMathlib/KStateWeaken.lean:91](../../../ArkLib/ToMathlib/KStateWeaken.lean#L91) — **Root-counting core (CompPoly-free).** For two *distinct* polynomials, the set of challenges on whi

### `card_filter_eval_zero_le` (2 declarations, 2 files)

- `theorem RingSwitching.card_filter_eval_zero_le` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1858](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1858) — **Root-set cardinality bound.** Over an integral domain `L`, the number of field elements at which a
- `theorem Polynomial.card_filter_eval_zero_le` [ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean:57](../../../ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean#L57) — **Root-set cardinality bound.** Over a finite integral domain `L`, a nonzero `p : L[X]` vanishes at

### `card_filter_forall_pi` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.card_filter_forall_pi` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:71](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L71) — Counting a coordinatewise event: the tuples satisfying `Q` in every coordinate form the `piFinset` o
- `theorem card_filter_forall_pi` [ArkLib/ToMathlib/CountingAgreementBricks.lean:76](../../../ArkLib/ToMathlib/CountingAgreementBricks.lean#L76) — Count of length-`s` tuples whose every coordinate satisfies `Q` equals `(#Q)^s`.

### `coeffHom_apply` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom_apply` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:249](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L249) — (no docstring)
- `theorem CompPoly.CPolynomial.coeffHom_apply` [ArkLib/ToCompPoly/Univariate/Basic.lean:297](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L297) — (no docstring)

### `coeff_S_eq_zero_of_lt` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_eq_zero_of_lt` [ArkLib/Data/Polynomial/HenselExistence.lean:203](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L203) — The `t`-th partial sum is supported on `[0, t]`: every coefficient above order `t` vanishes. (`S t`
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_eq_zero_of_lt` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:280](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L280) — `S t` is supported on `[0, t]`: every coefficient above order `t` vanishes.

### `coeff_S_stable` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_stable` [ArkLib/Data/Polynomial/HenselExistence.lean:214](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L214) — Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`. The diagonal value is reached a
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_stable` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:290](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L290) — Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`.

### `coeff_S_succ_of_le` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_succ_of_le` [ArkLib/Data/Polynomial/HenselExistence.lean:197](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L197) — Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_succ_of_le` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:275](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L275) — Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.

### `coeff_aeval_eq_sum_range` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_aeval_eq_sum_range` [ArkLib/Data/Polynomial/HenselExistence.lean:65](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L65) — Local copy of `NewtonLinearization.coeff_aeval_eq_sum_range`: `coeff n (aeval γ P) = ∑_{i ≤ deg P} P
- `theorem ProximityPrize.NewtonLinearization.coeff_aeval_eq_sum_range` [ArkLib/Data/Polynomial/NewtonLinearization.lean:166](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L166) — Local restatement of the `HasSubst`-free `aeval`-coefficient expansion (this is `ProximityPrize.coef

### `coeff_aeval_sub_at` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_aeval_sub_at` [ArkLib/Data/Polynomial/HenselExistence.lean:147](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L147) — Local copy of `NewtonLinearization.coeff_aeval_sub_at` (the `P'(c)`-linear response). For `P : R[X]`
- `theorem ProximityPrize.NewtonLinearization.coeff_aeval_sub_at` [ArkLib/Data/Polynomial/NewtonLinearization.lean:186](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L186) — **Newton/Hensel linearization of the composed series (P2 form).** For a polynomial `P` over `R` and

### `coeff_γ` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_γ` [ArkLib/Data/Polynomial/HenselExistence.lean:227](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L227) — (no docstring)
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_γ` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:303](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L303) — (no docstring)

### `coeff_γ_eq_S` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_γ_eq_S` [ArkLib/Data/Polynomial/HenselExistence.lean:236](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L236) — `γ` agrees with the `t`-th partial sum below order `t + 1`.
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_γ_eq_S` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:312](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L312) — `γ` agrees with the `t`-th partial sum below order `t + 1`.

### `coeffs` (2 declarations, 2 files)

- `def Polynomial.Bivariate.coeffs` [ArkLib/Data/Polynomial/Bivariate.lean:34](../../../ArkLib/Data/Polynomial/Bivariate.lean#L34) — The set of coefficients of a bivariate polynomial.
- `def UniPoly.coeffs` [ArkLib/Data/UniPoly/Basic.lean:41](../../../ArkLib/Data/UniPoly/Basic.lean#L41) — (no docstring)

### `collisionBwdBwd` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.collisionBwdBwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L263) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.collisionBwdBwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:239](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L239) — (no docstring)

### `collisionBwdFwd` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.collisionBwdFwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:281](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L281) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.collisionBwdFwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:257](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L257) — (no docstring)

### `collisionFwdBwd` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.collisionFwdBwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:272](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L272) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.collisionFwdBwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L248) — (no docstring)

### `collisionFwdFwd` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.collisionFwdFwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:254](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L254) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.collisionFwdFwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:230](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L230) — (no docstring)

### `collisionPerm` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.collisionPerm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:290](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L290) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.collisionPerm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:266](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L266) — (no docstring)

### `combined` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.combined` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:225](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L225) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.combined` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:201](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L201) — (no docstring)

### `computeRoundPoly` (2 declarations, 2 files)

- `def Sumcheck.Structured.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured.lean:130](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L130) — The general round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` is the public multilinea
- `def Sumcheck.Structured.Prismalinear.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:70](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L70) — The *prismalinear* round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` has per-variable

### `constantCoeff_eval` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselSeriesCoeff.constantCoeff_eval` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:252](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L252) — `constantCoeff (eval γ Q) = eval (constantCoeff γ) Q₀`: the order-0 part of the evaluated series is
- `theorem ArkLib.PerPlaceSep.constantCoeff_eval` [ArkLib/ToMathlib/PerPlaceSeparabilitySupply.lean:99](../../../ArkLib/ToMathlib/PerPlaceSeparabilitySupply.lean#L99) — The residue map commutes with polynomial evaluation: `π (f.eval a) = (f.map π).eval (π a)`.

### `constantCoeff_γ` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.constantCoeff_γ` [ArkLib/Data/Polynomial/HenselExistence.lean:231](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L231) — The constant coefficient of the Newton root is the prescribed root `c`.
- `theorem ProximityPrize.HenselSeriesCoeff.constantCoeff_γ` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:307](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L307) — The constant coefficient of the Newton root is the prescribed root `c`.

### `constraintMapCurve_eq_mulVec` (2 declarations, 2 files)

- `theorem GuruswamiSudan.OverRatFunc.ZDegree.constraintMapCurve_eq_mulVec` [ArkLib/Data/CodingTheory/GuruswamiSudan/GSCurveInterpolantZDegree.lean:95](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GSCurveInterpolantZDegree.lean#L95) — The matrix `gsMatrixZCurve`, mapped into `K = F(Z)`, represents `constraintMap` for the curve fold o
- `theorem GuruswamiSudan.OverRatFunc.ZDegree.Curve.constraintMapCurve_eq_mulVec` [ArkLib/Data/CodingTheory/GuruswamiSudan/GSInterpolantZDegreeCurve.lean:101](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GSInterpolantZDegreeCurve.lean#L101) — The matrix `gsMatrixZCurve`, mapped into `K = F(Z)`, represents `constraintMap` for the `L`-ary curv

### `coreInteractionOracleRbrKnowledgeError` (2 declarations, 2 files)

- `def coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1158](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1158) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1728](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1728) — (no docstring)

### `coreInteractionOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1129](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1129) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1688](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1688) — Perfect completeness for the core interaction oracle reduction

### `coreInteractionOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1166](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1166) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1737](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1737) — Round-by-round knowledge soundness for the core interaction oracle verifier

### `correlatedAgreement_affine_curves_of_lattice_data` (2 declarations, 2 files)

- `theorem ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_data` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean:885](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean#L885) — [BCIKS20] Theorem 1.5 consuming concrete square-lattice data. This is the data-level counterpart of
- `theorem ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_lattice_data` [ArkLib/ToMathlib/BoundaryDischarge.lean:542](../../../ArkLib/ToMathlib/BoundaryDischarge.lean#L542) — The affine-curves keystone can consume the exact lattice branch through the smaller `BoundaryCardLat

### `correlatedAgreement_affine_curves_of_lattice_data_isSquare` (2 declarations, 2 files)

- `theorem ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_data_isSquare` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean:1002](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean#L1002) — Curve-facing square-endpoint adapter from concrete lattice data. This is the data-level counterpart
- `theorem ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_lattice_data_isSquare` [ArkLib/ToMathlib/BoundaryDischarge.lean:605](../../../ArkLib/ToMathlib/BoundaryDischarge.lean#L605) — Curve-facing square-endpoint adapter from `BoundaryCardLatticeData`.  This is the lattice-data count

### `decidablePred_badPolyAgreement` (2 declarations, 2 files)

- `instance Issue29Ring.decidablePred_badPolyAgreement` [ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean:42](../../../ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean#L42) — (no docstring)
- `instance KStateWeaken.decidablePred_badPolyAgreement` [ArkLib/ToMathlib/KStateWeaken.lean:74](../../../ArkLib/ToMathlib/KStateWeaken.lean#L74) — (no docstring)

### `decodeMessagePhiInv` (3 declarations, 2 files)

- `lemma DuplexSpongeFS.Hyb23Bricks.decodeMessagePhiInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:116](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L116) — `φ_j⁻¹` (brute-force preimage search) succeeds iff a serialize-preimage exists.
- `lemma DuplexSpongeFS.Hyb23Bricks.decodeMessagePhiInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:126](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L126) — A `φ_j⁻¹` witness re-serializes to the input block (the `List.find?` success property).
- `def DuplexSpongeFS.TraceTransform.decodeMessagePhiInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean:115](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean#L115) — Implements the deterministic inverse codec map `φ_i⁻¹ : Im(φ_i) → ℳ_{P,i}`. Because `φ_i` (via `inst

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:52](../../../ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean#L52) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `def GuruswamiSudan.decoder` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:113](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L113) — Specification-level Guruswami-Sudan decoder. This finite-field specification enumerates all degree-`

### `degree` (2 declarations, 2 files)

- `def UniPoly.degree` [ArkLib/Data/UniPoly/Basic.lean:66](../../../ArkLib/Data/UniPoly/Basic.lean#L66) — Return the degree of a `UniPoly`.
- `def StirIOP.degree` [ArkLib/ProofSystem/Stir/MainThm.lean:45](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L45) — **Degree after `i` folds:** The starting degree is `deg`; every fold divides it by `foldingParamⱼ (j

### `dist` (2 declarations, 2 files)

- `def Code.dist` [ArkLib/Data/CodingTheory/Basic/Distance.lean:216](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean#L216) — The Hamming distance of a code `C` is the minimum Hamming distance between any two distinct elements
- `def dist` [ArkLib/Data/CodingTheory/Quarantine/Hypotheses.lean:21](../../../ArkLib/Data/CodingTheory/Quarantine/Hypotheses.lean#L21) — (no docstring)

### `domain_implies_char_ne_2` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:98](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L98) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:134](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L134) — (no docstring)

### `duplexSpongeTraceEntry` (2 declarations, 2 files)

- `abbrev OracleSpec.duplexSpongeTraceEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:371](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L371) — The type of a single entry in a duplex sponge query trace. Implicit-parameter companion to `DSTraceS
- `abbrev DuplexSpongeFS.DSTraceStorage.duplexSpongeTraceEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean:48](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean#L48) — A single query-answer entry of a `DuplexSpongeTrace`, i.e. one element of the underlying `QueryLog`

### `empty` (2 declarations, 2 files)

- `def DuplexSpongeFS.DSTraceStorage.ListBacked.empty` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean:530](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean#L530) — (no docstring)
- `def ProtocolSpec.empty` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:55](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L55) — The empty protocol specification, with no messages or challenges, written as `!p[]`.

### `epsCA_ge_one_sub_inv_of_allButOne` (2 declarations, 2 files)

- `theorem CodingTheory.Bridge.AllButOne.epsCA_ge_one_sub_inv_of_allButOne` [ArkLib/ToMathlib/BGKS20AllButOne.lean:102](../../../ArkLib/ToMathlib/BGKS20AllButOne.lean#L102) — **T5.4 endpoint from the "all but one scalar" producer.** Under the hypotheses of `nearCertainBadLin
- `theorem CodingTheory.Bridge.epsCA_ge_one_sub_inv_of_allButOne` [ArkLib/ToMathlib/NearCertainBadLineProof.lean:103](../../../ArkLib/ToMathlib/NearCertainBadLineProof.lean#L103) — **T5.4 endpoint from an all-but-one near-certain bad line.**

### `epsCA_le_one` (2 declarations, 2 files)

- `theorem ProximityGap.epsCA_le_one` [ArkLib/Data/CodingTheory/ProximityGap/Errors.lean:247](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean#L247) — The CA error is bounded by the total probability mass.
- `theorem CodingTheory.Bridge.epsCA_le_one` [ArkLib/ToMathlib/BridgeListDecodingCA.lean:65](../../../ArkLib/ToMathlib/BridgeListDecodingCA.lean#L65) — **`ε_ca ≤ 1`.** The correlated-agreement error is a supremum of values each of which is either `0` o

### `epsMCA_le_one` (2 declarations, 2 files)

- `theorem ProximityGap.epsMCA_le_one` [ArkLib/Data/CodingTheory/ProximityGap/Errors.lean:316](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean#L316) — The MCA error is bounded by the total probability mass.
- `theorem CodingTheory.Bridge.epsMCA_le_one` [ArkLib/ToMathlib/BridgeListDecodingCA.lean:77](../../../ArkLib/ToMathlib/BridgeListDecodingCA.lean#L77) — **`ε_mca ≤ 1`.** The mutual-correlated-agreement error is a supremum of PMF probabilities, hence at

### `epsRbr` (2 declarations, 2 files)

- `def Core2Keystone.epsRbr` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:72](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L72) — The WHIR per-challenge RBR error (verbatim from `Whir/RbrBudgetAccounting.lean:74`).
- `def Issue113WHIR.epsRbr` [ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:74](../../../ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean#L74) — The WHIR per-challenge RBR error: the maximum over the budget set. Mirror of `whir_rbr_soundness`'s

### `epsRbr_le_of_forall_le` (2 declarations, 2 files)

- `theorem Core2Keystone.epsRbr_le_of_forall_le` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:278](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L278) — **§3.2 — antitone transport to a dominating budget (the keystone budget is tight).** The `epsRbr` bu
- `theorem Issue113WHIR.epsRbr_le_of_forall_le` [ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:158](../../../ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean#L158) — **Tightness / universal property: `ε_rbr` is the SMALLEST uniform per-challenge bound.** If a candid

### `eqPoly_evalC_eq_C_eval` (2 declarations, 2 files)

- `theorem Spartan.Spec.eqPoly_evalC_eq_C_eval` [ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean:41](../../../ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean#L41) — (no docstring)
- `theorem Spartan.eqPoly_evalC_eq_C_eval` [ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean:31](../../../ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean#L31) — Fixing the `eqPolynomial` row variables at `r_x` via `C` commutes with `C` of the base-ring evaluati

### `eval` (2 declarations, 2 files)

- `def UniPoly.eval` [ArkLib/Data/UniPoly/Basic.lean:412](../../../ArkLib/Data/UniPoly/Basic.lean#L412) — Evaluates a `UniPoly` at a given value
- `def Plonk.Gate.eval` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:54](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L54) — Evaluate a gate on a given input vector.

### `evalDist_cast_uniformSample` (2 declarations, 2 files)

- `theorem Prover.evalDist_cast_uniformSample` [ArkLib/OracleReduction/Composition/Sequential/ChallengeSeamBridge.lean:74](../../../ArkLib/OracleReduction/Composition/Sequential/ChallengeSeamBridge.lean#L74) — **Atom 2: uniform sampling is invariant under transport along a type equality.** For `h : A = B` wit
- `theorem OptionTStateT.evalDist_cast_uniformSample` [ArkLib/OracleReduction/RunUnroll.lean:369](../../../ArkLib/OracleReduction/RunUnroll.lean#L369) — **Transport of uniform sampling along a type equality.** If `α = β` (propositionally), the uniform s

### `exists_challenge_flip_of_full` (2 declarations, 2 files)

- `theorem Verifier.KnowledgeStateFunction.exists_challenge_flip_of_full` [ArkLib/OracleReduction/Security/RbrKnowledgeFlip.lean:61](../../../ArkLib/OracleReduction/Security/RbrKnowledgeFlip.lean#L61) — **First-crossing for knowledge state functions, in the rbr-game event shape.** If the input statemen
- `theorem Verifier.StateFunction.exists_challenge_flip_of_full` [ArkLib/OracleReduction/Security/RoundByRound.lean:521](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L521) — **State-function first-crossing on the realized transcript.**  Specialization of `exists_challenge_f

### `exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` (2 declarations, 2 files)

- `lemma ProximityGap.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6727](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6727) — Complement-to-incidence form of the heavy-coordinate argument.  If a coordinate is not heavy for the
- `lemma ArkLib.Claim511.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` [ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean:129](../../../ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean#L129) — **Complement-to-incidence selection.** If at least `r` coordinates are *not* heavy (each bad for `<

### `exists_ne_zero_map_eq_zero` (2 declarations, 2 files)

- `theorem GSMultInterp.exists_ne_zero_map_eq_zero` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:215](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L215) — **Abstract underdetermined-system existence** (mirrors `BCKHS25.exists_ne_zero_map_eq_zero`): a line
- `theorem BCKHS25.exists_ne_zero_map_eq_zero` [ArkLib/Data/CodingTheory/ProximityGap/BCKHS25/Interpolation.lean:71](../../../ArkLib/Data/CodingTheory/ProximityGap/BCKHS25/Interpolation.lean#L71) — Abstract underdetermined-system existence: a linear map between finite-dimensional spaces with stric

### `exists_subset_card_eq_of_le_card` (2 declarations, 2 files)

- `lemma ProximityGap.exists_subset_card_eq_of_le_card` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6677](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6677) — Select exactly `r` elements from a finite set once its cardinality is large enough.  This is the fin
- `lemma ArkLib.Claim511.exists_subset_card_eq_of_le_card` [ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean:119](../../../ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean#L119) — Select exactly `r` elements from a finite set once its cardinality is large enough.  Final selection

### `extractability` (2 declarations, 2 files)

- `def Commitment.extractability` [ArkLib/Commitments/Functional/Basic.lean:238](../../../ArkLib/Commitments/Functional/Basic.lean#L238) — A commitment scheme satisfies **extractability** with error `extractabilityError` if there exists a
- `def CommitmentScheme.extractability` [ArkLib/Commitments/Functional/CommitmentScheme.lean:159](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L159) — A commitment scheme satisfies **extractability** with error `extractabilityError` if there exists a

### `extractor` (2 declarations, 2 files)

- `def CheckClaim.extractor` [ArkLib/ProofSystem/Component/CheckClaim.lean:167](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L167) — The round-by-round extractor for the `CheckClaim` reduction. Trivial since the witness is `Unit`.
- `def ReduceClaim.extractor` [ArkLib/ProofSystem/Component/ReduceClaim.lean:114](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L114) — The round-by-round extractor for the `ReduceClaim` (oracle) reduction. Requires a mapping `mapWitInv

### `failureProbability` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.failureProbability` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:132](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L132) — Paper-facing alias for CO25 Definition 3.7 failure probability.
- `def Verifier.failureProbability` [ArkLib/OracleReduction/Security/Rewinding.lean:163](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L163) — CO25 Definition 3.7, adapted to ArkLib's non-interactive verifier interface. The paper's size bound

### `failureProbabilityFamily` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.failureProbabilityFamily` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:142](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L142) — Paper-facing alias for CO25 Definition 3.7 with explicit security parameter `λ`.
- `def Verifier.failureProbabilityFamily` [ArkLib/OracleReduction/Security/Rewinding.lean:249](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L249) — CO25 Definition 3.7 with the security parameter `λ` made explicit as an external index.

### `fiatShamir_completeness_of_runEq` (2 declarations, 2 files)

- `theorem Reduction.fiatShamir_completeness_of_runEq` [ArkLib/OracleReduction/FiatShamir/Basic.lean:424](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L424) — Basic Fiat-Shamir completeness follows from the named run-equality residual and completeness of the
- `theorem Issue116.fiatShamir_completeness_of_runEq` [ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean:79](../../../ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean#L79) — Forward direction packaged for downstream users: basic FS completeness from the run-equality residua

### `fiatShamir_completeness_unroll_of_runEq` (2 declarations, 2 files)

- `theorem Reduction.fiatShamir_completeness_unroll_of_runEq` [ArkLib/OracleReduction/FiatShamir/Basic.lean:387](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L387) — The named run-equality residual is enough to unroll basic-Fiat-Shamir completeness to the explicit h
- `theorem Issue116.fiatShamir_completeness_unroll_of_runEq` [ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean:65](../../../ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean#L65) — Completeness of the transformed one-message basic Fiat-Shamir reduction is equivalent to the explici

### `finSumFinEquiv_symm_dite` (2 declarations, 2 files)

- `theorem RingSwitching.finSumFinEquiv_symm_dite` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1638](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1638) — Value-form of `finSumFinEquiv.symm`: classify the index by whether its value is `< m`.
- `theorem finSumFinEquiv_symm_dite` [ArkLib/ToMathlib/FinSumMvPolyBricks.lean:25](../../../ArkLib/ToMathlib/FinSumMvPolyBricks.lean#L25) — Value-form classification of `finSumFinEquiv.symm`.

### `finalSumcheckKStateProp` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1359](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1359) — (no docstring)
- `def RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1536](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1536) — (no docstring)

### `finalSumcheckKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:206](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L206) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1309](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1309) — RBR knowledge error for the final sumcheck step

### `finalSumcheckKnowledgeStateFunction` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1399](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1399) — The knowledge state function for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1573](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1573) — The knowledge state function for the final sumcheck step

### `finalSumcheckOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1620](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1620) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1706](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1706) — Round-by-round knowledge soundness for the final sumcheck step

### `finalSumcheckRbrExtractor` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1320](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1320) — The round-by-round extractor for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1516](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1516) — The round-by-round extractor for the final sumcheck step

### `finalSumcheckStepLogic` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1120](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1120) — The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:577](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L577) — The logic instance for the FRI final sumcheck step.

### `finalSumcheckStep_is_logic_complete` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_is_logic_complete` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1719](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1719) — **The final sumcheck step logic is strongly complete** (direct proof; discharges the former `FinalSu
- `lemma Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_is_logic_complete` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1076](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1076) — Strong completeness of the FRI final sumcheck logic step.

### `finalSumcheckStep_verifierCheck_passed` (3 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1274](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1274) — The final sumcheck verifier check follows directly from sumcheck consistency and witness structure.
- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1568](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1568) — The verifier check passes in the final sumcheck step. **Proof structure:** 1. From `sumcheckConsiste
- `lemma Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:991](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L991) — Verifier check passes in the FRI final sumcheck logic step.

### `firstSumcheckWithTarget_toVerifier_isFailingDet` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.firstSumcheckWithTarget_toVerifier_isFailingDet` [ArkLib/ProofSystem/Spartan/ComposedTightRbrKnowledge.lean:317](../../../ArkLib/ProofSystem/Spartan/ComposedTightRbrKnowledge.lean#L317) — **`hV₃` witness for the tight fold: the target-preserving first sum-check verifier is failing-determ
- `theorem Spartan.Spec.firstSumcheckWithTarget_toVerifier_isFailingDet` [ArkLib/ProofSystem/Spartan/TightDeterminismWitnesses.lean:35](../../../ArkLib/ProofSystem/Spartan/TightDeterminismWitnesses.lean#L35) — **`hV₃` witness (tight chain): the carried first sum-check verifier is failing-deterministic.**

### `foldMatrixNat_det_ne_zero` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.foldMatrixNat_det_ne_zero` [ArkLib/ProofSystem/Binius/BinaryBasefold/FoldDetDischarge.lean:124](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/FoldDetDischarge.lean#L124) — **Issue #317: every fold matrix in the `≤ ℓ` range is nonsingular.**
- `theorem Binius.BinaryBasefold.DetNeZero.foldMatrixNat_det_ne_zero` [ArkLib/ProofSystem/Binius/BinaryBasefold/FoldDetSplit.lean:288](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/FoldDetSplit.lean#L288) — **The induction** (issue #317): every `foldMatrixNat` within the `≤ ℓ` range has nonzero determinant

### `foldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.foldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean:184](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean#L184) — (no docstring)
- `theorem WhirIOP.FoldRound.foldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Whir/FoldRound.lean:265](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L265) — **Perfect completeness of the honest WHIR fold round.** The honest prover folds its committed codewo

### `foldProver` (2 declarations, 2 files)

- `def Fri.Spec.FoldPhase.foldProver` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:400](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L400) — The prover for the `i`-th round of the FRI protocol. It first receives the challenge, then does an `
- `def WhirIOP.FoldRound.foldProver` [ArkLib/ProofSystem/Whir/FoldRound.lean:174](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L174) — The honest fold-round prover. It receives `α`, folds its committed function, and sends the folded or

### `foldVerifier` (2 declarations, 2 files)

- `def Fri.Spec.FoldPhase.foldVerifier` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:454](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L454) — The oracle verifier for the `i`-th non-final folding round of the FRI protocol.
- `def WhirIOP.FoldRound.foldVerifier` [ArkLib/ProofSystem/Whir/FoldRound.lean:192](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L192) — The honest fold-round verifier. It performs no consistency check (that is deferred to the query phas

### `fullOracleReduction_perfectCompleteness_wired` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness_wired` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:212](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L212) — **Perfect completeness of the full Binary Basefold protocol, wired.** The core-interaction ⋈ query s
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness_wired` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:566](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L566) — **Perfect completeness of the full FRI-Binius protocol, wired (issue #313).** The `batchingCore ⋈ qu

### `fullPspec` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.fullPspec` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:56](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L56) — (no docstring)
- `def RingSwitching.fullPspec` [ArkLib/ProofSystem/RingSwitching/Spec.lean:57](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L57) — (no docstring)

### `genMutualCorrParamsUDR` (2 declarations, 2 files)

- `def Fold.genMutualCorrParamsUDR` [ArkLib/ProofSystem/Whir/FoldingGenMutualCorrParamsUDR.lean:63](../../../ArkLib/ProofSystem/Whir/FoldingGenMutualCorrParamsUDR.lean#L63) — **The unique-decoding-window instance of `Fold.GenMutualCorrParams`.** Given the per-level power-dom
- `def WhirIOP.genMutualCorrParamsUDR` [ArkLib/ProofSystem/Whir/GenMutualCorrParamsUDR.lean:148](../../../ArkLib/ProofSystem/Whir/GenMutualCorrParamsUDR.lean#L148) — **The unique-decoding-window instance of `GenMutualCorrParams`.** Given the per-round power-domain d

### `getBit_eq_testBit` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.QueryPhase.getBit_eq_testBit` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:392](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L392) — (no docstring)
- `lemma Binius.BinaryBasefold.getBit_eq_testBit` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Lift.lean:41](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Lift.lean#L41) — (no docstring)

### `getSumcheckRoundPoly_eval_eq_sum_snoc` (2 declarations, 2 files)

- `theorem RingSwitching.SumcheckPhase.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:297](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L297) — **Target (b): `getSumcheckRoundPoly` value as a cube sum (LAST-variable/`snoc` form, defect-#20 repa
- `theorem Sumcheck.Structured.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:117](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L117) — **Round-univariate evaluation as a survivor-cube sum (last-variable / `snoc` form).** Evaluating the

### `gsMatrixZCurve` (2 declarations, 2 files)

- `def GuruswamiSudan.OverRatFunc.ZDegree.gsMatrixZCurve` [ArkLib/Data/CodingTheory/GuruswamiSudan/GSCurveInterpolantZDegree.lean:58](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GSCurveInterpolantZDegree.lean#L58) — The `L`-ary curve-fold Guruswami–Sudan constraint system as a matrix over `F[Z]` (the inner `F[X]` i
- `def GuruswamiSudan.OverRatFunc.ZDegree.Curve.gsMatrixZCurve` [ArkLib/Data/CodingTheory/GuruswamiSudan/GSInterpolantZDegreeCurve.lean:68](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GSInterpolantZDegreeCurve.lean#L68) — The `L`-ary curve-fold Guruswami–Sudan constraint system as a matrix over `F[Z]` (the inner `F[X]` i

### `gs_list_size_bound` (2 declarations, 2 files)

- `theorem GSListSizeBound.gs_list_size_bound` [ArkLib/Data/CodingTheory/GuruswamiSudan/ListSizeBound.lean:130](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/ListSizeBound.lean#L130) — **Guruswami–Sudan list-size bound.** Let `Q : F[X][Y]` be a nonzero interpolant of `(1, k-1)`-weight
- `theorem CodingTheory.Bounds.gs_list_size_bound` [ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean:91](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean#L91) — **Guruswami–Sudan list-size bound.** If `Q ≠ 0` has `Y`-degree `≤ deg_Y`, then the set of candidate

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:758](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L758) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:201](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L201) — The first part of Lemma 5.3 from [BCIKS20]. Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`pr

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:797](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L797) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:213](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L213) — The second part of Lemma 5.3 from [BCIKS20]. For any solution `Q` of the Guruswami-Sudan system, and

### `ham_c0_c1` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c0_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:44](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L44) — Pairwise Hamming distances.
- `theorem JohnsonBound.JqlRefutation.ham_c0_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:84](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L84) — Pairwise Hamming distances.

### `ham_c0_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c0_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:45](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L45) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.ham_c0_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:85](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L85) — (no docstring)

### `ham_c1_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c1_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:46](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L46) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.ham_c1_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:86](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L86) — (no docstring)

### `hammingDist_comp_equiv` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.hammingDist_comp_equiv` [ArkLib/ProofSystem/Binius/BinaryBasefold/ExtractMLPCorrectness.lean:69](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ExtractMLPCorrectness.lean#L69) — Hamming distance is invariant under precomposition with an equivalence of the index type.
- `lemma BKR06.hammingDist_comp_equiv` [ArkLib/ToMathlib/BKR06EndToEnd.lean:524](../../../ArkLib/ToMathlib/BKR06EndToEnd.lean#L524) — Index relabeling preserves the Hamming distance.  (Mathlib's `hammingDist_comp` is codomain-side com

### `hasseCoeff` (2 declarations, 2 files)

- `def GSMultInterp.hasseCoeff` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:136](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L136) — The order-`(a, b)` *Hasse coefficient* of the bivariate polynomial `Q = ∑_{(s,t)∈monoIdx} c(s,t)·X^s
- `def ArkLib.GS.hasseCoeff` [ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean:67](../../../ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean#L67) — The bivariate Hasse–Taylor coefficient of bidegree `(i, j)` of `Q` at `(a, b)`: take the `j`-th oute

### `heavyCoords_card_mul_le` (2 declarations, 2 files)

- `lemma ProximityGap.heavyCoords_card_mul_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6685](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6685) — Generic double-counting brick for Claim 5.11. If each `z ∈ S` has at most `m` bad coordinates, then
- `lemma ArkLib.Claim511.heavyCoords_card_mul_le` [ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean:78](../../../ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean#L78) — **Double-counting brick.** If each `z ∈ S` has at most `m` bad coordinates, then the coordinates tha

### `hint` (2 declarations, 2 files)

- `def DomainSeparator.hint` [ArkLib/Data/Hash/DomainSep.lean:230](../../../ArkLib/Data/Hash/DomainSep.lean#L230) — Hint `count` native elements. Rust interface: ```rust pub fn hint(self, label: &str) -> Self ```
- `def HashStateWithInstructions.hint` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:192](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L192) — Process a hint operation. Rust interface: ```rust pub fn hint(&mut self) -> Result<(), DomainSeparat

### `honestTranscriptDist_reduction_evalDist` (2 declarations, 2 files)

- `theorem CheckClaim.honestTranscriptDist_reduction_evalDist` [ArkLib/ProofSystem/Component/CheckClaim.lean:121](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L121) — The honest transcript distribution for a valid `CheckClaim` statement is the deterministic empty tra
- `theorem SendWitness.honestTranscriptDist_reduction_evalDist` [ArkLib/ProofSystem/Component/SendWitness.lean:109](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L109) — The honest transcript distribution for `SendWitness` is the deterministic one-message transcript con

### `hybEncodedMessagesBefore` (6 declarations, 2 files)

- `lemma DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:224](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L224) — `hybEncodedMessagesBefore?` is the walk applied to the flattened prefix.
- `lemma DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:302](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L302) — **H23-2.** `hybEncodedMessagesBefore?` succeeds whenever every encoded block before the round lies i
- `lemma DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:343](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L343) — **H23-2 glue.** On any backtrack output passing the simulator's image guard, the `Hyb₃` codec bridge
- `lemma DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:418](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L418) — **H23-3.** On success of `hybEncodedMessagesBefore?`, every decoded message re-serializes to the cor
- `lemma DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:432](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L432) — **H23-4.** Two encoded prefixes decoding (via `hybEncodedMessagesBefore?`) to the same message prefi
- `def DuplexSpongeFS.TraceTransform.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean:368](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean#L368) — Public wrapper for the Section 5.8 `φ⁻¹` parser from the encoded-message tuple returned by `BackTrac

### `id_isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_isHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:332](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L332) — The zero-round identity oracle reduction is HVZK for any oracle-input relation.
- `theorem Reduction.id_isHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:375](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L375) — The zero-round identity reduction is honest-verifier zero-knowledge for any relation.

### `id_isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_isStatHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:342](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L342) — The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and any e
- `theorem Reduction.id_isStatHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:384](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L384) — The zero-round identity reduction is statistically honest-verifier zero-knowledge for any relation a

### `id_perfectHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_perfectHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:304](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L304) — The zero-round identity oracle reduction is perfect HVZK for any oracle-input relation.
- `theorem Reduction.id_perfectHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:355](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L355) — The zero-round identity reduction satisfies perfect honest-verifier zero-knowledge for any input rel

### `id_statisticalHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_statisticalHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:318](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L318) — The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and any e
- `theorem Reduction.id_statisticalHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:366](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L366) — The zero-round identity reduction satisfies statistical honest-verifier zero-knowledge for any relat

### `idxToSigma_inl` (2 declarations, 2 files)

- `theorem ArkLib.SeqComposeRbrKnowledge.idxToSigma_inl` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:69](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L69) — `seqComposeChallengeIdxToSigma` along the `inl` embedding of a head challenge index lands in the fir
- `theorem ArkLib.SeqComposeRbrSoundness.idxToSigma_inl` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:91](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L91) — `seqComposeChallengeIdxToSigma` along the `inl` embedding of a head challenge index lands in the fir

### `idxToSigma_inr` (2 declarations, 2 files)

- `theorem ArkLib.SeqComposeRbrKnowledge.idxToSigma_inr` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:96](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L96) — `seqComposeChallengeIdxToSigma` along the `inr` embedding of a tail challenge index: the first compo
- `theorem ArkLib.SeqComposeRbrSoundness.idxToSigma_inr` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:118](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L118) — `seqComposeChallengeIdxToSigma` along the `inr` embedding of a tail challenge index: the first compo

### `injOn` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injOn` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:233](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L233) — (no docstring)
- `lemma Domain.FftDomain.injOn` [ArkLib/Data/Domain/FftDomain/Defs.lean:116](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L116) — (no docstring)

### `injective` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injective` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:228](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L228) — (no docstring)
- `lemma Domain.FftDomain.injective` [ArkLib/Data/Domain/FftDomain/Defs.lean:112](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L112) — (no docstring)

### `inputAns` (2 declarations, 2 files)

- `def StirIOP.MultiRound.inputAns` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:180](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L180) — The honest answer of the input-codeword oracle (ascribed at `F`).
- `def Whir302Checked.inputAns` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:132](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L132) — The honest answer of the public input oracle.

### `instChalFintype` (2 declarations, 2 files)

- `instance Whir302.instChalFintype` [ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean:37](../../../ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean#L37) — (no docstring)
- `instance Whir302RBR.instChalFintype` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:396](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L396) — (no docstring)

### `instChalInhabited` (2 declarations, 2 files)

- `instance Whir302.instChalInhabited` [ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean:45](../../../ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean#L45) — (no docstring)
- `instance Whir302RBR.instChalInhabited` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:404](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L404) — (no docstring)

### `interpolate` (2 declarations, 2 files)

- `def ReedSolomon.interpolate` [ArkLib/Data/CodingTheory/ReedSolomon.lean:633](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L633) — The linear map that maps a codeword `f : ι → F` to a degree < \|ι\| polynomial p, such that `p(x) = f(
- `def UniPoly.Lagrange.interpolate` [ArkLib/Data/UniPoly/Basic.lean:1120](../../../ArkLib/Data/UniPoly/Basic.lean#L1120) — This function produces the polynomial which is of degree n and is equal to r i at ω^i for i = 0, 1,

### `isHVZK` (2 declarations, 2 files)

- `def OracleReduction.isHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:62](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L62) — Existential perfect HVZK for an oracle reduction.
- `def Reduction.isHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:90](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L90) — A reduction is honest-verifier zero-knowledge for relation `rel` if some simulator achieves perfect

### `isHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:397](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L397) — **OracleReduction `isHVZK` transfers along an equal honest distribution.**
- `theorem Reduction.isHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:480](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L480) — **`isHVZK` transfers along an `evalDist`-equal honest distribution.**

### `isHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:424](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L424) — **OracleReduction `isHVZK` honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.isHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:506](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L506) — **`isHVZK` honest-distribution congruence with opposite-order equality.**

### `isHVZK.isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.isStatHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:151](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L151) — Perfect HVZK existence for oracle reductions implies statistical HVZK existence.
- `theorem Reduction.isHVZK.isStatHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:198](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L198) — **Perfect HVZK implies statistical HVZK existence** at any error.

### `isHVZK.isStatHVZK_mono_relation_error` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.isStatHVZK_mono_relation_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:275](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L275) — Perfect HVZK existence for oracle reductions transports to statistical HVZK on a restricted relation
- `theorem Reduction.isHVZK.isStatHVZK_mono_relation_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:305](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L305) — **Perfect HVZK existence gives statistical HVZK on any subrelation and relaxed error.**

### `isHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:118](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L118) — `isHVZK` for oracle reductions is antitone in the relation.
- `theorem Reduction.isHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:167](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L167) — **`isHVZK` is antitone in the relation.** HVZK for `rel` implies HVZK for any `rel' ⊆ rel` (the same

### `isHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:523](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L523) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for exact HVZK at
- `theorem Reduction.isHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:597](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L597) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for exact HVZK.**

### `isHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:509](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L509) — **Existential zero-error approximate honest-distribution transfer for exact HVZK at the OracleReduct
- `theorem Reduction.isHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:583](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L583) — **Existential zero-error approximate honest-distribution transfer for exact HVZK.**

### `isHVZK_iff_isStatHVZK_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_iff_isStatHVZK_zero` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:174](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L174) — Perfect HVZK existence for oracle reductions is equivalent to zero-error statistical HVZK existence.
- `theorem Reduction.isHVZK_iff_isStatHVZK_zero` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:218](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L218) — **Perfect HVZK existence is equivalent to zero-error statistical HVZK existence.**

### `isHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:372](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L372) — **OracleReduction `isHVZK` from the symmetric-facing constant-simulator criterion.**
- `theorem Reduction.isHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:455](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L455) — **`isHVZK` from the symmetric-facing constant-simulator criterion.**

### `isHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:347](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L347) — **OracleReduction `isHVZK` from the constant-simulator criterion.**
- `theorem Reduction.isHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:432](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L432) — **`isHVZK` from the constant-simulator criterion.**

### `isStatHVZK` (2 declarations, 2 files)

- `def OracleReduction.isStatHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:71](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L71) — Existential statistical HVZK for an oracle reduction.
- `def Reduction.isStatHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:98](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L98) — A reduction is *statistically* honest-verifier zero-knowledge with error `ε` if some simulator achie

### `isStatHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:410](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L410) — **OracleReduction `isStatHVZK` transfers along an equal honest distribution.**
- `theorem Reduction.isStatHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:493](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L493) — **`isStatHVZK` transfers along an `evalDist`-equal honest distribution.**

### `isStatHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:436](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L436) — **OracleReduction `isStatHVZK` honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.isStatHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:518](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L518) — **`isStatHVZK` honest-distribution congruence with opposite-order equality.**

### `isStatHVZK.mono_error` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:198](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L198) — `isStatHVZK` for oracle reductions is monotone in the error bound.
- `theorem Reduction.isStatHVZK.mono_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:240](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L240) — **`isStatHVZK` is monotone in the error.**

### `isStatHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:187](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L187) — `isStatHVZK` for oracle reductions is antitone in the relation.
- `theorem Reduction.isStatHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:230](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L230) — **`isStatHVZK` is antitone in the relation.**

### `isStatHVZK.mono_relation_error` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_relation_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:261](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L261) — Existential statistical HVZK for oracle reductions transports across both relation restriction and e
- `theorem Reduction.isStatHVZK.mono_relation_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:295](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L295) — **Existential statistical HVZK transports across both relation restriction and error relaxation.** T

### `isStatHVZK.triangle_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:449](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L449) — **Existential approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.isStatHVZK.triangle_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:530](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L530) — **Existential approximate honest-distribution transfer for statistical HVZK.**

### `isStatHVZK.triangle_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:464](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L464) — **Existential symmetric-facing approximate honest-distribution transfer at the OracleReduction API b
- `theorem Reduction.isStatHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:543](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L543) — **Existential symmetric-facing approximate honest-distribution transfer.**

### `isStatHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:494](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L494) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for statistical H
- `theorem Reduction.isStatHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:570](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L570) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for statistical H

### `isStatHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:479](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L479) — **Existential zero-error approximate honest-distribution transfer for statistical HVZK at the Oracle
- `theorem Reduction.isStatHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:556](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L556) — **Existential zero-error approximate honest-distribution transfer for statistical HVZK.**

### `isStatHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:384](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L384) — **OracleReduction `isStatHVZK` from the symmetric-facing constant-simulator criterion.**
- `theorem Reduction.isStatHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:467](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L467) — **`isStatHVZK` from the symmetric-facing constant-simulator criterion.**

### `isStatHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:359](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L359) — **OracleReduction `isStatHVZK` from the constant-simulator criterion.**
- `theorem Reduction.isStatHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:443](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L443) — **`isStatHVZK` from the constant-simulator criterion.**

### `isStatHVZK_zero.isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_zero.isHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:162](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L162) — Zero-error statistical HVZK existence for oracle reductions recovers perfect HVZK existence.
- `theorem Reduction.isStatHVZK_zero.isHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:208](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L208) — **Zero-error statistical HVZK existence is perfect HVZK existence.**

### `isStatHVZK_zero.isHVZK_mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_zero.isHVZK_mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:287](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L287) — Zero-error statistical HVZK existence for oracle reductions transports back to perfect HVZK existenc
- `theorem Reduction.isStatHVZK_zero.isHVZK_mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:315](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L315) — **Zero-error statistical HVZK existence transports back to perfect HVZK existence on a subrelation.*

### `iterated_fold_to_const_strict` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.iterated_fold_to_const_strict` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1325](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1325) — **Strict version**: When folding the last oracle to level `ℓ` (final sumcheck), the iterated fold of
- `lemma Binius.FRIBinius.CoreInteractionPhase.iterated_fold_to_const_strict` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:733](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L733) — Strict helper: folding the last oracle block in the final sumcheck step yields the constant function

### `knowledgeSoundness.mono_error` (2 declarations, 2 files)

- `theorem Verifier.knowledgeSoundness.mono_error` [ArkLib/OracleReduction/Security/Basic.lean:381](../../../ArkLib/OracleReduction/Security/Basic.lean#L381) — Straightline knowledge soundness is monotone in the allowed knowledge error.
- `theorem Verifier.StateRestoration.knowledgeSoundness.mono_error` [ArkLib/OracleReduction/Security/StateRestoration.lean:218](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L218) — State-restoration knowledge soundness is monotone in the allowed knowledge-soundness error.

### `knowledgeSoundness.mono_relations` (2 declarations, 2 files)

- `theorem Verifier.knowledgeSoundness.mono_relations` [ArkLib/OracleReduction/Security/Basic.lean:397](../../../ArkLib/OracleReduction/Security/Basic.lean#L397) — Straightline knowledge soundness is monotone in the input and output relations. If knowledge soundne
- `theorem Verifier.StateRestoration.knowledgeSoundness.mono_relations` [ArkLib/OracleReduction/Security/StateRestoration.lean:232](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L232) — State-restoration knowledge soundness is monotone under enlarging the valid input relation and shrin

### `lambda_le_ggr11_of_Lambda_top` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_Lambda_top` [ArkLib/ToMathlib/GGR11Interleaved.lean:404](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L404) — Generic end-to-end infinite-list regime: if the base list size is infinite and the Red budget is pos
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_Lambda_top` [ArkLib/ToMathlib/GGR11Reconnect.lean:134](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L134) — **Infinite-list regime, reconnected.** When the base list size is infinite and the GGR11 Red budget

### `lambda_le_ggr11_of_le_exp` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_le_exp` [ArkLib/ToMathlib/GGR11Interleaved.lean:394](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L394) — Generic end-to-end elementary regime: if the Red budget already dominates the interleaving factor, t
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_le_exp` [ArkLib/ToMathlib/GGR11Reconnect.lean:122](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L122) — **Elementary regime, reconnected.** When the GGR11 Red budget already dominates the interleaving fac

### `lambda_le_ggr11_of_perWordBound` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_perWordBound` [ArkLib/ToMathlib/GGR11Interleaved.lean:118](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L118) — **Reduction of the GGR11 interleaved list-size bound to its per-word form.** Given the per-received-
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_perWordBound` [ArkLib/ToMathlib/GGR11Reconnect.lean:110](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L110) — **Reconnect (per-word form).** The bare bound follows from the (coarser) per-received-word residual

### `lambda_le_ggr11_of_treeFrontier` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_treeFrontier` [ArkLib/ToMathlib/GGR11Interleaved.lean:291](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L291) — End-to-end GGR11 list-size bound from the granular named frontier.
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_treeFrontier` [ArkLib/ToMathlib/GGR11Reconnect.lean:100](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L100) — **Reconnect (named frontier form).** The bare bound follows from the granular per-received-word `GGR

### `lambda_le_ggr11_of_treeStructure` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_treeStructure` [ArkLib/ToMathlib/GGR11Interleaved.lean:283](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L283) — **End-to-end:** the GGR11 interleaved list-size bound from the refined tree-existence residual.
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_treeStructure` [ArkLib/ToMathlib/GGR11Reconnect.lean:90](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L90) — **Reconnect (tree-existence form).** The bare `InterleavedCode.lambda_le_ggr11` bound follows from t

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib/Data/Fin/Tuple/Defs.lean:96](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L96) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib/Data/Matrix/Basic.lean:25](../../../ArkLib/Data/Matrix/Basic.lean#L25) — (no docstring)

### `lemma_5_10` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.BadEventDS.lemma_5_10` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:379](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L379) — CO25 Lemma 5.10, current trace-event form. If the combined bad event `E(tr)` does not occur, then th
- `theorem OracleSpec.QueryLog.BadEventDSPaper.lemma_5_10` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:355](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L355) — CO25 Lemma 5.10, current trace-event form. If the combined bad event `E(tr)` does not occur, then th

### `length_mainFoldedOracleMessageIdx` (2 declarations, 2 files)

- `lemma Whir302Checked.length_mainFoldedOracleMessageIdx` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:76](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L76) — Payload length of the folded-oracle message slot `i` is the cardinality of the next paper evaluation
- `lemma Whir302RBR.length_mainFoldedOracleMessageIdx` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:192](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L192) — Payload length of the folded-oracle message slot `i` is the cardinality of the next evaluation domai

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:242](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L242) — STATEMENT REPAIR (2026-06-04): completeness lifting now additionally takes the verifier's oracle-rou
- `theorem Reduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:777](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L777) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:291](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L291) — (no docstring)
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1058](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1058) — (no docstring)

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:252](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L252) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:882](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L882) — (no docstring)

### `liftContext_rbr_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:337](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L337) — Lifting the oracle verifier preserves round-by-round knowledge soundness, assuming the lens satisfie
- `theorem Verifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1804](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1804) — (no docstring)

### `liftContext_rbr_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:311](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L311) — (no docstring)
- `theorem Verifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1555](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1555) — (no docstring)

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:276](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L276) — Lifting the oracle verifier preserves soundness, assuming the lens satisfies its soundness condition
- `theorem Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:911](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L911) — Lifting a verifier context preserves soundness, assuming the lens satisfies its soundness conditions

### `liftM_optionT_run_eq_seam_right` (2 declarations, 2 files)

- `theorem Reduction.liftM_optionT_run_eq_seam_right` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean:75](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean#L75) — **`(liftM g).run = liftM g.run` across the `pSpec₂` challenge seam.** The `pSpec₂` analogue of `lift
- `theorem Verifier.liftM_optionT_run_eq_seam_right` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean:194](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean#L194) — (no docstring)

### `lift_oc_optionT_coh_right` (2 declarations, 2 files)

- `theorem Reduction.lift_oc_optionT_coh_right` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean:110](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean#L110) — **`OptionT`-lift coherence for a phase computation across the `pSpec₂` seam.** The `pSpec₂` analogue
- `theorem Verifier.lift_oc_optionT_coh_right` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean:177](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean#L177) — (no docstring)

### `lookupEncodedMessageAlphaHat` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Hyb23Bricks.lookupEncodedMessageAlphaHat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:96](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L96) — **H23-1.** Looking up the encoded block for message index `j` in the flattened `EncodedMessagesBefor
- `def DuplexSpongeFS.TraceTransform.lookupEncodedMessageAlphaHat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean:123](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean#L123) — Looks up the encoded message block `α̂_j` from the flat list of extracted sponge queries.

### `map` (2 declarations, 2 files)

- `def AGM.GroupRepresentation.map` [ArkLib/AGM/Basic.lean:109](../../../ArkLib/AGM/Basic.lean#L109) — **Functoriality of representations under group homomorphisms.** A group hom `f : G →* H` transports
- `def Fin.map` [ArkLib/Data/Fin/Sigma.lean:499](../../../ArkLib/Data/Fin/Sigma.lean#L499) — (no docstring)

### `mapEquiv` (2 declarations, 2 files)

- `def Probability.SizeSubset.mapEquiv` [ArkLib/Data/Probability/Combinatorial.lean:92](../../../ArkLib/Data/Probability/Combinatorial.lean#L92) — Transport a size-`n` subset across an equivalence of ambient types.
- `def Probability.SizedSubset.mapEquiv` [ArkLib/Data/Probability/UniformSubset.lean:54](../../../ArkLib/Data/Probability/UniformSubset.lean#L54) — Map an `n`-element subset across an equivalence of ambient finite types.

### `masterKStateCore` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.masterKStateCore` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1706](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1706) — Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event of the `i-th` oracle if
- `def RingSwitching.masterKStateCore` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:499](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L499) — (no docstring)

### `masterKStateProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.masterKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1720](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1720) — (no docstring)
- `def RingSwitching.masterKStateProp` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:507](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L507) — (no docstring)

### `mem_C_iff` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.mem_C_iff` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:49](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L49) — Membership in `C` is membership in the explicit three-element set.
- `theorem JohnsonBound.JqlRefutation.mem_C_iff` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:89](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L89) — Membership in `C` is membership in the explicit three-element set.

### `mem_support_oracleVerifier_run_oStmt` (2 declarations, 2 files)

- `theorem Sumcheck.Spec.mem_support_oracleVerifier_run_oStmt` [ArkLib/ProofSystem/Spartan/SumcheckPhaseRbr.lean:231](../../../ArkLib/ProofSystem/Spartan/SumcheckPhaseRbr.lean#L231) — **Reachable outputs of the (plain-verifier view of the) sum-check oracle verifier carry the unchange
- `theorem Sumcheck.Spec.SingleRound.mem_support_oracleVerifier_run_oStmt` [ArkLib/ProofSystem/Sumcheck/Spec/PinnedCompleteness.lean:167](../../../ArkLib/ProofSystem/Sumcheck/Spec/PinnedCompleteness.lean#L167) — **Per-round oracle pass-through.** Any statement in the support of the (plain-verifier view of the)

### `mem_support_simulateQ_id'_liftM_query` (2 declarations, 2 files)

- `lemma OptionT.mem_support_simulateQ_id'_liftM_query` [ArkLib/ToVCVio/Lemmas.lean:430](../../../ArkLib/ToVCVio/Lemmas.lean#L430) — **Generic**: any element of the range of a query is in the support of `simulateQ (fun t => liftM (qu
- `lemma mem_support_simulateQ_id'_liftM_query` [ArkLib/ToVCVio/Simulation.lean:217](../../../ArkLib/ToVCVio/Simulation.lean#L217) — (no docstring)

### `minDist_C` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.minDist_C` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:54](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L54) — Every distinct pair of codewords has Hamming distance `≥ 1`, and the pair `(c0, c1)` attains `1`. He
- `theorem JohnsonBound.JqlRefutation.minDist_C` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:97](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L97) — **`Code.minDist C = 1`.**  The defining set of distinct-pair distances is `{1, 2}` (`d(c0,c1) = d(c0

### `mk_eq_trunc_of_tail_zero` (2 declarations, 2 files)

- `theorem ArkLib.BetaToCurveCoeffPolys.mk_eq_trunc_of_tail_zero` [ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean:86](../../../ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean#L86) — A power series whose coefficients vanish from index `k` on **is** (the coercion of) its `k`-truncati
- `theorem PowerSeries.mk_eq_trunc_of_tail_zero` [ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean:77](../../../ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean#L77) — A power series whose coefficients vanish from index `k` on equals the coercion of its `k`-truncation

### `msgAns` (2 declarations, 2 files)

- `def StirIOP.MultiRound.msgAns` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:184](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L184) — The honest answer of a message oracle (ascribed at `F`).
- `def Whir302Checked.msgAns` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:125](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L125) — The honest answer of a message oracle (ascribed at `F`).

### `multilinearWeight` (2 declarations, 2 files)

- `def multilinearWeight` [ArkLib/Data/CodingTheory/Prelims.lean:23](../../../ArkLib/Data/CodingTheory/Prelims.lean#L23) — The tensor product weight `⊗_{i=0}^{ϑ-1}(1 - rᵢ, rᵢ)` for a specific index `i` given randomness `r`.
- `def Issue33Binius.multilinearWeight` [ArkLib/ProofSystem/Binius/BinaryBasefold/MultilinearWeightRecursion.lean:24](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/MultilinearWeightRecursion.lean#L24) — Tensor product weight `⊗_{j<ϑ}(1 - r_j, r_j)` at index `i` given challenges `r`. This is a verbatim

### `natDegree_lt_of_mem_degreeLT` (2 declarations, 2 files)

- `lemma ReedSolomon.natDegree_lt_of_mem_degreeLT` [ArkLib/Data/CodingTheory/ReedSolomon.lean:118](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L118) — (no docstring)
- `lemma Fri.Spec.Completeness.natDegree_lt_of_mem_degreeLT` [ArkLib/ToMathlib/FriCompleteFinalRound.lean:43](../../../ArkLib/ToMathlib/FriCompleteFinalRound.lean#L43) — A `CPolynomial` in `degreeLT D` (for positive `D`) has `natDegree < D`. Bridges the FRI final-round

### `natDegree_taylor_lt` (2 declarations, 2 files)

- `theorem ArkLib.BetaToCurveCoeffPolys.natDegree_taylor_lt` [ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean:141](../../../ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean#L141) — Taylor shift preserves the strict degree bound of a coefficient profile.
- `theorem Polynomial.natDegree_taylor_lt` [ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean:67](../../../ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean#L67) — A strict degree bound transports through a Taylor shift.

### `nearCertainBadLine_of_allButOne` (2 declarations, 2 files)

- `theorem CodingTheory.Bridge.AllButOne.nearCertainBadLine_of_allButOne` [ArkLib/ToMathlib/BGKS20AllButOne.lean:86](../../../ArkLib/ToMathlib/BGKS20AllButOne.lean#L86) — **"All but one scalar" producer (BGKS20 line-witness shape).** Given a stack `u` that is **not** joi
- `theorem CodingTheory.Bridge.nearCertainBadLine_of_allButOne` [ArkLib/ToMathlib/NearCertainBadLineProof.lean:84](../../../ArkLib/ToMathlib/NearCertainBadLineProof.lean#L84) — **All-but-one producer for `NearCertainBadLine`.** If a stack is not jointly close and every scalar

### `notFunction` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.notFunction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:215](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L215) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.notFunction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:191](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L191) — (no docstring)

### `not_collisionPerm_of_not_combined` (2 declarations, 2 files)

- `lemma OracleSpec.QueryLog.BadEventDS.not_collisionPerm_of_not_combined` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:295](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L295) — (no docstring)
- `lemma OracleSpec.QueryLog.BadEventDSPaper.not_collisionPerm_of_not_combined` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:271](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L271) — (no docstring)

### `ofFinCoeff` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.Rq.ofFinCoeff` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:253](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L253) — The reduced representative with prescribed finite coefficients `Σ_{k<N} cₖ Xᵏ`, valid when `N` does
- `def CompPoly.CPolynomial.ofFinCoeff` [ArkLib/ToCompPoly/Univariate/Basic.lean:300](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L300) — The polynomial with prescribed finite coefficient function: `Σ_{k<N} cₖ Xᵏ`.

### `one_le_Lambda_of_nonempty` (2 declarations, 2 files)

- `theorem CodingTheory.one_le_Lambda_of_nonempty` [ArkLib/Data/CodingTheory/ListSizeVolumeBound.lean:184](../../../ArkLib/Data/CodingTheory/ListSizeVolumeBound.lean#L184) — **List-size lower bound `1 ≤ \|Λ(C,δ)\|` for a nonempty code and `δ ≥ 0`.** Any codeword is `0`-close
- `lemma InterleavedCode.GGR11.one_le_Lambda_of_nonempty` [ArkLib/ToMathlib/GGR11TreeConstruction.lean:1247](../../../ArkLib/ToMathlib/GGR11TreeConstruction.lean#L1247) — With a nonempty code, a nonnegative radius, and finite lists, the maximised list size is at least on

### `oracleProver_run` (2 declarations, 2 files)

- `theorem SendSingleWitness.oracleProver_run` [ArkLib/ProofSystem/Component/SendWitness.lean:396](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L396) — (no docstring)
- `lemma CheckClaim.oracleProver_run` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:61](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L61) — The oracle `CheckClaim` prover is a deterministic pass-through: empty transcript, unchanged statemen

### `oracleVerifier_rbrSoundness` (2 declarations, 2 files)

- `theorem Sumcheck.Spec.oracleVerifier_rbrSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/OracleRbrSoundness.lean:107](../../../ArkLib/ProofSystem/Sumcheck/Spec/OracleRbrSoundness.lean#L107) — **Oracle-level multi-round round-by-round (plain) soundness of the generic sum-check oracle verifier
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRoundFlipImpClose.lean:46](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRoundFlipImpClose.lean#L46) — **Per-round plain RBR soundness, discharged for the single-round sum-check oracle verifier.** This c

### `pSpecCoreInteraction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:248](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L248) — (no docstring)
- `def RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/RingSwitching/Spec.lean:50](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L50) — (no docstring)

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:201](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L201) — (no docstring)
- `def Fri.Spec.pSpecFold` [ArkLib/ProofSystem/Fri/Spec/General.lean:66](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L66) — (no docstring)

### `pSpecSumcheckRound` (2 declarations, 2 files)

- `abbrev RingSwitching.pSpecSumcheckRound` [ArkLib/ProofSystem/RingSwitching/Spec.lean:41](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L41) — (no docstring)
- `def Sumcheck.Structured.pSpecSumcheckRound` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:256](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L256) — Protocol spec for one round of the structured sumcheck: P sends a degree-≤`d` univariate `h_i(X) ∈ L

### `pSpec_dir_zero` (2 declarations, 2 files)

- `theorem StirIOP.Round.pSpec_dir_zero` [ArkLib/ProofSystem/Stir/RoundProtocol.lean:65](../../../ArkLib/ProofSystem/Stir/RoundProtocol.lean#L65) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.pSpec_dir_zero` [ArkLib/ProofSystem/Sumcheck/Spec/Completeness.lean:70](../../../ArkLib/ProofSystem/Sumcheck/Spec/Completeness.lean#L70) — The sum-check round protocol leads with the prover's univariate-polynomial message.

### `pad` (2 declarations, 2 files)

- `def R1CS.pad` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:73](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L73) — Pad an R1CS instance (on the right) from `sz₁` to `sz₂` with zeros. Note that this results in trunca
- `theorem ArkLib.SectionNewtonCleared.Cleared.pad` [ArkLib/ToMathlib/SectionNewtonCleared.lean:83](../../../ArkLib/ToMathlib/SectionNewtonCleared.lean#L83) — (no docstring)

### `paperTranscriptVectorIOP_pureTrue_perfectCompleteness` (2 declarations, 2 files)

- `theorem Whir302.paperTranscriptVectorIOP_pureTrue_perfectCompleteness` [ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean:72](../../../ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean#L72) — (no docstring)
- `theorem Whir302RBR.paperTranscriptVectorIOP_pureTrue_perfectCompleteness` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:419](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L419) — (no docstring)

### `perfectCorrectness` (2 declarations, 2 files)

- `def Commitment.perfectCorrectness` [ArkLib/Commitments/Functional/Basic.lean:109](../../../ArkLib/Commitments/Functional/Basic.lean#L109) — A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
- `def CommitmentScheme.perfectCorrectness` [ArkLib/Commitments/Functional/CommitmentScheme.lean:74](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L74) — A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.

### `perfectHVZK` (2 declarations, 2 files)

- `def OracleReduction.perfectHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:44](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L44) — Perfect HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`.
- `def Reduction.perfectHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:69](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L69) — A reduction satisfies perfect honest-verifier zero-knowledge with respect to a simulator and relatio

### `perfectHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:33](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L33) — **OracleReduction perfect HVZK transfers along an equal honest distribution.**
- `theorem Reduction.perfectHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:64](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L64) — **Perfect HVZK transfers along an `evalDist`-equal honest distribution.** If two reductions have the

### `perfectHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:59](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L59) — **OracleReduction perfect HVZK honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.perfectHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:96](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L96) — **Perfect HVZK honest-distribution congruence with opposite-order equality.**

### `perfectHVZK.isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:130](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L130) — **A concrete OracleReduction perfect-HVZK simulator witnesses existential HVZK.**
- `theorem Reduction.perfectHVZK.isHVZK` [ArkLib/ToMathlib/ZKTransferBricks.lean:174](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L174) — **A concrete perfect-HVZK simulator witnesses existential HVZK.**

### `perfectHVZK.isHVZK_of_simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK_of_simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:152](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L152) — **Package an OracleReduction perfect-HVZK proof after normalizing the simulator distribution.**
- `theorem Reduction.perfectHVZK.isHVZK_of_simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:194](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L194) — **Package a perfect-HVZK proof after normalizing the simulator distribution.**

### `perfectHVZK.isHVZK_of_simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:176](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L176) — **Package an OracleReduction perfect-HVZK proof after simulator normalization in the opposite direct
- `theorem Reduction.perfectHVZK.isHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:216](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L216) — **Package a perfect-HVZK proof after simulator normalization in the opposite direction.**

### `perfectHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:107](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L107) — Perfect HVZK for oracle reductions is antitone in the relation.
- `theorem Reduction.perfectHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:156](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L156) — **Perfect HVZK is antitone in the relation.** A simulator that matches the honest transcript distrib

### `perfectHVZK.simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:86](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L86) — **OracleReduction perfect HVZK is preserved under an equal simulator distribution.**
- `theorem Reduction.perfectHVZK.simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:123](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L123) — **Perfect HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a simulator that prod

### `perfectHVZK.simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:108](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L108) — **OracleReduction perfect HVZK simulator congruence with opposite-order equality.**
- `theorem Reduction.perfectHVZK.simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:152](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L152) — **Perfect HVZK simulator congruence with opposite-order equality.**

### `perfectHVZK.statisticalHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.statisticalHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:96](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L96) — Perfect HVZK for oracle reductions implies statistical HVZK with any error bound.
- `theorem Reduction.perfectHVZK.statisticalHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:137](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L137) — Perfect HVZK implies statistical HVZK with any error `ε`.

### `perfectHVZK.statisticalHVZK_mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.statisticalHVZK_mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:224](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L224) — Perfect HVZK for oracle reductions transports to statistical HVZK on a subrelation at any error. The
- `theorem Reduction.perfectHVZK.statisticalHVZK_mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:262](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L262) — **Perfect HVZK transports to statistical HVZK on a subrelation at any error.** The same simulator is

### `perfectHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:283](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L283) — Symmetric-facing zero-error approximate honest-distribution transfer for perfect HVZK at the OracleR
- `theorem Reduction.perfectHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:362](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L362) — Symmetric-facing zero-error approximate honest-distribution transfer for perfect HVZK.

### `perfectHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:269](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L269) — **Zero-error approximate honest-distribution transfer for perfect HVZK at the OracleReduction API bo
- `theorem Reduction.perfectHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:342](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L342) — **Zero-error approximate honest-distribution transfer for perfect HVZK.** If the honest-transcript b

### `perfectHVZK_iff_statisticalHVZK_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_iff_statisticalHVZK_zero` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:85](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L85) — Perfect HVZK for oracle reductions is exactly statistical HVZK with error `0`.
- `theorem Reduction.perfectHVZK_iff_statisticalHVZK_zero` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:109](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L109) — Perfect HVZK is exactly statistical HVZK with error `0`.

### `perfectHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:321](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L321) — **Symmetric-facing OracleReduction constant-simulator criterion for perfect HVZK.**
- `theorem Reduction.perfectHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:406](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L406) — **Symmetric-facing constant-simulator criterion for perfect HVZK.**

### `perfectHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:296](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L296) — **OracleReduction constant-simulator criterion for perfect HVZK.**
- `theorem Reduction.perfectHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:380](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L380) — **Constant-simulator criterion for perfect HVZK.** If the honest transcript distribution is `evalDis

### `perfectlyCorrect` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.perfectlyCorrect` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Correctness.lean:197](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Correctness.lean#L197) — **Unconditional perfect correctness with the concrete binary decomposition.** Both message and inner
- `theorem ArkLib.Lattices.Ajtai.Simple.perfectlyCorrect` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Correctness.lean:33](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Correctness.lean#L33) — Simple Ajtai commitments are correct on short messages: an honest commitment to a message accepted b

### `phi` (2 declarations, 2 files)

- `def CodingTheory.Bounds.phi` [ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean:48](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean#L48) — Explicit `F`-algebra retraction of `psi`, sending `Y ↦ X₁` and coefficients `g(X) ↦ g(X₀)`.
- `def Logup.phi` [ArkLib/ProofSystem/Logup/Common.lean:685](../../../ArkLib/ProofSystem/Logup/Common.lean#L685) — The denominator term `φᵢ(u)` from Protocol 2.

### `probEvent_bind_eq_one` (2 declarations, 2 files)

- `lemma OracleComp.probEvent_bind_eq_one` [ArkLib/OracleReduction/ProbOneBindCompose.lean:40](../../../ArkLib/OracleReduction/ProbOneBindCompose.lean#L40) — **Probability-one bind composition.** If `mx` satisfies `p` with probability `1`, and `f a` satisfie
- `theorem probEvent_bind_eq_one` [ArkLib/ToMathlib/ProbEventBindOne.lean:29](../../../ArkLib/ToMathlib/ProbEventBindOne.lean#L29) — **Two-stage perfect composition.** If `mx` produces an output satisfying `P` with probability 1, and

### `probEvent_optionT_mk_eq_elim` (2 declarations, 2 files)

- `lemma probEvent_optionT_mk_eq_elim` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessProof.lean:71](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessProof.lean#L71) — **`OptionT.mk` event = `Option.elim`-bad event on the underlying computation.** Bridges the soundnes
- `theorem Verifier.StateFunction.probEvent_optionT_mk_eq_elim` [ArkLib/OracleReduction/Security/RoundByRound.lean:292](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L292) — **`OptionT` probEvent as a success-conjunction on the underlying computation.**  An `OptionT ProbCom

### `probEvent_uniformSample_eq_Pr_uniform` (2 declarations, 2 files)

- `theorem RingSwitching.BatchingPhase.probEvent_uniformSample_eq_Pr_uniform` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:57](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L57) — Bridge the framework's `SampleableType` uniform sampler to the PMF uniform notation used by Schwartz
- `theorem RingSwitching.SumcheckPhase.probEvent_uniformSample_eq_Pr_uniform` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:63](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L63) — Bridge the framework's `SampleableType` uniform sampler to the PMF uniform notation used by some sta

### `prop_4_23_singleRepetition_proximityCheck_bound` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.QueryPhase.prop_4_23_singleRepetition_proximityCheck_bound` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:2719](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L2719) — **Single Repetition Proximity Check Bound (Proposition 4.24)** For a single repetition of the proxim
- `theorem Binius.BinaryBasefold.prop_4_23_singleRepetition_proximityCheck_bound` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhaseSoundness.lean:1272](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhaseSoundness.lean#L1272) — **Proposition 4.24** (Query-phase soundness, assuming no bad events). If any oracle is non-compliant

### `proximityCondition` (2 declarations, 2 files)

- `def MutualCorrAgreement.proximityCondition` [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:56](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean#L56) — For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽` and linea
- `def Generator.proximityCondition` [ArkLib/ProofSystem/Whir/ProximityGen.lean:38](../../../ArkLib/ProofSystem/Whir/ProximityGen.lean#L38) — For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽ˡ` and linear

### `psi` (2 declarations, 2 files)

- `def CodingTheory.Bounds.psi` [ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean:32](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean#L32) — The `F`-algebra map `F[X₀, X₁] → (F[X])[Y]` sending `X₀ ↦ C X` and `X₁ ↦ Y`.
- `def ArkLib.Lattices.CyclotomicModulus.psi` [ArkLib/Data/Lattices/CyclotomicRing/Subfield/Packing.lean:126](../../../ArkLib/Data/Lattices/CyclotomicRing/Subfield/Packing.lean#L126) — The **packing map** `ψ : (R_q^H)^{d/k} → R_q` of Hachi [NOZ26, §3, Eq. 8], as the single sum `Σ_{j}

### `psi_injective` (2 declarations, 2 files)

- `theorem CodingTheory.Bounds.psi_injective` [ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean:51](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean#L51) — (no docstring)
- `theorem ArkLib.Lattices.CyclotomicModulus.psi_injective` [ArkLib/Data/Lattices/CyclotomicRing/Subfield/TraceInnerProduct.lean:269](../../../ArkLib/Data/Lattices/CyclotomicRing/Subfield/TraceInnerProduct.lean#L269) — **`ψ` is injective** (Hachi [NOZ26, §3, Theorem 2]). The trace form `(a,b) ↦ ⟨a,b⟩` is non-degenerat

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean:91](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean#L91) — Oracle query helper: query a committed codeword at a given domain point. Restricted to codeword indi
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:1040](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L1040) — (no docstring)

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:247](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L247) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:1158](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L1158) — (no docstring)

### `rbrBudgetSet` (2 declarations, 2 files)

- `def Core2Keystone.rbrBudgetSet` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:57](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L57) — The WHIR per-challenge RBR budget set (verbatim shape from `Whir/RbrBudgetAccounting.lean`). Reprodu
- `def Issue113WHIR.rbrBudgetSet` [ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:55](../../../ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean#L55) — The WHIR RBR budget set: the union of the four per-round budget families, as a `Finset ℝ≥0`. This is

### `rbrBudgetSet_nonempty` (2 declarations, 2 files)

- `theorem Core2Keystone.rbrBudgetSet_nonempty` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:63](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L63) — (no docstring)
- `theorem Issue113WHIR.rbrBudgetSet_nonempty` [ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:62](../../../ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean#L62) — The budget set is nonempty (it contains `ε_fin`). This is the side condition the in-tree `max' (by s

### `reduction_isHVZK` (2 declarations, 2 files)

- `theorem CheckClaim.reduction_isHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:156](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L156) — `CheckClaim` has an explicit perfect-HVZK simulator.
- `theorem DoNothing.reduction_isHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:79](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L79) — The `DoNothing` reduction has an explicit perfect-HVZK simulator for any relation.

### `reduction_isStatHVZK` (2 declarations, 2 files)

- `theorem CheckClaim.reduction_isStatHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:161](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L161) — `CheckClaim` has statistical HVZK at every error budget.
- `theorem DoNothing.reduction_isStatHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:85](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L85) — The `DoNothing` reduction has statistical HVZK for any relation and error budget.

### `reduction_perfectHVZK` (2 declarations, 2 files)

- `theorem CheckClaim.reduction_perfectHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:142](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L142) — `CheckClaim` is perfectly HVZK for the predicate relation. The simulator is the identity transcript
- `theorem DoNothing.reduction_perfectHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:64](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L64) — The `DoNothing` reduction is perfectly HVZK for any relation.

### `reduction_statisticalHVZK` (2 declarations, 2 files)

- `theorem CheckClaim.reduction_statisticalHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:150](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L150) — Perfect HVZK implies statistical HVZK at every error budget.
- `theorem DoNothing.reduction_statisticalHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:71](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L71) — The `DoNothing` reduction is statistically HVZK for any relation and error budget.

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:193](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L193) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1401](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1401) — (no docstring)

### `redundantEntryDSPaper` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.redundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:45](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L45) — **Paper-faithful redundant entry (CO25 Def. 5.5).** An entry is redundant if a prior entry answers i
- `def DuplexSpongeFS.Paper.redundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:50](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L50) — Paper-faithful CO25 Definition 5.5: an entry is redundant iff a prior entry answers the same query —

### `relIn` (2 declarations, 2 files)

- `def CheckClaim.relIn` [ArkLib/ProofSystem/Component/CheckClaim.lean:61](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L61) — (no docstring)
- `def RandomQuery.relIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:44](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L44) — The input relation is that the two oracles are equal.

### `removeRedundantEntryDSPaper` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:62](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L62) — Remove paper-redundant entries by repeated erasure (classical choice of a redundant index), mirrorin
- `def DuplexSpongeFS.Paper.removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:72](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L72) — Paper-faithful dedup procedure: repeatedly erase a paper-redundant entry until none remain (verbatim

### `removeRedundantEntryDSPaper_eq_self` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.removeRedundantEntryDSPaper_eq_self` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:94](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L94) — Subtype fixpoint form for the canonical output.
- `theorem DuplexSpongeFS.Paper.removeRedundantEntryDSPaper_eq_self` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:105](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L105) — Subtype fixpoint form for the canonical output of `removeRedundantEntryDSPaper`.

### `removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:80](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L80) — `removeRedundantEntryDSPaper` is a fixpoint on already-deduplicated traces.
- `theorem DuplexSpongeFS.Paper.removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:91](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L91) — `removeRedundantEntryDSPaper` is a fixpoint on traces already satisfying `NoRedundantEntryDSPaper`.

### `removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:88](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L88) — First-projection form of the fixpoint lemma.
- `theorem DuplexSpongeFS.Paper.removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L99) — First-projection form of the fixpoint lemma.

### `rewindingKnowledgeSoundness` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.rewindingKnowledgeSoundness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:159](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L159) — Paper-facing alias for CO25 Definition 3.8 rewinding knowledge soundness.
- `def Verifier.rewindingKnowledgeSoundness` [ArkLib/OracleReduction/Security/Rewinding.lean:211](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L211) — CO25 Definition 3.8, adapted to ArkLib's non-interactive argument interface. ArkLib's `Prover.NARG`

### `rewindingKnowledgeSoundnessFamily` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.rewindingKnowledgeSoundnessFamily` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:176](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L176) — Paper-facing alias for CO25 Definition 3.8 with explicit security parameter `λ`.
- `def Verifier.rewindingKnowledgeSoundnessFamily` [ArkLib/OracleReduction/Security/Rewinding.lean:264](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L264) — CO25 Definition 3.8 with the security parameter `λ` made explicit as an external index. This is a wr

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib/Data/Fin/Tuple/Defs.lean:90](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L90) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib/Data/Matrix/Basic.lean:21](../../../ArkLib/Data/Matrix/Basic.lean#L21) — (no docstring)

### `roundKnowledgeError` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckPhase.roundKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:252](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L252) — Repaired local bound for the current round-by-round proof. The degree-two bad-event lemma below is t
- `def Sumcheck.Structured.roundKnowledgeError` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:473](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L473) — Round-by-round knowledge error for a single round of the structured sumcheck: the Schwartz–Zippel bo

### `rsPoint_injective` (2 declarations, 2 files)

- `theorem ArkLib.KoalaBearAttack.rsPoint_injective` [ArkLib/ToMathlib/KoalaBearAttackInstance.lean:77](../../../ArkLib/ToMathlib/KoalaBearAttackInstance.lean#L77) — Distinct `Fin 4` points give distinct field points (characteristic `p > 4`).
- `theorem KoalaBear.rsPoint_injective` [ArkLib/ToMathlib/KoalaIRSAccounting.lean:66](../../../ArkLib/ToMathlib/KoalaIRSAccounting.lean#L66) — The four evaluation points `rsPoint j = (j.val : Sextic)` are pairwise distinct: each `j.val` is `<

### `rs_lambda_high_rate_jh01` (2 declarations, 2 files)

- `theorem CodingTheory.rs_lambda_high_rate_jh01` [ArkLib/Data/CodingTheory/ListDecoding/Bounds/RandomAndReedSolomon.lean:861](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds/RandomAndReedSolomon.lean#L861) — **ABF26 Theorem 3.14 [JH01 Thm 2], repaired list-size form.** Large-rate Reed-Solomon lower bound. F
- `theorem CodingTheory.ReedSolomon.rs_lambda_high_rate_jh01` [ArkLib/Data/CodingTheory/ListDecoding/JH01.lean:214](../../../ArkLib/Data/CodingTheory/ListDecoding/JH01.lean#L214) — ABF26 Theorem 3.14 / JH01 Theorem 2, in a repaired list-size form.  For every `j ≥ 2`, infinitely ma

### `run` (2 declarations, 2 files)

- `def AGM.Adversary.run` [ArkLib/AGM/Basic.lean:484](../../../ArkLib/AGM/Basic.lean#L484) — Running the adversary on a given table, returning the list of group elements it is supposed to outpu
- `def Prover.run` [ArkLib/OracleReduction/Execution.lean:97](../../../ArkLib/OracleReduction/Execution.lean#L97) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `secondSCVP_mem_restrictDegree` (2 declarations, 2 files)

- `theorem Spartan.Spec.secondSCVP_mem_restrictDegree` [ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean:76](../../../ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean#L76) — The second sum-check virtual polynomial has degree `<= 2` per variable.
- `theorem Spartan.secondSCVP_mem_restrictDegree` [ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean:74](../../../ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean#L74) — **Degree bound of the second sum-check virtual polynomial** (`≤ 2` per variable): packages `ℳ(Y)` fo

### `seqCompose_perfectCompleteness_threaded` (2 declarations, 2 files)

- `theorem OracleReduction.seqCompose_perfectCompleteness_threaded` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeOracleCompleteness.lean:107](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeOracleCompleteness.lean#L107) — **n-ary message-seam `seqCompose` perfect completeness for oracle reductions (issue #29).** Every co
- `theorem Reduction.seqCompose_perfectCompleteness_threaded` [ArkLib/OracleReduction/Composition/Sequential/SeqComposePerfectCompletenessThreaded.lean:59](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposePerfectCompletenessThreaded.lean#L59) — **n-ary message-seam `seqCompose` perfect completeness, keystones inlined.** Every component is none

### `shiftSeries` (2 declarations, 2 files)

- `def ArkLib.Claim59Conditional.shiftSeries` [ArkLib/ToMathlib/BCIKS20PointwiseConditional.lean:53](../../../ArkLib/ToMathlib/BCIKS20PointwiseConditional.lean#L53) — The BCIKS shift series corresponding to the substitution $X \mapsto X - x_0$.
- `def ArkLib.SubstFieldCaveat.shiftSeries` [ArkLib/ToMathlib/SubstFieldCaveat.lean:75](../../../ArkLib/ToMathlib/SubstFieldCaveat.lean#L75) — The shift series corresponding to the substitution $X \mapsto X - x_0$.

### `simulateQ_askInput` (2 declarations, 2 files)

- `theorem StirIOP.MultiRound.simulateQ_askInput` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:248](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L248) — `simulateQ` collapse for the input-oracle query.
- `theorem Whir302Checked.simulateQ_askInput` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:447](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L447) — `simulateQ` collapse for an input-oracle query.

### `simulateQ_askList` (2 declarations, 2 files)

- `theorem StirIOP.MultiRound.simulateQ_askList` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:168](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L168) — If every step of an `askList` simulates to a pure value, the whole `askList` collapses to the corres
- `theorem Whir302Checked.simulateQ_askList` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:113](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L113) — If every step of an `askList` simulates to a pure value, the whole `askList` collapses to the corres

### `simulateQ_askMsg` (2 declarations, 2 files)

- `theorem StirIOP.MultiRound.simulateQ_askMsg` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:254](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L254) — `simulateQ` collapse for a message-oracle query.
- `theorem Whir302Checked.simulateQ_askMsg` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:438](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L438) — `simulateQ` collapse for a message-oracle query.

### `simulateQ_optionT_failure'` (2 declarations, 2 files)

- `theorem Logup.simulateQ_optionT_failure'` [ArkLib/ProofSystem/Logup/Security/OuterRun.lean:52](../../../ArkLib/ProofSystem/Logup/Security/OuterRun.lean#L52) — `simulateQ` commutes with `OptionT` `failure`.
- `theorem RingSwitching.SumcheckPhase.simulateQ_optionT_failure'` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:102](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L102) — `simulateQ` commutes with `OptionT` `failure`, for an arbitrary lawful target monad `m` (so it appli

### `simulateQ_optionT_pure'` (2 declarations, 2 files)

- `theorem Logup.simulateQ_optionT_pure'` [ArkLib/ProofSystem/Logup/Security/OuterRun.lean:44](../../../ArkLib/ProofSystem/Logup/Security/OuterRun.lean#L44) — `simulateQ` commutes with `OptionT.pure`.
- `theorem RingSwitching.SumcheckPhase.simulateQ_optionT_pure'` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:91](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L91) — `simulateQ` commutes with `OptionT.pure` (no explicit empty-spec universes).

### `simulateQ_oracleVerify_eq` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.SingleRound.Simple.simulateQ_oracleVerify_eq` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:965](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L965) — Closed form of the simulated oracle-verifier `verify`: the inner `simOracle2` simulation collapses t
- `theorem ToyProblem.Spec.simulateQ_oracleVerify_eq` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:788](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L788) — **Closed form of the compiled toy-problem oracle verifier.** Simulating `oracleVerifier.verify` agai

### `simulateQ_simOracle2_query` (2 declarations, 2 files)

- `lemma RingSwitching.BatchingPhase.simulateQ_simOracle2_query` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:84](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L84) — OptionT/query form of `simulateQ_simOracle2_messageQuery`.
- `lemma RingSwitching.simulateQ_simOracle2_query` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1543](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1543) — **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s

### `simulateQ_simOracle_foldlM` (2 declarations, 2 files)

- `theorem simulateQ_simOracle_foldlM` [ArkLib/OracleReduction/SimOracleFoldlM.lean:27](../../../ArkLib/OracleReduction/SimOracleFoldlM.lean#L27) — If every step of a `foldlM` simulates (under the honest single-family oracle) to a pure value, the w
- `lemma Spartan.Spec.simulateQ_simOracle_foldlM` [ArkLib/ProofSystem/Spartan/SecondSumcheckFaithful.lean:75](../../../ArkLib/ProofSystem/Spartan/SecondSumcheckFaithful.lean#L75) — Simulating a `foldlM` whose every step simulates to a pure value collapses to the `foldl` of the pur

### `singleton_bound` (2 declarations, 2 files)

- `theorem singleton_bound` [ArkLib/Data/CodingTheory/Basic/LinearCode.lean:121](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean#L121) — **Singleton bound** for arbitrary codes
- `theorem ArkLib.CS25.singleton_bound` [ArkLib/Data/CodingTheory/SingletonBound.lean:30](../../../ArkLib/Data/CodingTheory/SingletonBound.lean#L30) — **Singleton bound.**  A code with minimum distance `≥ d` (`d ≥ 1`) has at most `q^(n−(d−1))` codewor

### `soundness.mono_error` (2 declarations, 2 files)

- `theorem Verifier.soundness.mono_error` [ArkLib/OracleReduction/Security/Basic.lean:315](../../../ArkLib/OracleReduction/Security/Basic.lean#L315) — Verifier soundness is monotone in the allowed soundness error.
- `theorem Verifier.StateRestoration.soundness.mono_error` [ArkLib/OracleReduction/Security/StateRestoration.lean:143](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L143) — State-restoration soundness is monotone in the allowed soundness error.

### `soundness.mono_languages` (2 declarations, 2 files)

- `theorem Verifier.soundness.mono_languages` [ArkLib/OracleReduction/Security/Basic.lean:331](../../../ArkLib/OracleReduction/Security/Basic.lean#L331) — Verifier soundness is monotone in the input and output languages. If soundness holds for a smaller h
- `theorem Verifier.StateRestoration.soundness.mono_languages` [ArkLib/OracleReduction/Security/StateRestoration.lean:157](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L157) — State-restoration soundness is monotone under enlarging the honest input language and shrinking the

### `sq_sum_le_card_support_mul_sum_sq` (2 declarations, 2 files)

- `theorem Finset.sq_sum_le_card_support_mul_sum_sq` [ArkLib/ToMathlib/SqSumCardSupport.lean:20](../../../ArkLib/ToMathlib/SqSumCardSupport.lean#L20) — (no docstring)
- `theorem ArkLib.sq_sum_le_card_support_mul_sum_sq` [ArkLib/ToMathlib/SupportSqBound.lean:25](../../../ArkLib/ToMathlib/SupportSqBound.lean#L25) — **Cauchy-Schwarz support bound.** Over a finite type, `(∑ f)² ≤ \|support f\| · (∑ f²)`.

### `sqrtRate_le_one` (2 declarations, 2 files)

- `theorem ArkLib.BoundaryCardResidualRefutation.sqrtRate_le_one` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean:68](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean#L68) — (no docstring)
- `theorem ArkLib.BoundaryCardStrictInteriorRefutation.sqrtRate_le_one` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardStrictInteriorRefutation.lean:131](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardStrictInteriorRefutation.lean#L131) — (no docstring)

### `statisticalHVZK` (2 declarations, 2 files)

- `def OracleReduction.statisticalHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:53](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L53) — Statistical HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`.
- `def Reduction.statisticalHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:80](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L80) — A reduction satisfies statistical honest-verifier zero-knowledge with error `ε` if the simulator's t

### `statisticalHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:46](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L46) — **OracleReduction statistical HVZK transfers along an equal honest distribution.**
- `theorem Reduction.statisticalHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:80](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L80) — **Statistical HVZK transfers along an `evalDist`-equal honest distribution.** The same simulator and

### `statisticalHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:73](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L73) — **OracleReduction statistical HVZK honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.statisticalHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:109](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L109) — **Statistical HVZK honest-distribution congruence with opposite-order equality.**

### `statisticalHVZK.isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:141](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L141) — **A concrete OracleReduction statistical-HVZK simulator witnesses existential statistical HVZK.**
- `theorem Reduction.statisticalHVZK.isStatHVZK` [ArkLib/ToMathlib/ZKTransferBricks.lean:184](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L184) — **A concrete statistical-HVZK simulator witnesses existential statistical HVZK.**

### `statisticalHVZK.isStatHVZK_of_simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK_of_simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:164](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L164) — **Package an OracleReduction statistical-HVZK proof after normalizing the simulator distribution.**
- `theorem Reduction.statisticalHVZK.isStatHVZK_of_simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:205](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L205) — **Package a statistical-HVZK proof after normalizing the simulator distribution.**

### `statisticalHVZK.isStatHVZK_of_simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:188](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L188) — **Package an OracleReduction statistical-HVZK proof after simulator normalization in the opposite di
- `theorem Reduction.statisticalHVZK.isStatHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:227](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L227) — **Package a statistical-HVZK proof after simulator normalization in the opposite direction.**

### `statisticalHVZK.mono_error` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:140](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L140) — Statistical HVZK for oracle reductions is monotone in the error bound.
- `theorem Reduction.statisticalHVZK.mono_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:188](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L188) — **Statistical HVZK is monotone in the error.** A simulator within total-variation distance `ε₁` is a

### `statisticalHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:129](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L129) — Statistical HVZK for oracle reductions is antitone in the relation.
- `theorem Reduction.statisticalHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:177](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L177) — **Statistical HVZK is antitone in the relation.**

### `statisticalHVZK.mono_relation_error` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_relation_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:211](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L211) — Statistical HVZK for oracle reductions transports across both relation restriction and error relaxat
- `theorem Reduction.statisticalHVZK.mono_relation_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:250](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L250) — **Statistical HVZK transports across both relation restriction and error relaxation.**

### `statisticalHVZK.simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:97](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L97) — **OracleReduction statistical HVZK is preserved under an equal simulator distribution.**
- `theorem Reduction.statisticalHVZK.simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:138](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L138) — **Statistical HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a simulator that

### `statisticalHVZK.simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:119](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L119) — **OracleReduction statistical HVZK simulator congruence with opposite-order equality.**
- `theorem Reduction.statisticalHVZK.simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:163](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L163) — **Statistical HVZK simulator congruence with opposite-order equality.**

### `statisticalHVZK.simulator_triangle` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_triangle` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:199](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L199) — **Triangle composition of statistical HVZK at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.simulator_triangle` [ArkLib/ToMathlib/ZKTransferBricks.lean:240](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L240) — **Triangle composition of statistical HVZK.** If `sim₁` is within `ε₁` of the honest distribution an

### `statisticalHVZK.triangle_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:213](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L213) — **Approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.triangle_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:265](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L265) — **Approximate honest-distribution transfer for statistical HVZK.** If a simulator is statistical-HVZ

### `statisticalHVZK.triangle_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:227](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L227) — **Symmetric-facing approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:291](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L291) — **Symmetric-facing approximate honest-distribution transfer.** This is the same result as `statistic

### `statisticalHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:255](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L255) — Symmetric-facing zero-error approximate honest-distribution transfer for statistical HVZK at the Ora
- `theorem Reduction.statisticalHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:324](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L324) — Symmetric-facing zero-error approximate honest-distribution transfer for statistical HVZK.

### `statisticalHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:241](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L241) — **Zero-error approximate honest-distribution transfer for statistical HVZK at the OracleReduction AP
- `theorem Reduction.statisticalHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:308](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L308) — **Zero-error approximate honest-distribution transfer for statistical HVZK.** If the honest transcri

### `statisticalHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:334](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L334) — **Symmetric-facing OracleReduction constant-simulator criterion for statistical HVZK.**
- `theorem Reduction.statisticalHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:419](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L419) — **Symmetric-facing constant-simulator criterion for statistical HVZK.**

### `statisticalHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:308](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L308) — **OracleReduction constant-simulator criterion for statistical HVZK.**
- `theorem Reduction.statisticalHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:394](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L394) — **Statistical constant-simulator criterion.** If the honest transcript distribution is `evalDist`-eq

### `statisticalHVZK_zero.perfectHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_zero.perfectHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:236](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L236) — Zero-error statistical HVZK for oracle reductions converts back to perfect HVZK for the same simulat
- `theorem Reduction.statisticalHVZK_zero.perfectHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:272](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L272) — **Zero-error statistical HVZK converts back to perfect HVZK for the same simulator.**

### `statisticalHVZK_zero.perfectHVZK_mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_zero.perfectHVZK_mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:248](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L248) — Zero-error statistical HVZK for oracle reductions transports back to perfect HVZK on a subrelation.
- `theorem Reduction.statisticalHVZK_zero.perfectHVZK_mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:283](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L283) — **Zero-error statistical HVZK transports back to perfect HVZK on a subrelation.** The same simulator

### `subdomainZeroEquiv` (2 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomainZeroEquiv` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:133](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L133) — The zeroth subdomain has the same finite set of field points as the ambient domain.
- `def Fri.subdomainZeroEquiv` [ArkLib/ProofSystem/BatchedFri/Security.lean:1598](../../../ArkLib/ProofSystem/BatchedFri/Security.lean#L1598) — The round-zero Batched FRI subdomain is equivalent to the original evaluation domain.

### `sum_div_mul_prod_eq_sum_mul_prod_erase` (2 declarations, 2 files)

- `theorem Logup.sum_div_mul_prod_eq_sum_mul_prod_erase` [ArkLib/ProofSystem/Logup/Common.lean:755](../../../ArkLib/ProofSystem/Logup/Common.lean#L755) — (no docstring)
- `theorem Finset.sum_div_mul_prod_eq_sum_mul_prod_erase` [ArkLib/ToMathlib/ProtocolCountingBricks.lean:30](../../../ArkLib/ToMathlib/ProtocolCountingBricks.lean#L30) — **LogUp clear-denominators core.** `(∑ num/den)·(∏ den) = ∑ num·∏_{erase} den`.

### `sumcheckConsistencyProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.sumcheckConsistencyProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1475](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1475) — Sumcheck consistency: the claimed sumcheck target equals the sum of `H` over the boolean hypercube o
- `def Sumcheck.Structured.sumcheckConsistencyProp` [ArkLib/ProofSystem/Sumcheck/Structured.lean:212](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L212) — Sumcheck consistency: the claimed sum equals the actual polynomial evaluation sum over the evaluatio

### `sumcheckConsistency_at_last_simplifies` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.sumcheckConsistency_at_last_simplifies` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1185](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1185) — At `Fin.last ℓ`, sumcheck consistency is the single empty-variable evaluation.
- `lemma Binius.FRIBinius.CoreInteractionPhase.sumcheckConsistency_at_last_simplifies` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:685](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L685) — At `Fin.last ℓ'`, sumcheck consistency simplifies to a single evaluation.

### `sumcheckFoldOracleReduction` (2 declarations, 2 files)

- `def sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:805](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L805) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:155](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L155) — (no docstring)

### `sumcheckFoldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:910](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L910) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:253](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L253) — (no docstring)

### `sumcheckFoldOracleVerifier` (2 declarations, 2 files)

- `def sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:521](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L521) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:148](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L148) — (no docstring)

### `sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1064](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1064) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:443](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L443) — (no docstring)

### `support_mk` (2 declarations, 2 files)

- `lemma ReduceClaim.support_mk` [ArkLib/ProofSystem/Component/ReduceClaim.lean:129](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L129) — (no docstring)
- `lemma OptionT.support_mk` [ArkLib/ToVCVio/Lemmas.lean:106](../../../ArkLib/ToVCVio/Lemmas.lean#L106) — (no docstring)

### `toMLE_evalC_eq_sum` (2 declarations, 2 files)

- `theorem Spartan.Spec.toMLE_evalC_eq_sum` [ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean:50](../../../ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean#L50) — (no docstring)
- `theorem Spartan.toMLE_evalC_eq_sum` [ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean:41](../../../ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean#L41) — **Polynomial-level partial evaluation of `Matrix.toMLE`.** Fixing the row variables at `r_x` yields

### `toMLE_evalC_mem_restrictDegree` (2 declarations, 2 files)

- `theorem Spartan.Spec.toMLE_evalC_mem_restrictDegree` [ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean:62](../../../ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean#L62) — (no docstring)
- `theorem Spartan.toMLE_evalC_mem_restrictDegree` [ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean:54](../../../ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean#L54) — **The row-fixed matrix MLE is multilinear in the column variables (degree ≤ 1).**

### `toMonadDecoration` (2 declarations, 2 files)

- `def Interaction.OracleDecoration.toMonadDecoration` [ArkLib/Interaction/Oracle/Core.lean:802](../../../ArkLib/Interaction/Oracle/Core.lean#L802) — (no docstring)
- `def Interaction.Oracle.Spec.toMonadDecoration` [ArkLib/Interaction/Oracle/Spec.lean:193](../../../ArkLib/Interaction/Oracle/Spec.lean#L193) — (no docstring)

### `toOracleSpec` (2 declarations, 2 files)

- `def Interaction.Oracle.Spec.toOracleSpec` [ArkLib/Interaction/Oracle/Spec.lean:158](../../../ArkLib/Interaction/Oracle/Spec.lean#L158) — (no docstring)
- `def OracleInterface.toOracleSpec` [ArkLib/OracleReduction/OracleInterface.lean:92](../../../ArkLib/OracleReduction/OracleInterface.lean#L92) — Converts an indexed type family of oracle interfaces into an oracle specification. Notation: `[v]ₒ`

### `toPoly` (2 declarations, 2 files)

- `def GSMultInterp.toPoly` [ArkLib/Data/CodingTheory/GuruswamiSudan/DictionaryBridge.lean:26](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/DictionaryBridge.lean#L26) — The bivariate polynomial `∑_{(s,t)∈monoIdx} c(s,t)·X^s·Y^t` carried by a coefficient vector `c`, as
- `def UniPoly.toPoly` [ArkLib/Data/UniPoly/Basic.lean:758](../../../ArkLib/Data/UniPoly/Basic.lean#L758) — Convert a `UniPoly` to a (mathlib) `Polynomial`.

### `toPoly_add` (2 declarations, 2 files)

- `theorem GSMultInterp.toPoly_add` [ArkLib/Data/CodingTheory/GuruswamiSudan/DictionaryBridge.lean:48](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/DictionaryBridge.lean#L48) — `toPoly` is additive in the coefficient vector.
- `theorem UniPoly.toPoly_add` [ArkLib/Data/UniPoly/Basic.lean:854](../../../ArkLib/Data/UniPoly/Basic.lean#L854) — `UniPoly` addition is mapped to `Polynomial` addition

### `umCode` (2 declarations, 2 files)

- `def ReedSolomon.Multiplicity.umCode` [ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean:97](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean#L97) — **ABF26 Definition A.7 [GW13, KSY14]** — the univariate multiplicity code `UM[F, L, k, s]`. Defined
- `def CodingTheory.umCode` [ArkLib/Data/CodingTheory/SubspaceDesign.lean:1105](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean#L1105) — **ABF26 DA.7 (Univariate Multiplicity codes)**. The UM code `UM[F, L, k, s]`: `UM[F, L, k, s] := { f

### `uniform` (2 declarations, 2 files)

- `def OracleReduction.OracleDistribution.uniform` [ArkLib/OracleReduction/Security/OracleDistribution.lean:119](../../../ArkLib/OracleReduction/Security/OracleDistribution.lean#L119) — Uniform full-table sampling. Requires `SampleableType` over the dependent product `OracleFamily spec
- `def SumcheckDomain.uniform` [ArkLib/ProofSystem/Sumcheck/Domain.lean:74](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L74) — The *uniform* domain: the same `m`-point embedding `D₀` in every one of the `k` coordinates. Its `cu

### `unroll_2_message_VP` (2 declarations, 2 files)

- `theorem StirIOP.Round.unroll_2_message_VP` [ArkLib/ProofSystem/Stir/RoundCompleteness.lean:55](../../../ArkLib/ProofSystem/Stir/RoundCompleteness.lean#L55) — (no docstring)
- `theorem WhirIOP.FoldRound.unroll_2_message_VP` [ArkLib/ProofSystem/Whir/FoldRound.lean:65](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L65) — (no docstring)

### `vanishesToOrder` (2 declarations, 2 files)

- `def GSMultInterp.vanishesToOrder` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:153](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L153) — `Q` (given by coefficient vector `c`) **vanishes to order `m`** at `(x₀, y₀)`: every Hasse coefficie
- `def ArkLib.GS.vanishesToOrder` [ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean#L60) — `Q : F[X][Y]` **vanishes to order `m` at `(a, b)`** when, for every `Y`-index `j`, the inner Taylor

### `vecL2NormSq` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:91](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L91) — Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms.
- `def ArkLib.Lattices.CenteredCoeffView.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/Norms.lean:80](../../../ArkLib/Data/Lattices/CyclotomicRing/Norms.lean#L80) — Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms.

### `verifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:58](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L58) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:168](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L168) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s

### `verifyOpening` (2 declarations, 2 files)

- `def KZG.verifyOpening` [ArkLib/Commitments/Functional/KZG/Basic.lean:69](../../../ArkLib/Commitments/Functional/KZG/Basic.lean#L69) — To verify a KZG opening `opening` for a commitment `commitment` at point `z` with claimed evaluation
- `def InductiveMerkleTree.verifyOpening` [ArkLib/Commitments/Functional/MerkleTree/Batch.lean:101](../../../ArkLib/Commitments/Functional/MerkleTree/Batch.lean#L101) — Verify one packaged opening against a claimed root, in `OracleComp (spec α)`.

### `weight_Λ_over_𝒪_add_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_add_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:650](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L650) — `Λ_𝒪(a + b) ≤ max(Λ_𝒪 a, Λ_𝒪 b)`: sub-additivity over `𝒪 H`.
- `lemma ArkLib.weight_Λ_over_𝒪_add_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:82](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L82) — Sub-additivity of the `𝒪`-weight under addition: `Λ(a + b) ≤ max (Λ a) (Λ b)`.

### `weight_Λ_over_𝒪_mul_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_mul_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:635](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L635) — `Λ_𝒪(a · b) ≤ Λ_𝒪(a) + Λ_𝒪(b)`: sub-multiplicativity over `𝒪 H`.  Take the canonical representatives
- `lemma ArkLib.weight_Λ_over_𝒪_mul_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:143](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L143) — Sub-multiplicativity of the `𝒪`-weight: `Λ(a · b) ≤ Λ a + Λ b`. This is the central inequality the A

### `weight_Λ_over_𝒪_neg` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_neg` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:665](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L665) — `Λ_𝒪(-a) = Λ_𝒪(a)`: the `𝒪`-weight is negation-invariant (`mk (-ra) = -a`, `weight_Λ_neg`).
- `lemma ArkLib.weight_Λ_over_𝒪_neg` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:99](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L99) — Sub-additivity of the `𝒪`-weight under negation: it is invariant.

### `weight_Λ_over_𝒪_pow_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_pow_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:691](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L691) — `Λ_𝒪(a ^ k) ≤ k • Λ_𝒪(a)` (i.e. `≤ k · Λ_𝒪(a)` in `WithBot ℕ`): the power bound over `𝒪 H`, by induc
- `lemma ArkLib.weight_Λ_over_𝒪_pow_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:158](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L158) — Sub-multiplicativity for powers: `Λ(a ^ n) ≤ n • Λ a` (with `0 • Λ a = 0`, matching `weight_Λ_over_𝒪

### `weight_Λ_over_𝒪_sum_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_sum_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:677](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L677) — `Λ_𝒪(∑ᵢ f i) ≤ sup of Λ_𝒪(f i)`: the `𝒪`-weight of a finite sum is bounded by the sup of the summand
- `lemma ArkLib.weight_Λ_over_𝒪_sum_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:124](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L124) — The `𝒪`-weight of a finite sum is bounded by the `sup` of the summands' weights.

### `whirCheckedVectorIOP_isSecureWithGap_of_rbr` (2 declarations, 2 files)

- `theorem Whir302Checked.whirCheckedVectorIOP_isSecureWithGap_of_rbr` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:1006](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L1006) — With the completeness leg PROVEN for the checking verifier, `IsSecureWithGap` for the checked WHIR `
- `theorem WhirIOP.whirCheckedVectorIOP_isSecureWithGap_of_rbr` [ArkLib/ProofSystem/Whir/ProtocolSoundness.lean:202](../../../ArkLib/ProofSystem/Whir/ProtocolSoundness.lean#L202) — The checked WHIR `VectorIOP` has the secure-with-gap package once its genuine RBR knowledge-soundnes

### `whirVectorIOP_isSecureWithGap_indicator` (2 declarations, 2 files)

- `theorem WhirIOP.whirVectorIOP_isSecureWithGap_indicator` [ArkLib/ProofSystem/Whir/ProtocolSoundness.lean:161](../../../ArkLib/ProofSystem/Whir/ProtocolSoundness.lean#L161) — Secure-with-gap package for the current WHIR skeleton at the proved indicator budget.
- `theorem Whir302RBR.whirVectorIOP_isSecureWithGap_indicator` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:478](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L478) — **The full security package with the indicator budget:** the concrete WHIR `VectorIOP` is secure wit

### `whirVectorIOP_perfectCompleteness_holds` (2 declarations, 2 files)

- `theorem Whir302.whirVectorIOP_perfectCompleteness_holds` [ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean:125](../../../ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean#L125) — (no docstring)
- `theorem Whir302RBR.whirVectorIOP_perfectCompleteness_holds` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:469](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L469) — The perfect-completeness residual of the concrete WHIR `VectorIOP` (replica of `Whir302.whirVectorIO

### `whirVectorIOP_rbrKnowledgeSoundness_indicator` (2 declarations, 2 files)

- `theorem WhirIOP.whirVectorIOP_rbrKnowledgeSoundness_indicator` [ArkLib/ProofSystem/Whir/ProtocolSoundness.lean:101](../../../ArkLib/ProofSystem/Whir/ProtocolSoundness.lean#L101) — **Proved indicator-budget RBR package for the current WHIR skeleton.**  The state-function argument
- `theorem Whir302RBR.whirVectorIOP_rbrKnowledgeSoundness_indicator` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:335](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L335) — **Discharged #302 residual (indicator budget):** the concrete WHIR `VectorIOP` satisfies round-by-ro

### `witnessStructuralInvariant` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1467](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1467) — This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
- `def RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:492](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L492) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`

### `AnchoredFrom` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.AnchoredFrom` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:78](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L78) — Some entry of the log is an anchored collision against the running cache.
- `def DuplexSpongeFS.EagerLazyDS.AnchoredFrom` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:78](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L78) — Some entry of the log is an anchored collision against the running cache.

### `ConsistentFrom` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.ConsistentFrom` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:73](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L73) — The whole log is consistent with the running cache.
- `def DuplexSpongeFS.EagerLazyDS.ConsistentFrom` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:73](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L73) — The whole log is consistent with the running cache.

### `DSEntry` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.EagerLazyDS.DSEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L46) — A single log entry of the combined oracle.
- `abbrev DuplexSpongeFS.EagerLazyDS.DSEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L46) — A single log entry of the combined oracle.

### `EPaperReduction` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.EagerLazyDS.EPaperReduction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1598](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1598) — The dedup reduction (the one remaining pure-combinatorics obligation): a log consistent with the emp
- `abbrev DuplexSpongeFS.EagerLazyDS.EPaperReduction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1598](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1598) — The dedup reduction (the one remaining pure-combinatorics obligation): a log consistent with the emp

### `E_of_hasFirstHashForwardCapacityBeforeHash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.E_of_hasFirstHashForwardCapacityBeforeHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:220](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L220) — Raw first-occurrence collision shape fires the combined bad event `E`: transport the shape through d
- `theorem DuplexSpongeFS.Sponge316.E_of_hasFirstHashForwardCapacityBeforeHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:220](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L220) — Raw first-occurrence collision shape fires the combined bad event `E`: transport the shape through d

### `FwdKeysNodup` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.FwdKeysNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:661](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L661) — The forward keys of the permutation cache are distinct.
- `def DuplexSpongeFS.EagerLazyDS.FwdKeysNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:661](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L661) — The forward keys of the permutation cache are distinct.

### `HasCapBeforeInverseAnswerPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:126](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L126) — Broad (guard-free) inverse-anchored collision shape, for the dedup'd base trace.
- `def DuplexSpongeFS.Sponge316.HasCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:126](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L126) — Broad (guard-free) inverse-anchored collision shape, for the dedup'd base trace.

### `HasFirstCapBeforeInverseAnswerPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:116](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L116) — First-occurrence inverse-anchored collision shape (paper semantics, ℕ-indexed): an inverse entry wit
- `def DuplexSpongeFS.Sponge316.HasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:116](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L116) — First-occurrence inverse-anchored collision shape (paper semantics, ℕ-indexed): an inverse entry wit

### `HasFirstHashFwdCapNat` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstHashFwdCapNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:55](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L55) — ℕ-indexed, `getElem?`-based restatement of `HasFirstHashForwardCapacityBeforeHash`: a first-occurren
- `def DuplexSpongeFS.Sponge316.HasFirstHashFwdCapNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:55](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L55) — ℕ-indexed, `getElem?`-based restatement of `HasFirstHashForwardCapacityBeforeHash`: a first-occurren

### `HasFirstHashPermCapNatPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:707](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L707) — ℕ-indexed first-hash collision shape, paper semantics: the hash anchor is first-occurrence, and an e
- `def DuplexSpongeFS.Sponge316.HasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:707](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L707) — ℕ-indexed first-hash collision shape, paper semantics: the hash anchor is first-occurrence, and an e

### `HasFirstPermCapacityBeforeForwardOutputPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:271](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L271) — Paper-semantics first-occurrence collision shape: the tracked forward entry has no prior copy of its
- `def DuplexSpongeFS.Sponge316.HasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:271](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L271) — Paper-semantics first-occurrence collision shape: the tracked forward entry has no prior copy of its

### `HasFirstPermCapacityBeforeForwardOutputPaperNat` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstPermCapacityBeforeForwardOutputPaperNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:331](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L331) — Natural-index form of `HasFirstPermCapacityBeforeForwardOutputPaper`, for the recursive `eraseIdx` p
- `def DuplexSpongeFS.Sponge316.HasFirstPermCapacityBeforeForwardOutputPaperNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:331](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L331) — Natural-index form of `HasFirstPermCapacityBeforeForwardOutputPaper`, for the recursive `eraseIdx` p

### `HasHashPermCapBeforeHashPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasHashPermCapBeforeHashPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:719](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L719) — Broad (no-firstness) hash-anchored collision shape, paper semantics.
- `def DuplexSpongeFS.Sponge316.HasHashPermCapBeforeHashPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:719](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L719) — Broad (no-firstness) hash-anchored collision shape, paper semantics.

### `HasPermCapacityBeforeForwardOutputPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:256](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L256) — Direction-agnostic prior-permutation capacity shape: some permutation entry (either direction) stric
- `def DuplexSpongeFS.Sponge316.HasPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:256](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L256) — Direction-agnostic prior-permutation capacity shape: some permutation entry (either direction) stric

### `Lemma5_12HonestResidualPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.Lemma5_12HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:658](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L658) — CO25 Lemma 5.12 (honest form), **paper semantics**: off the paper combined bad event, no BackTrack c
- `def DuplexSpongeFS.Sponge316.Lemma5_12HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:658](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L658) — CO25 Lemma 5.12 (honest form), **paper semantics**: off the paper combined bad event, no BackTrack c

### `Lemma5_14HonestResidualPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.Lemma5_14HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:666](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L666) — CO25 Lemma 5.14 (honest form), **paper semantics**: off the paper combined bad event, the backtrack
- `def DuplexSpongeFS.Sponge316.Lemma5_14HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:666](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L666) — CO25 Lemma 5.14 (honest form), **paper semantics**: off the paper combined bad event, the backtrack

### `Lemma5_16HonestResidualPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.Lemma5_16HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:676](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L676) — CO25 Lemma 5.16 (honest form), **paper semantics**: off the paper combined bad event, all chain quer
- `def DuplexSpongeFS.Sponge316.Lemma5_16HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:676](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L676) — CO25 Lemma 5.16 (honest form), **paper semantics**: off the paper combined bad event, all chain quer

### `OracleInterface` (3 declarations, 2 files)

- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:88](../../../ArkLib/OracleReduction/Basic.lean#L88) — (no docstring)
- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:162](../../../ArkLib/OracleReduction/Basic.lean#L162) — (no docstring)
- `class OracleInterface` [ArkLib/OracleReduction/OracleInterface.lean:52](../../../ArkLib/OracleReduction/OracleInterface.lean#L52) — `OracleInterface` is a type class that provides an oracle interface for a type `Message`. It consist

### `SlotKind` (2 declarations, 2 files)

- `inductive DuplexSpongeFS.Sponge316.SlotKind` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:66](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L66) — A tagged trace slot: either a hash entry or a forward permutation entry. The tag determines the slot
- `inductive DuplexSpongeFS.Sponge316.SlotKind` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:66](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L66) — A tagged trace slot: either a hash entry or a forward permutation entry. The tag determines the slot

### `SlotKind.entry` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.SlotKind.entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L70) — (no docstring)
- `def DuplexSpongeFS.Sponge316.SlotKind.entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L70) — (no docstring)

### `SlotKind.guard` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.SlotKind.guard` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:78](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L78) — The slot's first-occurrence guard: no strictly earlier slot holds any certificate target for this en
- `def DuplexSpongeFS.Sponge316.SlotKind.guard` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:78](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L78) — The slot's first-occurrence guard: no strictly earlier slot holds any certificate target for this en

### `SlotKind.not_redundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.SlotKind.not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:93](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L93) — A guarded slot is never paper-redundant.
- `lemma DuplexSpongeFS.Sponge316.SlotKind.not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:93](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L93) — A guarded slot is never paper-redundant.

### `SlotKind.ok` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.SlotKind.ok` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:88](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L88) — A guarded slot: the entry sits at slot `i` and is the first occurrence of its certificate class.
- `def DuplexSpongeFS.Sponge316.SlotKind.ok` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:88](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L88) — A guarded slot: the entry sits at slot `i` and is the first occurrence of its certificate class.

### `SlotKind.ok_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.SlotKind.ok_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L148) — A guarded slot shifts through `eraseIdx` of a different index.
- `lemma DuplexSpongeFS.Sponge316.SlotKind.ok_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L148) — A guarded slot shifts through `eraseIdx` of a different index.

### `TwoSurvivors` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TwoSurvivors` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:164](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L164) — Two ordered guarded slots, the raw-trace shape of the two-survivor transport.
- `def DuplexSpongeFS.Sponge316.TwoSurvivors` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:164](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L164) — Two ordered guarded slots, the raw-trace shape of the two-survivor transport.

### `aligned_inputs` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.aligned_inputs` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:191](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L191) — **End-aligned input agreement** (CO25 Claim 5.19, Eq. 44 induction): off `EPaper`, the input states
- `theorem DuplexSpongeFS.Paper.aligned_inputs` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:191](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L191) — **End-aligned input agreement** (CO25 Claim 5.19, Eq. 44 induction): off `EPaper`, the input states

### `aligned_inputs_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.aligned_inputs_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:546](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L546) — End-aligned input agreement: off `BadEventDSPaper.E`, two family sequences agree at end-aligned inpu
- `theorem DuplexSpongeFS.Sponge316.aligned_inputs_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:546](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L546) — End-aligned input agreement: off `BadEventDSPaper.E`, two family sequences agree at end-aligned inpu

### `anchoredFrom_of_at` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_at` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L70) — **Positional anchoring**: a `collisionStep` at any position (against the prefix fold) yields `Anchor
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_at` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L70) — **Positional anchoring**: a `collisionStep` at any position (against the prefix fold) yields `Anchor

### `anchoredFrom_of_eraseIdx_classRed` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_eraseIdx_classRed` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:537](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L537) — A class-redundant erasure reflects anchoredness in a consistent log.
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_eraseIdx_classRed` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:537](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L537) — A class-redundant erasure reflects anchoredness in a consistent log.

### `anchoredFrom_of_eraseIdx_of_noop` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_eraseIdx_of_noop` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:375](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L375) — Erasing a no-op entry reflects anchoredness: a collision in the erased log is a collision in the ori
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_eraseIdx_of_noop` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:375](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L375) — Erasing a no-op entry reflects anchoredness: a collision in the erased log is a collision in the ori

### `anchoredFrom_of_removeRedundantEntryDSPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:595](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L595) — Anchoredness of the paper-deduplicated log reflects back to the original consistent log.
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:595](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L595) — Anchoredness of the paper-deduplicated log reflects back to the original consistent log.

### `anchoredFrom_of_removeRedundantEntryDSPaper_aux` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_removeRedundantEntryDSPaper_aux` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:557](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L557) — (no docstring)
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_removeRedundantEntryDSPaper_aux` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:557](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L557) — (no docstring)

### `anchoredFrom_of_split` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1084](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1084) — **Constructive anchoring**: a collision at a split point makes the whole fold anchored.
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1084](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1084) — **Constructive anchoring**: a collision at a split point makes the whole fold anchored.

### `anchored_of_E_func` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_func` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1569](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1569) — **E_func arm.** A function violation among dedup entries is impossible in a non-anchored consistent
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_func` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1569](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1569) — **E_func arm.** A function violation among dedup entries is impossible in a non-anchored consistent

### `anchored_of_E_h` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_h` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1464](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1464) — **E_h arm.** A hash-capacity duplicate among dedup entries anchors the consistent log.
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_h` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1464](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1464) — **E_h arm.** A hash-capacity duplicate among dedup entries anchors the consistent log.

### `anchored_of_E_p` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1491](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1491) — **E_p arm.** A forward-permutation capacity duplicate anchors the consistent log.
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1491](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1491) — **E_p arm.** A forward-permutation capacity duplicate anchors the consistent log.

### `anchored_of_E_pinv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1530](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1530) — **E_pinv arm.** An inverse-permutation capacity duplicate (B1-repaired) anchors the log.
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1530](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1530) — **E_pinv arm.** An inverse-permutation capacity duplicate (B1-repaired) anchors the log.

### `anchored_of_hash_anchor` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_hash_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:299](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L299) — **The `E_hash` arm anchors a collision** (CO25 Eq. 24 over a certified consistent list): a hash entr
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_hash_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:299](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L299) — **The `E_hash` arm anchors a collision** (CO25 Eq. 24 over a certified consistent list): a hash entr

### `anchored_of_permInv_anchor` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_permInv_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:190](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L190) — **The `E_pinv` arm anchors a collision** (CO25 Eq. 26 over a certified consistent list): an inverse
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_permInv_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:190](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L190) — **The `E_pinv` arm anchors a collision** (CO25 Eq. 26 over a certified consistent list): an inverse

### `anchored_of_perm_anchor` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_perm_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:387](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L387) — **The `E_p` arm anchors a collision** (CO25 Eq. 25 over a certified consistent list): a forward entr
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_perm_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:387](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L387) — **The `E_p` arm anchors a collision** (CO25 Eq. 25 over a certified consistent list): a forward entr

### `appendStage1Bridge` (2 declarations, 2 files)

- `theorem Reduction.appendStage1Bridge` [ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean:99](../../../ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean#L99) — **The discharged `hStage1Bridge`.** The `Prod.fst`-marginal of the state-threaded phase-1 stage game
- `theorem Reduction.appendStage1Bridge` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean:64](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean#L64) — **Discharged `hStage1Bridge`.** The `Prod.fst`-marginal of the state-threaded phase-1 stage game (`a

### `appendStage2Bridge` (2 declarations, 2 files)

- `theorem Reduction.appendStage2Bridge` [ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean:127](../../../ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean#L127) — **The discharged `hStage2Bridge`.** For a phase-1 success `a` (with the completeness agreement `a.1.
- `theorem Reduction.appendStage2Bridge` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean:143](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean#L143) — **Discharged `hStage2Bridge`.** For each phase-1 success `a` with `goodOf rel₂ a` (which supplies th

### `appendStage₁_run_eq_liftM` (2 declarations, 2 files)

- `theorem Reduction.appendStage₁_run_eq_liftM` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean:171](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean#L171) — **The `OptionT.run` of the phase-1 stage body equals `liftM` of `R₁.run`'s `OptionT.run`.** `appendS
- `theorem Reduction.appendStage₁_run_eq_liftM` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges2.lean:145](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges2.lean#L145) — **The `OptionT.run` of the phase-1 stage body equals `liftM` of `R₁.run`'s `OptionT.run`.** `appendS

### `base_earlier_fwd_slots` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_fwd_slots` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1328](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1328) — **Slot-persistence (forward).** An earlier forward base entry's pair is cached in the later entry's
- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_fwd_slots` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1328](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1328) — **Slot-persistence (forward).** An earlier forward base entry's pair is cached in the later entry's

### `base_earlier_hash_slot` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_hash_slot` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1426](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1426) — **Slot-persistence (hash).**
- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_hash_slot` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1426](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1426) — **Slot-persistence (hash).**

### `base_earlier_inv_slots` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_inv_slots` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1390](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1390) — **Slot-persistence (inverse).**
- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_inv_slots` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1390](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1390) — **Slot-persistence (inverse).**

### `base_fwd_anchored` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_fwd_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1117](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1117) — **Forward-arm anchoring producer.** If a forward base entry `⟨inr (inl a), b⟩` has its answer capaci
- `theorem DuplexSpongeFS.EagerLazyDS.base_fwd_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1117](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1117) — **Forward-arm anchoring producer.** If a forward base entry `⟨inr (inl a), b⟩` has its answer capaci

### `base_hash_anchored` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_hash_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1240](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1240) — **Hash-arm anchoring producer.** A hash base entry whose answer is an existing slot anchors the cons
- `theorem DuplexSpongeFS.EagerLazyDS.base_hash_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1240](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1240) — **Hash-arm anchoring producer.** A hash base entry whose answer is an existing slot anchors the cons

### `base_inv_anchored` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_inv_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1152](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1152) — **Inverse-arm anchoring producer.** Symmetric to `base_fwd_anchored` for an inverse base entry `⟨inr
- `theorem DuplexSpongeFS.EagerLazyDS.base_inv_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1152](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1152) — **Inverse-arm anchoring producer.** Symmetric to `base_fwd_anchored` for an inverse base entry `⟨inr

### `base_no_earlier_sameClass` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_no_earlier_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1064](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1064) — **w1**: a base entry has no earlier same-class entry in its raw prefix. Directly from the first-occu
- `theorem DuplexSpongeFS.EagerLazyDS.base_no_earlier_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1064](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1064) — **w1**: a base entry has no earlier same-class entry in its raw prefix. Directly from the first-occu

### `base_raw_split` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_raw_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:905](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L905) — **Raw split at a base position.** For a base-trace index `j`, writing `pⱼ = f j` for the order embed
- `theorem DuplexSpongeFS.EagerLazyDS.base_raw_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:905](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L905) — **Raw split at a base position.** For a base-trace index `j`, writing `pⱼ = f j` for the order embed

### `cacheFold_hash_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.cacheFold_hash_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L148) — Every cached hash answer in a fold of `ℓ` over `c₀` either was in `c₀` or comes from a hash entry of
- `theorem DuplexSpongeFS.EagerLazyDS.cacheFold_hash_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L148) — Every cached hash answer in a fold of `ℓ` over `c₀` either was in `c₀` or comes from a hash entry of

### `cacheFold_pair_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.cacheFold_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:190](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L190) — Every cached permutation pair in a fold of `ℓ` over `c₀` either was in `c₀` or comes from a forward
- `theorem DuplexSpongeFS.EagerLazyDS.cacheFold_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:190](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L190) — Every cached permutation pair in a fold of `ℓ` over `c₀` either was in `c₀` or comes from a forward

### `card_capacityFiber_preimage` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.card_capacityFiber_preimage` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:139](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L139) — The capacity-fiber preimage count: exactly `\|W\| · \|U\|^R` states carry a capacity from `W`.
- `lemma DuplexSpongeFS.EagerLazyDS.card_capacityFiber_preimage` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:139](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L139) — The capacity-fiber preimage count: exactly `\|W\| · \|U\|^R` states carry a capacity from `W`.

### `card_le_of_unusedKeysList_eq_nil` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.card_le_of_unusedKeysList_eq_nil` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:229](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L229) — An exhausted keys pool forces the cache to cover the type.
- `lemma DuplexSpongeFS.EagerLazyDS.card_le_of_unusedKeysList_eq_nil` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:229](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L229) — An exhausted keys pool forces the cache to cover the type.

### `card_le_of_unusedValuesList_eq_nil` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.card_le_of_unusedValuesList_eq_nil` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:220](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L220) — An exhausted values pool forces the cache to cover the type.
- `lemma DuplexSpongeFS.EagerLazyDS.card_le_of_unusedValuesList_eq_nil` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:220](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L220) — An exhausted values pool forces the cache to cover the type.

### `card_listEval_eq_le` (2 declarations, 2 files)

- `theorem Whir302SZ.card_listEval_eq_le` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:64](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L64) — **The Schwartz–Zippel salvage bound for `listEval`** (the WHIR sumcheck flip event): if two coeffici
- `theorem Whir302SZ.card_listEval_eq_le` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:137](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L137) — **The Schwartz–Zippel salvage bound for `listEval`** (the WHIR sumcheck flip event): if two coeffici

### `choose_pow_le_qEntropy` (2 declarations, 2 files)

- `theorem CodingTheory.choose_pow_le_qEntropy` [ArkLib/Data/CodingTheory/EntropyVolumeUpper.lean:55](../../../ArkLib/Data/CodingTheory/EntropyVolumeUpper.lean#L55) — **Single-term q-ary entropy UPPER bound.**  For `2 ≤ q`, `0 < k`, `k < n`: `C(n,k) · (q-1)^k ≤ q^{n·
- `theorem CodingTheory.choose_pow_le_qEntropy` [ArkLib/Data/CodingTheory/EntropyVolumeUpperBound.lean:53](../../../ArkLib/Data/CodingTheory/EntropyVolumeUpperBound.lean#L53) — **Per-term `q`-ary entropy upper bound.** For `2 ≤ q`, `0 < k`, `k < n`, `C(n,k) · (q-1)^k ≤ q^{n ·

### `coeff_ehQ_eq_leading` (2 declarations, 2 files)

- `lemma MvPolynomial.coeff_ehQ_eq_leading` [ArkLib/ToMathlib/RestrictedSumset.lean:223](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L223) — The coefficient of the top monomial `X₀^{n-1} X₁^{n-2}` in `ehQ C'` (with `\|C'\| = 2(n-2)`) equals it
- `lemma MvPolynomial.coeff_ehQ_eq_leading` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:278](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L278) — `ehQ h Cset` differs from the leading part `vdmX h · y^{\|Cset\|}` by a polynomial of strictly smaller

### `coeff_zero_of_natDegree_lt` (2 declarations, 2 files)

- `lemma ProximityGap.coeff_zero_of_natDegree_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:694](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L694) — (no docstring)
- `lemma ProximityGap.coeff_zero_of_natDegree_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:31](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L31) — (no docstring)

### `collisionStep` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.collisionStep` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L52) — **The anchored per-step collision event**: the query was fresh (a genuine sample), and the sampled a
- `def DuplexSpongeFS.EagerLazyDS.collisionStep` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L52) — **The anchored per-step collision event**: the query was fresh (a genuine sample), and the sampled a

### `consistentFrom_eraseIdx_classRed` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_eraseIdx_classRed` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:527](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L527) — A class-redundant erasure preserves consistency in a consistent log.
- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_eraseIdx_classRed` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:527](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L527) — A class-redundant erasure preserves consistency in a consistent log.

### `consistentFrom_eraseIdx_of_noop` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_eraseIdx_of_noop` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:352](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L352) — Erasing a no-op entry preserves consistency.
- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_eraseIdx_of_noop` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:352](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L352) — Erasing a no-op entry preserves consistency.

### `consistentFrom_prefix_getElem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_prefix_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:44](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L44) — Consistency localizes: on a consistent log, entry `k` is consistent with the cache folded over the s
- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_prefix_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:44](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L44) — Consistency localizes: on a consistent log, entry `k` is consistent with the cache folded over the s

### `consistentFrom_removeRedundantEntryDSPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:548](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L548) — Consistency survives the full paper dedup pass.
- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:548](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L548) — Consistency survives the full paper dedup pass.

### `consistentFrom_split` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:820](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L820) — `ConsistentFrom` gives entry-consistency at every split point against the fold cache of the prefix.
- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:820](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L820) — `ConsistentFrom` gives entry-consistency at every split point against the fold cache of the prefix.

### `consistent_fwd_hit_pair_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistent_fwd_hit_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:757](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L757) — A consistent forward hit puts the entry's exact pair in the cache: if the running cache already hold
- `theorem DuplexSpongeFS.EagerLazyDS.consistent_fwd_hit_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:757](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L757) — A consistent forward hit puts the entry's exact pair in the cache: if the running cache already hold

### `consistent_inv_hit_pair_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistent_inv_hit_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:785](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L785) — A consistent inverse hit puts the entry's exact pair in the cache.
- `theorem DuplexSpongeFS.EagerLazyDS.consistent_inv_hit_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:785](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L785) — A consistent inverse hit puts the entry's exact pair in the cache.

### `decodeLT_ne_of_val_ne` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:87](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L87) — Distinct codewords decode to distinct polynomials: the decoded polynomial interpolates the codeword
- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:181](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L181) — Distinct smooth codewords decode to distinct univariate polynomials (the decoded polynomial interpol

### `div_card_pow_C_le_stepBound` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.div_card_pow_C_le_stepBound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:264](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L264) — The hash-arm arithmetic: `A / \|U\|^C ≤ stepBound` for `A ≤ 2m`.
- `lemma DuplexSpongeFS.EagerLazyDS.div_card_pow_C_le_stepBound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:264](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L264) — The hash-arm arithmetic: `A / \|U\|^C ≤ stepBound` for `A ≤ 2m`.

### `div_le_stepBound_of_le` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.div_le_stepBound_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L287) — The permutation-arm arithmetic: `A / len ≤ stepBound` for `A` below the numerator and `len` above th
- `lemma DuplexSpongeFS.EagerLazyDS.div_le_stepBound_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L287) — The permutation-arm arithmetic: `A / len ≤ stepBound` for `A` below the numerator and `len` above th

### `dsCacheSize_empty` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.dsCacheSize_empty` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:457](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L457) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.dsCacheSize_empty` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:457](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L457) — (no docstring)

### `dsfs_hLHS` (2 declarations, 2 files)

- `theorem Reduction.dsfs_hLHS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:197](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L197) — The annotated (assoc-routed) lift equals the direct lift, for every computation: the DS-hLHS. Induct
- `theorem Reduction.dsfs_hLHS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L202) — The annotated (assoc-routed) lift equals the direct lift, for every computation: the DS-hLHS. Induct

### `dsfs_hLHS₂` (2 declarations, 2 files)

- `theorem Reduction.dsfs_hLHS₂` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:256](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L256) — Annotated lift through `OptionT (OracleComp base)` (the third path) = direct lift.
- `theorem Reduction.dsfs_hLHS₂` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:261](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L261) — Annotated lift through `OptionT (OracleComp base)` (the third path) = direct lift.

### `dsfs_lift_query_bridge_inl` (2 declarations, 2 files)

- `theorem Reduction.dsfs_lift_query_bridge_inl` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:166](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L166) — Bridge: annotated vs direct lift of a single left-side query.
- `theorem Reduction.dsfs_lift_query_bridge_inl` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:171](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L171) — Bridge: annotated vs direct lift of a single left-side query.

### `dsfs_lift_query_bridge_inl₂` (2 declarations, 2 files)

- `theorem Reduction.dsfs_lift_query_bridge_inl₂` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:226](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L226) — Bridge: annotated vs direct lift of a single left-side query.
- `theorem Reduction.dsfs_lift_query_bridge_inl₂` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:232](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L232) — Bridge: annotated vs direct lift of a single left-side query.

### `dsfs_lift_query_bridge_inr` (2 declarations, 2 files)

- `theorem Reduction.dsfs_lift_query_bridge_inr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:65](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L65) — Bridge: annotated (assoc-routed) vs direct lift of a single right-side query.
- `theorem Reduction.dsfs_lift_query_bridge_inr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L70) — Bridge: annotated (assoc-routed) vs direct lift of a single right-side query.

### `ePaperReduction_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.ePaperReduction_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1609](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1609) — **`EPaperReduction` is a theorem.** A consistent log exhibiting the paper bad event `EPaper` is anch
- `theorem DuplexSpongeFS.EagerLazyDS.ePaperReduction_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1609](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1609) — **`EPaperReduction` is a theorem.** A consistent log exhibiting the paper bad event `EPaper` is anch

### `ePaper_of_answerCap_pair'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.ePaper_of_answerCap_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean#L52) — C1, unordered form: two first-of-mirror-class slots with distinct entries and equal answer-side capa
- `theorem DuplexSpongeFS.Paper.ePaper_of_answerCap_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean#L52) — C1, unordered form: two first-of-mirror-class slots with distinct entries and equal answer-side capa

### `ePaper_of_fwd_inv_pair'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.ePaper_of_fwd_inv_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean:119](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean#L119) — C1 finisher, forward-form previous step vs inverse-form current step (the CO25 5.12 case `ι > 0`): c
- `theorem DuplexSpongeFS.Paper.ePaper_of_fwd_inv_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean:119](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean#L119) — C1 finisher, forward-form previous step vs inverse-form current step (the CO25 5.12 case `ι > 0`): c

### `ePaper_of_hash_inv_pair'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.ePaper_of_hash_inv_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean:104](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean#L104) — C1 finisher, hash anchor vs inverse-form chain slot (the CO25 5.12 case `ι = 0`): equal answer capac
- `theorem DuplexSpongeFS.Paper.ePaper_of_hash_inv_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean:104](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean#L104) — C1 finisher, hash anchor vs inverse-form chain slot (the CO25 5.12 case `ι = 0`): equal answer capac

### `ePaper_of_jbt_inv_slot'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.ePaper_of_jbt_inv_slot'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:178](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L178) — **5.12 core**: a chain step whose `J_BT` slot carries the *inverse-form* entry fires `EPaper`. Downw
- `theorem DuplexSpongeFS.Paper.ePaper_of_jbt_inv_slot'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:178](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L178) — **5.12 core**: a chain step whose `J_BT` slot carries the *inverse-form* entry fires `EPaper`. Downw

### `e_fork_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.ForkCounter.e_fork_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:159](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L159) — The fork event fires: the family has two elements.
- `theorem DuplexSpongeFS.Sponge316.ForkCounter.e_fork_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:159](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L159) — The fork event fires: the family has two elements.

### `e_func_of_twoSurvivors_fwd_same_input` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.e_func_of_twoSurvivors_fwd_same_input` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:225](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L225) — **`Eprp`/`E_func` landing**: two guarded forward slots with the same input force the permutation-inc
- `lemma DuplexSpongeFS.Sponge316.e_func_of_twoSurvivors_fwd_same_input` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:225](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L225) — **`Eprp`/`E_func` landing**: two guarded forward slots with the same input force the permutation-inc

### `e_h_of_hasFirstHashPermCapNatPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_h_of_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:908](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L908) — **The hash-anchored keystone (paper semantics)**: a raw first-occurrence hash collision forces the p
- `theorem DuplexSpongeFS.Sponge316.e_h_of_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:908](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L908) — **The hash-anchored keystone (paper semantics)**: a raw first-occurrence hash collision forces the p

### `e_h_of_twoSurvivors_hash_hash` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.e_h_of_twoSurvivors_hash_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:256](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L256) — **`Efork,h` landing**: two guarded hash slots sharing the answer capacity force `capacitySegmentDupH
- `lemma DuplexSpongeFS.Sponge316.e_h_of_twoSurvivors_hash_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:256](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L256) — **`Efork,h` landing**: two guarded hash slots sharing the answer capacity force `capacitySegmentDupH

### `e_of_hasFirstCapBeforeInverseAnswerPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:277](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L277) — The inverse-anchored keystone, composed into the combined paper bad event `E`.
- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:277](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L277) — The inverse-anchored keystone, composed into the combined paper bad event `E`.

### `e_of_hasFirstHashPermCapNatPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:935](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L935) — The hash-anchored keystone composed into the combined paper bad event `E`.
- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:935](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L935) — The hash-anchored keystone composed into the combined paper bad event `E`.

### `e_of_hasFirstPermCapacityBeforeForwardOutputPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:639](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L639) — The reshaped keystone, composed into the combined paper bad event `E`.
- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:639](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L639) — The reshaped keystone, composed into the combined paper bad event `E`.

### `e_p_of_hasFirstPermCapacityBeforeForwardOutputPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_p_of_hasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:618](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L618) — **The reshaped keystone (paper semantics)**: a raw first-occurrence permutation-capacity collision f
- `theorem DuplexSpongeFS.Sponge316.e_p_of_hasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:618](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L618) — **The reshaped keystone (paper semantics)**: a raw first-occurrence permutation-capacity collision f

### `e_p_of_twoSurvivors_hash_fwd` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.e_p_of_twoSurvivors_hash_fwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:240](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L240) — **`Efork,h,p` landing (permutation-late order)**: a guarded hash slot before a guarded forward slot
- `lemma DuplexSpongeFS.Sponge316.e_p_of_twoSurvivors_hash_fwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:240](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L240) — **`Efork,h,p` landing (permutation-late order)**: a guarded hash slot before a guarded forward slot

### `e_pinv_of_hasFirstCapBeforeInverseAnswerPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_pinv_of_hasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:261](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L261) — **The inverse-anchored keystone (paper semantics)**: a raw first-occurrence inverse entry whose answ
- `theorem DuplexSpongeFS.Sponge316.e_pinv_of_hasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:261](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L261) — **The inverse-anchored keystone (paper semantics)**: a raw first-occurrence inverse entry whose answ

### `e_time_h_honest_raw_hasFirstHashPermCapNatPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:953](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L953) — Off the **paper** combined bad event, an honest hash-timing witness yields the direction-agnostic fi
- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:953](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L953) — Off the **paper** combined bad event, an honest hash-timing witness yields the direction-agnostic fi

### `e_time_p_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.TimePCounter.e_time_p_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:170](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L170) — The out-of-order-permutation event fires on the countermodel.
- `theorem DuplexSpongeFS.Sponge316.TimePCounter.e_time_p_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:170](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L170) — The out-of-order-permutation event fires on the countermodel.

### `ehQ` (2 declarations, 2 files)

- `def MvPolynomial.ehQ` [ArkLib/ToMathlib/RestrictedSumset.lean:218](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L218) — **The Erdős–Heilbronn polynomial** for a padded sumset `C'`.
- `def MvPolynomial.ehQ` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:273](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L273) — **The general Erdős–Heilbronn polynomial** for a padded sumset `C'`.

### `ehY` (2 declarations, 2 files)

- `def MvPolynomial.ehY` [ArkLib/ToMathlib/RestrictedSumset.lean:169](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L169) — Abbreviation for the "diagonal" variable `y = X₀ + X₁`.
- `def MvPolynomial.ehY` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:191](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L191) — The "diagonal" variable `y = ∑_k X k`.

### `entryConsistent` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.entryConsistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L67) — A log entry agrees with a cache: if its query is cached, the logged answer is the cached one.
- `def DuplexSpongeFS.EagerLazyDS.entryConsistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L67) — A log entry agrees with a cache: if its query is cached, the logged answer is the cached one.

### `entryFwdKey` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.entryFwdKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:348](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L348) — The forward key inserted by an entry (`none` for a hash entry).
- `def DuplexSpongeFS.EagerLazyDS.entryFwdKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:348](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L348) — The forward key inserted by an entry (`none` for a hash entry).

### `entryInvKey` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.entryInvKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:357](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L357) — The inverse key inserted by an entry (`none` for a hash entry). For a forward entry `⟨inr (inl a), b
- `def DuplexSpongeFS.EagerLazyDS.entryInvKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:357](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L357) — The inverse key inserted by an entry (`none` for a hash entry). For a forward entry `⟨inr (inl a), b

### `eval_ehQ_eq_zero` (2 declarations, 2 files)

- `lemma MvPolynomial.eval_ehQ_eq_zero` [ArkLib/ToMathlib/RestrictedSumset.lean:294](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L294) — `ehQ Cset` vanishes at every point `s : Fin 2 → F` whose two coordinates either coincide, or sum to
- `lemma MvPolynomial.eval_ehQ_eq_zero` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:335](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L335) — `ehQ h Cset` vanishes at every point `s : Fin h → F` whose coordinates are not all distinct, or whos

### `famC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TimePCounter.famC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:104](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L104) — The singleton backtrack family `{seqC}` (maximality is vacuous).
- `def DuplexSpongeFS.Sponge316.TimePCounter.famC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:104](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L104) — The singleton backtrack family `{seqC}` (maximality is vacuous).

### `famF` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.famF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:135](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L135) — The two-element backtrack family `{seqOne, seqTwo}`; maximality holds because neither chain's state
- `def DuplexSpongeFS.Sponge316.ForkCounter.famF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:135](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L135) — The two-element backtrack family `{seqOne, seqTwo}`; maximality holds because neither chain's state

### `finalCheckTight_perfectCompleteness` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.finalCheckTight_perfectCompleteness` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:299](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L299) — **The tight terminal completeness leaf `h₈`**: perfect completeness of the tight chain's zero-round
- `theorem Spartan.Spec.Bricks.finalCheckTight_perfectCompleteness` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:247](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L247) — **Completeness leaf for the tight terminal check** (#329, B7): `finalCheckTight` carries the conjoin

### `find` (4 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1097](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1097) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1105](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1105) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1097](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1097) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1105](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1105) — (no docstring)

### `finset_card_ge_of_pred_natCast_le_ennreal_lt` (2 declarations, 2 files)

- `lemma ProximityGap.finset_card_ge_of_pred_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:127](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L127) — (no docstring)
- `theorem ProximityGap.finset_card_ge_of_pred_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:131](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L131) — Convert an ENNReal lower bound on a finite set cardinality into a natural number weak cardinality bo

### `finset_card_gt_of_natCast_le_ennreal_lt` (2 declarations, 2 files)

- `lemma ProximityGap.finset_card_gt_of_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:120](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L120) — (no docstring)
- `theorem ProximityGap.finset_card_gt_of_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:120](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L120) — Convert an ENNReal lower bound on a finite set cardinality into a natural number strict cardinality

### `firstGuardD_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L118) — Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- `lemma DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L118) — Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.

### `firstGuard_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L69) — Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- `lemma DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L69) — Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.

### `firstHashPermNatPaper_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstHashPermNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:741](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L741) — **One-step preservation (paper)**: erasing one paper-redundant entry preserves the first-hash collis
- `lemma DuplexSpongeFS.Sponge316.firstHashPermNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:741](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L741) — **One-step preservation (paper)**: erasing one paper-redundant entry preserves the first-hash collis

### `firstHashPermNatPaper_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstHashPermNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:879](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L879) — **Fixpoint preservation (paper)**: dedup carries the first-hash collision shape to the broad base-tr
- `lemma DuplexSpongeFS.Sponge316.firstHashPermNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:879](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L879) — **Fixpoint preservation (paper)**: dedup carries the first-hash collision shape to the broad base-tr

### `firstInvNatPaper_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstInvNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:149](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L149) — **One-step preservation (paper semantics)**: erasing one paper-redundant entry preserves the first-o
- `lemma DuplexSpongeFS.Sponge316.firstInvNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:149](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L149) — **One-step preservation (paper semantics)**: erasing one paper-redundant entry preserves the first-o

### `firstInvNatPaper_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstInvNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L234) — **Fixpoint preservation (paper semantics)**: dedup preserves the inverse-anchored shape.
- `lemma DuplexSpongeFS.Sponge316.firstInvNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L234) — **Fixpoint preservation (paper semantics)**: dedup preserves the inverse-anchored shape.

### `firstOfClassAt_of_noRedundant` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.firstOfClassAt_of_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L53) — **Certificate freshness**: the dedup's `NoRedundantEntryDSPaper` certificate gives first-of-class at
- `theorem DuplexSpongeFS.EagerLazyDS.firstOfClassAt_of_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L53) — **Certificate freshness**: the dedup's `NoRedundantEntryDSPaper` certificate gives first-of-class at

### `firstOfClassAt_of_perm_index'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.firstOfClassAt_of_perm_index'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean#L67) — **Index bridge**: a nonterminal `BacktrackSequence.Index` permutation slot is a first-of-mirror-clas
- `theorem DuplexSpongeFS.Paper.firstOfClassAt_of_perm_index'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean#L67) — **Index bridge**: a nonterminal `BacktrackSequence.Index` permutation slot is a first-of-mirror-clas

### `firstPermNatPaper_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:404](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L404) — **One-step preservation (paper semantics)**: erasing one paper-redundant entry preserves the first-p
- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:404](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L404) — **One-step preservation (paper semantics)**: erasing one paper-redundant entry preserves the first-p

### `firstPermNatPaper_of_first` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:346](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L346) — Convert the public finite-index paper witness into the natural-index form.
- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:346](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L346) — Convert the public finite-index paper witness into the natural-index form.

### `firstPermNatPaper_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:582](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L582) — **Fixpoint preservation (paper semantics)**: dedup preserves the first-perm collision shape as the b
- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:582](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L582) — **Fixpoint preservation (paper semantics)**: dedup preserves the first-perm collision shape as the b

### `firstSumcheck_rbrKnowledgeSoundness_honest` (2 declarations, 2 files)

- `theorem Spartan.Spec.firstSumcheck_rbrKnowledgeSoundness_honest` [ArkLib/ProofSystem/Spartan/FirstSumcheckComplete.lean:202](../../../ArkLib/ProofSystem/Spartan/FirstSumcheckComplete.lean#L202) — **First sum-check phase round-by-round knowledge soundness (issue #114).** The Spartan lift of the g
- `theorem Spartan.Spec.firstSumcheck_rbrKnowledgeSoundness_honest` [ArkLib/ProofSystem/Spartan/SumcheckKnowledgeLeaves.lean:82](../../../ArkLib/ProofSystem/Spartan/SumcheckKnowledgeLeaves.lean#L82) — The first Spartan sum-check RBR-KS leaf over the honest transported relation contract, reduced to th

### `foldl_hash_provenance` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_hash_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1205](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1205) — **Hash-cache provenance (whole fold).**
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_hash_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1205](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1205) — **Hash-cache provenance (whole fold).**

### `foldl_pair_provenance` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_pair_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:740](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L740) — **Pair provenance (whole fold)**: a pair in the final cache was in the start cache or inserted by so
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_pair_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:740](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L740) — **Pair provenance (whole fold)**: a pair in the final cache was in the start cache or inserted by so

### `foldl_stepCache_fwdNodup` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_fwdNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:702](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L702) — Forward-key distinctness is preserved along a whole non-anchored fold.
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_fwdNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:702](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L702) — Forward-key distinctness is preserved along a whole non-anchored fold.

### `foldl_stepCache_hash_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_hash_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1369](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1369) — The hash cache only grows along the whole fold.
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_hash_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1369](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1369) — The hash cache only grows along the whole fold.

### `foldl_stepCache_pair_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_pair_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:102](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L102) — Permutation pairs persist through any fold suffix.
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_pair_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:102](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L102) — Permutation pairs persist through any fold suffix.

### `foldl_stepCache_perm_sublist` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_perm_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:329](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L329) — The permutation cache only grows along the whole fold.
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_perm_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:329](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L329) — The permutation cache only grows along the whole fold.

### `foldl_stepCache_take_from_getElem` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.foldl_stepCache_take_from_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:408](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L408) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.foldl_stepCache_take_from_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:408](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L408) — (no docstring)

### `foldl_take_succ_eq` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_take_succ_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L90) — Folding one more prefix entry is one `stepCache` step.
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_take_succ_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L90) — Folding one more prefix entry is one `stepCache` step.

### `for` (2 declarations, 2 files)

- `theorem for` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessProof.lean:14](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessProof.lean#L14) — (no docstring)
- `theorem for` [ArkLib/ProofSystem/Logup/Security/Soundness.lean:46](../../../ArkLib/ProofSystem/Logup/Security/Soundness.lean#L46) — (no docstring)

### `forwardEntryC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.forwardEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L58) — (no docstring)
- `def DuplexSpongeFS.Sponge316.forwardEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L58) — (no docstring)

### `forwardEntryD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.forwardEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L54) — (no docstring)
- `def DuplexSpongeFS.Sponge316.forwardEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L54) — (no docstring)

### `forwardEntryP` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.forwardEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:245](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L245) — (no docstring)
- `def DuplexSpongeFS.Sponge316.forwardEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:245](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L245) — (no docstring)

### `fresh_at_firstOfClass_hash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:61](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L61) — **Freshness (hash case)**: at a class-first slot holding a hash entry, the hash cache misses.
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:61](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L61) — **Freshness (hash case)**: at a class-first slot holding a hash entry, the hash cache misses.

### `fresh_at_firstOfClass_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L90) — **Freshness (forward case)**: at a class-first slot holding a forward permutation entry, the pair ca
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L90) — **Freshness (forward case)**: at a class-first slot holding a forward permutation entry, the pair ca

### `fresh_at_firstOfClass_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:132](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L132) — **Freshness (inverse case)**: at a class-first slot holding an inverse permutation entry, the pair c
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:132](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L132) — **Freshness (inverse case)**: at a class-first slot holding an inverse permutation entry, the pair c

### `fresh_fwd_inserts` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_fwd_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1272](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1272) — A fresh forward entry's pair ends up in the final fold cache.
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_fwd_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1272](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1272) — A fresh forward entry's pair ends up in the final fold cache.

### `fresh_hash_inserts` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_hash_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1377](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1377) — A fresh hash entry's answer ends up cached in the final fold.
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_hash_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1377](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1377) — A fresh hash entry's answer ends up cached in the final fold.

### `fresh_inv_inserts` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_inv_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1287) — A fresh inverse entry's pair ends up in the final fold cache.
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_inv_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1287) — A fresh inverse entry's pair ends up in the final fold cache.

### `fwdInState` (2 declarations, 2 files)

- `def DuplexSpongeFS.Paper.fwdInState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L58) — Query-state extractor for forward-permutation entries (avoids the dependent-`Sigma` `HEq` when compa
- `def DuplexSpongeFS.Paper.fwdInState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L58) — Query-state extractor for forward-permutation entries (avoids the dependent-`Sigma` `HEq` when compa

### `fwdInStateD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.fwdInStateD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:272](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L272) — Query-state extractor for forward-permutation entries.
- `def DuplexSpongeFS.Sponge316.fwdInStateD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:272](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L272) — Query-state extractor for forward-permutation entries.

### `fwdOutState` (2 declarations, 2 files)

- `def DuplexSpongeFS.Paper.fwdOutState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:65](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L65) — Answer-state extractor for forward-permutation entries.
- `def DuplexSpongeFS.Paper.fwdOutState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:65](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L65) — Answer-state extractor for forward-permutation entries.

### `fwdOutStateD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.fwdOutStateD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:279](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L279) — Answer-state extractor for forward-permutation entries.
- `def DuplexSpongeFS.Sponge316.fwdOutStateD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:279](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L279) — Answer-state extractor for forward-permutation entries.

### `fwd_entry_fresh` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fwd_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:861](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L861) — **A non-redundant forward entry is fresh.** If `⟨inr (inl a), b⟩` occurs in a consistent log with no
- `theorem DuplexSpongeFS.EagerLazyDS.fwd_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:861](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L861) — **A non-redundant forward entry is fresh.** If `⟨inr (inl a), b⟩` occurs in a consistent log with no

### `fwd_fresh_cap_new` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fwd_fresh_cap_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:552](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L552) — A fresh forward step that is not an anchored collision yields an answer capacity that is neither an
- `theorem DuplexSpongeFS.EagerLazyDS.fwd_fresh_cap_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:552](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L552) — A fresh forward step that is not an anchored collision yields an answer capacity that is neither an

### `fwd_hit_sameClass_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fwd_hit_sameClass_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:773](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L773) — **Piece (A2c)**: in a fold from empty over `L`, a consistent forward entry `⟨inr (inl a), b⟩` whose
- `theorem DuplexSpongeFS.EagerLazyDS.fwd_hit_sameClass_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:773](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L773) — **Piece (A2c)**: in a fold from empty over `L`, a consistent forward entry `⟨inr (inl a), b⟩` whose

### `game_apply_eq` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge314.K1.game_apply_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:83](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L83) — For every sampled carrier `c`, the logged eager game on `P` is deterministic: it returns the inverse
- `lemma DuplexSpongeFS.Sponge314.K1.game_apply_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:83](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L83) — For every sampled carrier `c`, the logged eager game on `P` is deterministic: it returns the inverse

### `game_eq` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge314.K1.game_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:92](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L92) — The full game equals sampling a carrier and returning the deterministic logged output.
- `lemma DuplexSpongeFS.Sponge314.K1.game_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:92](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L92) — The full game equals sampling a carrier and returning the deterministic logged output.

### `getElem_idx_congr` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L49) — Transport a `List.getElem` along a `Nat` index equality.
- `lemma DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L49) — Transport a `List.getElem` along a `Nat` index equality.

### `getElem_idx_congrD` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L286) — Transport a `List.getElem` along a `Nat` index equality.
- `lemma DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L286) — Transport a `List.getElem` along a `Nat` index equality.

### `getElem_list_congr` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L53) — Transport a `List.getElem` along a list equality.
- `lemma DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L53) — Transport a `List.getElem` along a list equality.

### `getElem_list_congrD` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L292) — Transport a `List.getElem` along a list equality.
- `lemma DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L292) — Transport a `List.getElem` along a list equality.

### `getElem_mem_take` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.getElem_mem_take` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:896](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L896) — An earlier-indexed element lies in the prefix `take p`.
- `theorem DuplexSpongeFS.EagerLazyDS.getElem_mem_take` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:896](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L896) — An earlier-indexed element lies in the prefix `take p`.

### `hasCapBeforeInverseAnswerPaper_of_first` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasCapBeforeInverseAnswerPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:136](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L136) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.hasCapBeforeInverseAnswerPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:136](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L136) — (no docstring)

### `hasFirstHashFwdCapNat_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:97](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L97) — **One-step preservation**: erasing one redundant entry preserves `HasFirstHashFwdCapNat`.
- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:97](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L97) — **One-step preservation**: erasing one redundant entry preserves `HasFirstHashFwdCapNat`.

### `hasFirstHashFwdCapNat_of_first` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L68) — The `Fin`-indexed first-occurrence shape implies the ℕ-indexed one.
- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L68) — The `Fin`-indexed first-occurrence shape implies the ℕ-indexed one.

### `hasFirstHashFwdCapNat_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:194](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L194) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves `HasFirstHashFwdCa
- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:194](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L194) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves `HasFirstHashFwdCa

### `hasFirstPermCapacityBeforeForwardOutputPaper_current_not_redundant` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasFirstPermCapacityBeforeForwardOutputPaper_current_not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:315](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L315) — The paper first-occurrence collision shape carries the nonredundancy proof for its forward anchor.
- `theorem DuplexSpongeFS.Sponge316.hasFirstPermCapacityBeforeForwardOutputPaper_current_not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:315](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L315) — The paper first-occurrence collision shape carries the nonredundancy proof for its forward anchor.

### `hasForwardCapacityBeforeHash_of_nat` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_of_nat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L85) — The ℕ-indexed shape implies the plain (`Fin`-indexed, no firstness) collision shape.
- `lemma DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_of_nat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L85) — The ℕ-indexed shape implies the plain (`Fin`-indexed, no firstness) collision shape.

### `hasFwdKey` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.hasFwdKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:340](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L340) — Whether a permutation cache already holds the forward key `a`.
- `def DuplexSpongeFS.EagerLazyDS.hasFwdKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:340](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L340) — Whether a permutation cache already holds the forward key `a`.

### `hasFwdKey_foldl_imp` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hasFwdKey_foldl_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:436](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L436) — A forward key present after the whole fold was either present at the start or inserted by some entry
- `theorem DuplexSpongeFS.EagerLazyDS.hasFwdKey_foldl_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:436](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L436) — A forward key present after the whole fold was either present at the start or inserted by some entry

### `hasFwdKey_stepCache_imp` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hasFwdKey_stepCache_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:400](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L400) — One fold step can only create the forward key it inserts: if a key is present after the step but not
- `theorem DuplexSpongeFS.EagerLazyDS.hasFwdKey_stepCache_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:400](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L400) — One fold step can only create the forward key it inserts: if a key is present after the step but not

### `hasHashEntry_eraseIdxPaper` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_eraseIdxPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:162](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L162) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_eraseIdxPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:162](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L162) — (no docstring)

### `hasHashEntry_removeRedundantPaper` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L203) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L203) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr

### `hasHashEntry_removeRedundantPaper_of_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:227](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L227) — Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
- `theorem DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:227](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L227) — Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica

### `hasHashPermCapBeforeHashPaper_of_nat` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasHashPermCapBeforeHashPaper_of_nat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:728](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L728) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.hasHashPermCapBeforeHashPaper_of_nat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:728](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L728) — (no docstring)

### `hasInvKey` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.hasInvKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:344](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L344) — Whether a permutation cache already holds the inverse key `b`.
- `def DuplexSpongeFS.EagerLazyDS.hasInvKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:344](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L344) — Whether a permutation cache already holds the inverse key `b`.

### `hasInvKey_foldl_imp` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hasInvKey_foldl_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:451](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L451) — An inverse key present after the whole fold was present at the start or inserted by some entry of th
- `theorem DuplexSpongeFS.EagerLazyDS.hasInvKey_foldl_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:451](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L451) — An inverse key present after the whole fold was present at the start or inserted by some entry of th

### `hasInvKey_stepCache_imp` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hasInvKey_stepCache_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:363](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L363) — One fold step can only create the inverse key it inserts (sound direction only).
- `theorem DuplexSpongeFS.EagerLazyDS.hasInvKey_stepCache_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:363](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L363) — One fold step can only create the inverse key it inserts (sound direction only).

### `hasPermCapacityBeforeForwardOutputPaper_of_first` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L287) — Forgetting the first-occurrence guard leaves the broad paper shape.
- `theorem DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L287) — Forgetting the first-occurrence guard leaves the broad paper shape.

### `hasPermCapacityBeforeForwardOutputPaper_of_firstPermNat` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_of_firstPermNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:384](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L384) — Convert the natural-index witness back to the broad paper shape.
- `lemma DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_of_firstPermNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:384](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L384) — Convert the natural-index witness back to the broad paper shape.

### `hasPermCapacityBeforeForwardOutputPaper_removeRedundant_of_first` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_removeRedundant_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:608](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L608) — **Public dedup bridge (paper semantics)**: a raw first-occurrence perm-capacity collision survives `
- `theorem DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_removeRedundant_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:608](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L608) — **Public dedup bridge (paper semantics)**: a raw first-occurrence perm-capacity collision survives `

### `hashEntryC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.hashEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L54) — (no docstring)
- `def DuplexSpongeFS.Sponge316.hashEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L54) — (no docstring)

### `hashEntryD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.hashEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:50](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L50) — (no docstring)
- `def DuplexSpongeFS.Sponge316.hashEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:50](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L50) — (no docstring)

### `hashEntryP` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.hashEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:241](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L241) — (no docstring)
- `def DuplexSpongeFS.Sponge316.hashEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:241](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L241) — (no docstring)

### `hashKey_isSome_foldl_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hashKey_isSome_foldl_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:333](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L333) — A cached hash key stays cached through any fold suffix (`isSome` form).
- `theorem DuplexSpongeFS.EagerLazyDS.hashKey_isSome_foldl_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:333](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L333) — A cached hash key stays cached through any fold suffix (`isSome` form).

### `hashRecord_cached_after_consistent` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hashRecord_cached_after_consistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:283](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L283) — After a consistent hash step, the exact logged hash answer is cached.
- `theorem DuplexSpongeFS.EagerLazyDS.hashRecord_cached_after_consistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:283](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L283) — After a consistent hash step, the exact logged hash answer is cached.

### `hashRecord_take_of_le` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hashRecord_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:162](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L162) — A hash record at the `(j'+1)`-prefix fold persists (with its value) to any larger prefix.
- `theorem DuplexSpongeFS.EagerLazyDS.hashRecord_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:162](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L162) — A hash record at the `(j'+1)`-prefix fold persists (with its value) to any larger prefix.

### `hash_anchor_unique` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.hash_anchor_unique` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:156](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L156) — **U2 (anchor uniqueness, paper event)**: off `EPaper`, two hash anchors with equal answer capacities
- `theorem DuplexSpongeFS.Paper.hash_anchor_unique` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:156](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L156) — **U2 (anchor uniqueness, paper event)**: off `EPaper`, two hash anchors with equal answer capacities

### `hash_anchor_unique_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hash_anchor_unique_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:473](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L473) — Off `BadEventDSPaper.E`, two hash anchors with equal answer capacities carry the same statement.
- `theorem DuplexSpongeFS.Sponge316.hash_anchor_unique_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:473](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L473) — Off `BadEventDSPaper.E`, two hash anchors with equal answer capacities carry the same statement.

### `hash_entry_fresh` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hash_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1221](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1221) — **A non-redundant hash entry is fresh.** A consistent hash hit forces the cached answer to equal the
- `theorem DuplexSpongeFS.EagerLazyDS.hash_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1221](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1221) — **A non-redundant hash entry is fresh.** A consistent hash hit forces the cached answer to equal the

### `hash_fresh_ans_new` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hash_fresh_ans_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:574](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L574) — A fresh hash step that is not an anchored collision yields an answer that is not an existing slot.
- `theorem DuplexSpongeFS.EagerLazyDS.hash_fresh_ans_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:574](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L574) — A fresh hash step that is not an anchored collision yields an answer that is not an existing slot.

### `hash_step_separation` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.hash_step_separation` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L122) — **U3 (anchor separation, paper event)**: off `EPaper`, no chain-step output capacity equals a hash-a
- `theorem DuplexSpongeFS.Paper.hash_step_separation` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L122) — **U3 (anchor separation, paper event)**: off `EPaper`, no chain-step output capacity equals a hash-a

### `hash_step_separation_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hash_step_separation_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:388](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L388) — Off `BadEventDSPaper.E`, a hash anchor capacity cannot occur as the answer capacity of a family chai
- `theorem DuplexSpongeFS.Sponge316.hash_step_separation_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:388](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L388) — Off `BadEventDSPaper.E`, a hash anchor capacity cannot occur as the answer capacity of a family chai

### `head_some` (2 declarations, 2 files)

- `lemma CheckClaim.head_some` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:76](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L76) — A simulated `some`-wrapped computation only outputs `some`.
- `lemma CheckClaim.head_some` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:84](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L84) — A simulated `some`-wrapped computation only outputs `some`.

### `honestBad_birthday_unconditional` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.BirthdayBoundPaper.honestBad_birthday_unconditional` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean#L52) — **The §5.6 → §5.8 channel, unconditional**: the honest bad events of the eager `D_𝔖`-carrier game ob
- `theorem DuplexSpongeFS.BirthdayBoundPaper.honestBad_birthday_unconditional` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean#L52) — **The §5.6 → §5.8 channel, unconditional**: the honest bad events of the eager `D_𝔖`-carrier game ob

### `honestBad_claim5_21Bound_unconditional` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.BirthdayBoundPaper.honestBad_claim5_21Bound_unconditional` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean#L68) — **Claim 5.21, unconditional**: at the CO25 trace length `T = tₕ + 1 + tₚ + L + tₚᵢ`, the honest bad
- `theorem DuplexSpongeFS.BirthdayBoundPaper.honestBad_claim5_21Bound_unconditional` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean#L68) — **Claim 5.21, unconditional**: at the CO25 trace length `T = tₕ + 1 + tₚ + L + tₚᵢ`, the honest bad

### `index_entry_forward_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.index_entry_forward_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:291](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L291) — **The cascade (the mathematical core of CO25 Lemmas 5.12/5.16)**: off the combined paper bad event,
- `theorem DuplexSpongeFS.Sponge316.index_entry_forward_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:291](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L291) — **The cascade (the mathematical core of CO25 Lemmas 5.12/5.16)**: off the combined paper bad event,

### `index_step1` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.index_step1` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:130](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L130) — The chain index of step 1 (pair `(sA, sB)`) is the raw slot `3`.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.index_step1` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:130](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L130) — The chain index of step 1 (pair `(sA, sB)`) is the raw slot `3`.

### `index_step2` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.index_step2` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:150](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L150) — The chain index of step 2 (pair `(sa, sb)`) is the raw slot `1`.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.index_step2` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:150](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L150) — The chain index of step 2 (pair `(sa, sb)`) is the raw slot `1`.

### `inv_entry_fresh` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.inv_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:874](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L874) — **A non-redundant inverse entry is fresh.**
- `theorem DuplexSpongeFS.EagerLazyDS.inv_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:874](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L874) — **A non-redundant inverse entry is fresh.**

### `inv_fresh_cap_new` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.inv_fresh_cap_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:563](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L563) — A fresh inverse step that is not an anchored collision yields an answer capacity that is neither an
- `theorem DuplexSpongeFS.EagerLazyDS.inv_fresh_cap_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:563](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L563) — A fresh inverse step that is not an anchored collision yields an answer capacity that is neither an

### `inv_hit_sameClass_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.inv_hit_sameClass_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:800](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L800) — **Piece (A2c), inverse arm**: in a fold from empty over `L`, a consistent inverse entry `⟨inr (inr b
- `theorem DuplexSpongeFS.EagerLazyDS.inv_hit_sameClass_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:800](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L800) — **Piece (A2c), inverse arm**: in a fold from empty over `L`, a consistent inverse entry `⟨inr (inr b

### `inverseEntryC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.inverseEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:62](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L62) — (no docstring)
- `def DuplexSpongeFS.Sponge316.inverseEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:62](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L62) — (no docstring)

### `inverseEntryD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.inverseEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L58) — (no docstring)
- `def DuplexSpongeFS.Sponge316.inverseEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L58) — (no docstring)

### `inverseEntryP` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.inverseEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:249](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L249) — (no docstring)
- `def DuplexSpongeFS.Sponge316.inverseEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:249](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L249) — (no docstring)

### `isTotalQueryBound_P` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge314.K1.isTotalQueryBound_P` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L77) — `P` makes exactly one query.
- `lemma DuplexSpongeFS.Sponge314.K1.isTotalQueryBound_P` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L77) — `P` makes exactly one query.

### `jbt_hash_firstOfClassAt''` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_hash_firstOfClassAt''` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:158](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L158) — **Bridge**: the `J_BT` hash slot is first-of-mirror-class (hash entries are self-mirrors).
- `theorem DuplexSpongeFS.Paper.jbt_hash_firstOfClassAt''` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:158](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L158) — **Bridge**: the `J_BT` hash slot is first-of-mirror-class (hash entries are self-mirrors).

### `jbt_hash_getElem''` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_hash_getElem''` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:140](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L140) — The `J_BT` hash slot carries the hash anchor (Fin-getElem normal form).
- `theorem DuplexSpongeFS.Paper.jbt_hash_getElem''` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:140](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L140) — The `J_BT` hash slot carries the hash anchor (Fin-getElem normal form).

### `jbt_perm_getElem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_perm_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:61](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L61) — Unconditional either-direction payload of a nonterminal `J_BT` permutation index (local copy of the
- `theorem DuplexSpongeFS.Paper.jbt_perm_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:61](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L61) — Unconditional either-direction payload of a nonterminal `J_BT` permutation index (local copy of the

### `jbt_perm_slot_cases'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_cases'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L99) — The raw-trace entry at a nonterminal `J_BT` permutation index is the forward or the inverse form of
- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_cases'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L99) — The raw-trace entry at a nonterminal `J_BT` permutation index is the forward or the inverse form of

### `jbt_perm_slot_firstOfClassAt'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_firstOfClassAt'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L122) — **Bridge**: a nonterminal `J_BT` permutation slot is first-of-mirror-class (`M2Engine.FirstOfClassAt
- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_firstOfClassAt'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L122) — **Bridge**: a nonterminal `J_BT` permutation slot is first-of-mirror-class (`M2Engine.FirstOfClassAt

### `jbt_perm_slot_lt'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_lt'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L85) — A nonterminal `J_BT` permutation index is a genuine raw-trace index.
- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_lt'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L85) — A nonterminal `J_BT` permutation index is a genuine raw-trace index.

### `key_cached_after_step_hash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:213](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L213) — After folding any entry, that entry's key is cached (fresh ⟹ created; hit ⟹ was there). The work-ord
- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:213](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L213) — After folding any entry, that entry's key is cached (fresh ⟹ created; hit ⟹ was there). The work-ord

### `key_cached_after_step_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:221](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L221) — After folding a forward entry, its forward key is cached.
- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:221](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L221) — After folding a forward entry, its forward key is cached.

### `key_cached_after_step_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:232](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L232) — After folding an inverse entry, its value key is cached.
- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:232](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L232) — After folding an inverse entry, its value key is cached.

### `lazyDSImplFlagged` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L68) — The ghost-flagged lazy combined oracle: run `lazyDSImpl` verbatim and accumulate, as a `Prop` state
- `def DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L68) — The ghost-flagged lazy combined oracle: run `lazyDSImpl` verbatim and accumulate, as a `Prop` state

### `lazyDSImplFlagged_flag_monotone` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_flag_monotone` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:125](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L125) — The flag is sticky: once set, every reachable successor state keeps it.
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_flag_monotone` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:125](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L125) — The flag is sticky: once set, every reachable successor state keeps it.

### `lazyDSImplFlagged_run` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_run` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L77) — Single-step exposure of the flagged oracle (public; the defeq `show` does not transport across files
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_run` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L77) — Single-step exposure of the flagged oracle (public; the defeq `show` does not transport across files

### `lazyDSImplFlagged_step_bad` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_bad` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L300) — **The engine's `hstep_bad`**: from an unflagged state with cache size `m`, one step flags with proba
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_bad` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L300) — **The engine's `hstep_bad`**: from an unflagged state with cache size `m`, one step flags with proba

### `lazyDSImplFlagged_step_size` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_size` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L114) — The engine's `hstep_size` for the flagged carrier: the cache component grows by at most one per step
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_size` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L114) — The engine's `hstep_size` for the flagged carrier: the cache component grows by at most one per step

### `lazyDSImplFlagged_step_support` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_support` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L84) — **The per-step support facts**: each reachable one-step outcome of the flagged oracle has the folded
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_support` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L84) — **The per-step support facts**: each reachable one-step outcome of the flagged oracle has the folded

### `lazyDSImpl_run_map_flagged` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImpl_run_map_flagged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L85) — **The forgetting bridge**: the plain lazy run is the state projection of the flagged run — the ghost
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImpl_run_map_flagged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L85) — **The forgetting bridge**: the plain lazy run is the state projection of the flagged run — the ghost

### `le_length_unusedKeysList` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.le_length_unusedKeysList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L202) — The unused-keys pool keeps at least `\|X\| - \|cache\|` elements.
- `lemma DuplexSpongeFS.EagerLazyDS.le_length_unusedKeysList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L202) — The unused-keys pool keeps at least `\|X\| - \|cache\|` elements.

### `le_length_unusedValuesList` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.le_length_unusedValuesList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L184) — The unused-values pool keeps at least `\|X\| - \|cache\|` elements.
- `lemma DuplexSpongeFS.EagerLazyDS.le_length_unusedValuesList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L184) — The unused-values pool keeps at least `\|X\| - \|cache\|` elements.

### `lemma512Paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.lemma512Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean:137](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean#L137) — **CO25 Lemma 5.12 (paper event)**: off the paper-faithful bad event `EPaper`, no BackTrack chain ste
- `theorem DuplexSpongeFS.Paper.lemma512Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean:137](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean#L137) — **CO25 Lemma 5.12 (paper event)**: off the paper-faithful bad event `EPaper`, no BackTrack chain ste

### `lemma514Paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.lemma514Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:275](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L275) — **CO25 Lemma 5.14 over the paper event** (M2b, Def-5.5/Eq-26-faithful): off `EPaper` the backtrack f
- `theorem DuplexSpongeFS.Paper.lemma514Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:275](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L275) — **CO25 Lemma 5.14 over the paper event** (M2b, Def-5.5/Eq-26-faithful): off `EPaper` the backtrack f

### `lemma516HashPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.lemma516HashPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:260](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L260) — **Lemma 5.16, hash half (paper event)**: off `EPaper`, the anchoring hash query does not appear afte
- `theorem DuplexSpongeFS.Paper.lemma516HashPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:260](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L260) — **Lemma 5.16, hash half (paper event)**: off `EPaper`, the anchoring hash query does not appear afte

### `lemma516Paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.lemma516Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:351](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L351) — **CO25 Lemma 5.16 over the paper bad event**: off `EPaper`, all BackTrack chain queries appear in tr
- `theorem DuplexSpongeFS.Paper.lemma516Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:351](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L351) — **CO25 Lemma 5.16 over the paper bad event**: off `EPaper`, all BackTrack chain queries appear in tr

### `lemma516TimePPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.lemma516TimePPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:295](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L295) — **Lemma 5.16, permutation half (paper event)**: off `EPaper`, no chain permutation query appears in
- `theorem DuplexSpongeFS.Paper.lemma516TimePPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:295](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L295) — **Lemma 5.16, permutation half (paper event)**: off `EPaper`, no chain permutation query appears in

### `lemma58StepBound` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.lemma58StepBound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:243](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L243) — The per-step bad probability: `(2m+1)·\|U\|^R / (\|U\|^N − m)` from cache size `m` — the union bound ove
- `def DuplexSpongeFS.EagerLazyDS.lemma58StepBound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:243](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L243) — The per-step bad probability: `(2m+1)·\|U\|^R / (\|U\|^N − m)` from cache size `m` — the union bound ove

### `lemma58StepBound_monotone` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.lemma58StepBound_monotone` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L248) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.lemma58StepBound_monotone` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L248) — (no docstring)

### `lemma58_num_ne_zero` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.lemma58_num_ne_zero` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:257](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L257) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.lemma58_num_ne_zero` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:257](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L257) — (no docstring)

### `lemma5_12HonestResidualPaper_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_12HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:441](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L441) — The residual `Lemma5_12HonestResidualPaper`, discharged.
- `theorem DuplexSpongeFS.Sponge316.lemma5_12HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:441](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L441) — The residual `Lemma5_12HonestResidualPaper`, discharged.

### `lemma5_12_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_12_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:425](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L425) — **CO25 Lemma 5.12, paper semantics — DISCHARGED**: off the paper combined bad event, no BackTrack ch
- `theorem DuplexSpongeFS.Sponge316.lemma5_12_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:425](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L425) — **CO25 Lemma 5.12, paper semantics — DISCHARGED**: off the paper combined bad event, no BackTrack ch

### `lemma5_14HonestFalseStatement_false` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.ForkCounter.lemma5_14HonestFalseStatement_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:594](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L594) — **The in-tree `Lemma5_14HonestFalseStatement` is FALSE** (at `StmtIn := Unit`, `U := UInt8`, sponge
- `theorem DuplexSpongeFS.Sponge316.ForkCounter.lemma5_14HonestFalseStatement_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:594](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L594) — **The in-tree `Lemma5_14HonestFalseStatement` is FALSE** (at `StmtIn := Unit`, `U := UInt8`, sponge

### `lemma5_14HonestResidualPaper_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_14HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:705](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L705) — The residual `Lemma5_14HonestResidualPaper`, discharged.
- `theorem DuplexSpongeFS.Sponge316.lemma5_14HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:705](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L705) — The residual `Lemma5_14HonestResidualPaper`, discharged.

### `lemma5_14_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_14_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:629](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L629) — **CO25 Lemma 5.14, paper semantics — DISCHARGED**: off `BadEventDSPaper.E`, the backtrack family has
- `theorem DuplexSpongeFS.Sponge316.lemma5_14_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:629](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L629) — **CO25 Lemma 5.14, paper semantics — DISCHARGED**: off `BadEventDSPaper.E`, the backtrack family has

### `lemma5_16HonestFalseAsStated_false` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.TimePCounter.lemma5_16HonestFalseAsStated_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:502](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L502) — **The in-tree `Lemma5_16HonestFalseAsStated` is FALSE** (at `StmtIn := Unit`, `U := UInt8`, sponge w
- `theorem DuplexSpongeFS.Sponge316.TimePCounter.lemma5_16HonestFalseAsStated_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:502](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L502) — **The in-tree `Lemma5_16HonestFalseAsStated` is FALSE** (at `StmtIn := Unit`, `U := UInt8`, sponge w

### `lemma5_16HonestResidualPaper_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:508](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L508) — The residual `Lemma5_16HonestResidualPaper`, discharged.
- `theorem DuplexSpongeFS.Sponge316.lemma5_16HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:508](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L508) — The residual `Lemma5_16HonestResidualPaper`, discharged.

### `lemma5_16_honest_hash_half` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_honest_hash_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L234) — **M2c, hash half** — CO25 Lemma 5.16, `E_{time,h}` side: off the combined bad event `E`, no backtrac
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_honest_hash_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L234) — **M2c, hash half** — CO25 Lemma 5.16, `E_{time,h}` side: off the combined bad event `E`, no backtrac

### `lemma5_16_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:497](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L497) — **CO25 Lemma 5.16, paper semantics — DISCHARGED** (both halves): off the paper combined bad event, a
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:497](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L497) — **CO25 Lemma 5.16, paper semantics — DISCHARGED** (both halves): off the paper combined bad event, a

### `lemma5_16_paper_hash_half` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper_hash_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:1011](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L1011) — **CO25 Lemma 5.16, hash half, paper semantics — DISCHARGED**: off the paper combined bad event, no b
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper_hash_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:1011](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L1011) — **CO25 Lemma 5.16, hash half, paper semantics — DISCHARGED**: off the paper combined bad event, no b

### `lemma5_16_paper_time_p_half` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper_time_p_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:452](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L452) — **CO25 Lemma 5.16, permutation half, paper semantics — DISCHARGED**: off the paper combined bad even
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper_time_p_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:452](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L452) — **CO25 Lemma 5.16, permutation half, paper semantics — DISCHARGED**: off the paper combined bad even

### `lemma5_8Bound_one_lt_one` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge314.K1.lemma5_8Bound_one_lt_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:128](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L128) — The claimed CO25 Lemma 5.8 bound at `T = 1` is `4/(2·256) < 1`.
- `lemma DuplexSpongeFS.Sponge314.K1.lemma5_8Bound_one_lt_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:128](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L128) — The claimed CO25 Lemma 5.8 bound at `T = 1` is `4/(2·256) < 1`.

### `lemma5_8EagerBirthdayFalseStatement_false` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge314.K1.lemma5_8EagerBirthdayFalseStatement_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:147](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L147) — **#314 K1 — the eager birthday residual is FALSE as stated** (at `StmtIn := Unit`, `U := UInt8`, spo
- `theorem DuplexSpongeFS.Sponge314.K1.lemma5_8EagerBirthdayFalseStatement_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:147](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L147) — **#314 K1 — the eager birthday residual is FALSE as stated** (at `StmtIn := Unit`, `U := UInt8`, spo

### `lemma5_8EagerPaperResidual_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.BirthdayBoundPaper.lemma5_8EagerPaperResidual_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean#L46) — **The repaired Lemma 5.8 eager residual holds**: the lazy-side bound `probEvent_EPaper_toReal_le_lem
- `theorem DuplexSpongeFS.BirthdayBoundPaper.lemma5_8EagerPaperResidual_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean#L46) — **The repaired Lemma 5.8 eager residual holds**: the lazy-side bound `probEvent_EPaper_toReal_le_lem

### `length_not_lt` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.length_not_lt` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:244](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L244) — Asymmetric length kill: a strictly shorter family sequence would put its hash-anchor capacity on a c
- `theorem DuplexSpongeFS.Paper.length_not_lt` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:244](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L244) — Asymmetric length kill: a strictly shorter family sequence would put its hash-anchor capacity on a c

### `length_not_lt_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.length_not_lt_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:599](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L599) — Asymmetric length kill: a strictly shorter family sequence would put its hash-anchor capacity on a c
- `theorem DuplexSpongeFS.Sponge316.length_not_lt_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:599](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L599) — Asymmetric length kill: a strictly shorter family sequence would put its hash-anchor capacity on a c

### `listPoly` (2 declarations, 2 files)

- `def Whir302SZ.listPoly` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:25](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L25) — The polynomial whose Horner evaluation is `listEval`.
- `def Whir302SZ.listPoly` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:98](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L98) — The polynomial whose Horner evaluation is `listEval`.

### `listPoly_cons` (2 declarations, 2 files)

- `theorem Whir302SZ.listPoly_cons` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:37](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L37) — (no docstring)
- `theorem Whir302SZ.listPoly_cons` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:110](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L110) — (no docstring)

### `listPoly_eval` (2 declarations, 2 files)

- `theorem Whir302SZ.listPoly_eval` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:28](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L28) — (no docstring)
- `theorem Whir302SZ.listPoly_eval` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:101](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L101) — (no docstring)

### `listPoly_natDegree_lt` (2 declarations, 2 files)

- `theorem Whir302SZ.listPoly_natDegree_lt` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:40](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L40) — (no docstring)
- `theorem Whir302SZ.listPoly_natDegree_lt` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:113](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L113) — (no docstring)

### `list_split_at` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.list_split_at` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:889](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L889) — A list splits at any in-range position into prefix, element, suffix.
- `theorem DuplexSpongeFS.EagerLazyDS.list_split_at` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:889](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L889) — A list splits at any in-range position into prefix, element, suffix.

### `mem_imp_sameClass_mem_removeRedundant` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_imp_sameClass_mem_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:470](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L470) — **Dedup is a system of class representatives**: every entry of the raw log has a class-representativ
- `theorem DuplexSpongeFS.EagerLazyDS.mem_imp_sameClass_mem_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:470](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L470) — **Dedup is a system of class representatives**: every entry of the raw log has a class-representativ

### `mem_of_mem_removeRedundantEntryDSPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_of_mem_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:608](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L608) — Every entry of the dedup'd base trace was already an entry of the original log.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_of_mem_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:608](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L608) — Every entry of the dedup'd base trace was already an entry of the original log.

### `mem_slotList_foldl_of_mem_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_foldl_of_mem_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:646](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L646) — A capacity cached early stays a slot of every later fold cache.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_foldl_of_mem_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:646](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L646) — A capacity cached early stays a slot of every later fold cache.

### `mem_slotList_of_hash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L234) — A cached hash answer is a slot.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L234) — A cached hash answer is a slot.

### `mem_slotList_of_hash_cached` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_hash_cached` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1302](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1302) — A cached hash answer is a slot.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_hash_cached` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1302](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1302) — A cached hash answer is a slot.

### `mem_slotList_of_mem_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_mem_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:637](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L637) — Both capacities of a cached permutation pair are slots.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_mem_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:637](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L637) — Both capacities of a cached permutation pair are slots.

### `mem_slotList_of_pair_fst` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_pair_fst` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:246](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L246) — A cached pair's forward-key capacity is a slot.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_pair_fst` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:246](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L246) — A cached pair's forward-key capacity is a slot.

### `mem_slotList_of_pair_snd` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_pair_snd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:255](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L255) — A cached pair's value capacity is a slot.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_pair_snd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:255](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L255) — A cached pair's value capacity is a slot.

### `mem_support_pure_eq` (2 declarations, 2 files)

- `lemma CheckClaim.mem_support_pure_eq` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:98](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L98) — Membership in the support of a `pure` pins the value. Applied (defeq-unified) against computations t
- `lemma CheckClaim.mem_support_pure_eq` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:106](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L106) — Membership in the support of a `pure` pins the value. Applied (defeq-unified) against computations t

### `mem_support_pure_optionT` (2 declarations, 2 files)

- `lemma CheckClaim.mem_support_pure_optionT` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:88](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L88) — A simulated `pure (some b)` only outputs `some b`.
- `lemma CheckClaim.mem_support_pure_optionT` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:96](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L96) — A simulated `pure (some b)` only outputs `some b`.

### `mergeVec` (2 declarations, 2 files)

- `def ArkLib.GMMDS.mergeVec` [ArkLib/Data/CodingTheory/GMMDS/LovettCoordMerge.lean:61](../../../ArkLib/Data/CodingTheory/GMMDS/LovettCoordMerge.lean#L61) — The merged multiplicity vector over `Fin (n−1)`: the new last coordinate carries the sum of `v(j*)`
- `def ArkLib.GMMDS.mergeVec` [ArkLib/Data/CodingTheory/GMMDS/LovettMergeSubstitution.lean:90](../../../ArkLib/Data/CodingTheory/GMMDS/LovettMergeSubstitution.lean#L90) — The merged vector in dimension `n`: move the `p`-mass onto `q`, zero out `p`.

### `mkSt` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TimePCounter.mkSt` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:65](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L65) — (no docstring)
- `def DuplexSpongeFS.Sponge316.TimePCounter.mkSt` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:65](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L65) — (no docstring)

### `natCast_sub_le_ennreal` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.natCast_sub_le_ennreal` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:253](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L253) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.natCast_sub_le_ennreal` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:253](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L253) — (no docstring)

### `noRedundant_pairwise_classDistinct` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.noRedundant_pairwise_classDistinct` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:617](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L617) — A `NoRedundantEntryDSPaper` trace is pairwise class-distinct: no later entry shares a class with any
- `theorem DuplexSpongeFS.EagerLazyDS.noRedundant_pairwise_classDistinct` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:617](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L617) — A `NoRedundantEntryDSPaper` trace is pairwise class-distinct: no later entry shares a class with any

### `noRedundant_raw_no_earlier_sameClass` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.noRedundant_raw_no_earlier_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:947](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L947) — In a `NoRedundant` log, no earlier entry is the same class as a later one (raw `ℕ` positions). The f
- `theorem DuplexSpongeFS.EagerLazyDS.noRedundant_raw_no_earlier_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:947](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L947) — In a `NoRedundant` log, no earlier entry is the same class as a later one (raw `ℕ` positions). The f

### `notFunction_data_impossible` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.notFunction_data_impossible` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:116](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L116) — **`E_func` refutation**: on a no-redundancy, consistent list, no forward entry can share its key wit
- `theorem DuplexSpongeFS.EagerLazyDS.notFunction_data_impossible` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:116](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L116) — **`E_func` refutation**: on a no-redundancy, consistent list, no forward entry can share its key wit

### `not_E_trc` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L274) — The combined bad event `E` does NOT fire on the countermodel trace.
- `theorem DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L274) — The combined bad event `E` does NOT fire on the countermodel trace.

### `not_E_trcF` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L365) — The combined bad event `E` does NOT fire on the countermodel trace.
- `theorem DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L365) — The combined bad event `E` does NOT fire on the countermodel trace.

### `not_anchoredFrom_cons` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_cons` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:544](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L544) — Cons-unfolding of `¬ AnchoredFrom`: no step of `e :: ℓ` is an anchored collision.
- `theorem DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_cons` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:544](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L544) — Cons-unfolding of `¬ AnchoredFrom`: no step of `e :: ℓ` is an anchored collision.

### `not_anchoredFrom_split` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:833](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L833) — `¬ AnchoredFrom` gives non-collision at every split point against the fold cache of the prefix.
- `theorem DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:833](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L833) — `¬ AnchoredFrom` gives non-collision at every split point against the fold cache of the prefix.

### `not_hasFwdKey_of_find` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.not_hasFwdKey_of_find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:663](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L663) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.not_hasFwdKey_of_find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:663](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L663) — (no docstring)

### `not_mem_fwdKeys_of_cap_not_slot` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.not_mem_fwdKeys_of_cap_not_slot` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:670](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L670) — A state whose capacity is not a slot is not a cached forward key.
- `lemma DuplexSpongeFS.EagerLazyDS.not_mem_fwdKeys_of_cap_not_slot` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:670](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L670) — A state whose capacity is not a slot is not a cached forward key.

### `not_redundantEntryDSPaper_forward_of_no_prior` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDSPaper_forward_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:297](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L297) — A forward slot whose pair has no prior copy in either direction is not paper-redundant: the first-oc
- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDSPaper_forward_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:297](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L297) — A forward slot whose pair has no prior copy in either direction is not paper-redundant: the first-oc

### `not_redundantEntryDSPaper_hash_of_no_prior` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDSPaper_hash_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:686](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L686) — A hash slot that is the first occurrence of its concrete entry is not paper-redundant (the hash cert
- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDSPaper_hash_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:686](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L686) — A hash slot that is the first occurrence of its concrete entry is not paper-redundant (the hash cert

### `optionT_bind_pure_some` (2 declarations, 2 files)

- `lemma RingSwitching.SumcheckPhase.optionT_bind_pure_some` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1080](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1080) — `OptionT.bind` of an honest `pure (some a)` reduces to the continuation at `a`. Used to collapse the
- `lemma RingSwitching.SumcheckPhase.optionT_bind_pure_some` [ArkLib/ProofSystem/RingSwitching/SumcheckRoundCompleteness.lean:69](../../../ArkLib/ProofSystem/RingSwitching/SumcheckRoundCompleteness.lean#L69) — `OptionT.bind` of an honest `pure (some a)` reduces to the continuation at `a`. Used to collapse the

### `optionT_liftM_run_add_left'` (2 declarations, 2 files)

- `theorem Reduction.optionT_liftM_run_add_left'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:41](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L41) — Run-characterization of the composite lift (left-inclusion).
- `theorem Reduction.optionT_liftM_run_add_left'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L46) — Run-characterization of the composite lift (left-inclusion).

### `optionT_liftM_run_assoc_path'` (2 declarations, 2 files)

- `theorem Reduction.optionT_liftM_run_assoc_path'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:48](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L48) — (no docstring)
- `theorem Reduction.optionT_liftM_run_assoc_path'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L53) — (no docstring)

### `pairKey_isSome_foldl_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.pairKey_isSome_foldl_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:341](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L341) — A satisfiable pair-cache predicate stays satisfiable through any fold suffix.
- `theorem DuplexSpongeFS.EagerLazyDS.pairKey_isSome_foldl_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:341](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L341) — A satisfiable pair-cache predicate stays satisfiable through any fold suffix.

### `pairKey_isSome_take_of_le` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.pairKey_isSome_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:98](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L98) — A satisfiable pair predicate at the `(j'+1)`-prefix fold persists to any larger prefix.
- `theorem DuplexSpongeFS.EagerLazyDS.pairKey_isSome_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:98](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L98) — A satisfiable pair predicate at the `(j'+1)`-prefix fold persists to any larger prefix.

### `pairRecord_cached_after_consistent_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_cached_after_consistent_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:293](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L293) — After a consistent forward step, the exact pair `(input, output)` is cached.
- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_cached_after_consistent_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:293](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L293) — After a consistent forward step, the exact pair `(input, output)` is cached.

### `pairRecord_cached_after_consistent_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_cached_after_consistent_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:312](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L312) — After a consistent inverse step, the exact pair `(answer, query)` is cached.
- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_cached_after_consistent_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:312](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L312) — After a consistent inverse step, the exact pair `(answer, query)` is cached.

### `pairRecord_take_of_le` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:174](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L174) — A pair record at the `(j'+1)`-prefix fold persists to any larger prefix.
- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:174](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L174) — A pair record at the `(j'+1)`-prefix fold persists to any larger prefix.

### `pairUDRClose_of_pairFiberwiseClose` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.pairUDRClose_of_pairFiberwiseClose` [ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean:1086](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean#L1086) — if `d⁽ⁱ⁾(f⁽ⁱ⁾, g⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance), then `d(f⁽ⁱ⁾, g⁽ⁱ⁾) < dᵢ/2` (regular c
- `lemma Binius.BinaryBasefold.pairUDRClose_of_pairFiberwiseClose` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorFar.lean:310](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorFar.lean#L310) — (no docstring)

### `prependRLCTargetWTKS` (2 declarations, 2 files)

- `abbrev Spartan.Spec.Bricks.prependRLCTargetWTKS` [ArkLib/ProofSystem/Spartan/ComposedTightRbrKnowledge.lean:177](../../../ArkLib/ProofSystem/Spartan/ComposedTightRbrKnowledge.lean#L177) — The carried honest RLC-target adapter pinned to the concrete oracle-interface universe used by the r
- `abbrev Spartan.Spec.Bricks.prependRLCTargetWTKS` [ArkLib/ProofSystem/Spartan/TightComposedFull.lean:52](../../../ArkLib/ProofSystem/Spartan/TightComposedFull.lean#L52) — Universe-pinned local alias of the carried RLC-target adapter (mirror of `prependRLCTargetKS`).

### `priorCapWitnessC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.priorCapWitnessC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:103](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L103) — Prior-witness class for the inverse-anchored collision shape: an earlier hash entry whose answer **i
- `def DuplexSpongeFS.Sponge316.priorCapWitnessC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:103](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L103) — Prior-witness class for the inverse-anchored collision shape: an earlier hash entry whose answer **i

### `probEvent_EPaper_toReal_le_lemma5_8Bound` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1662](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1662) — **CO25 Lemma 5.8, unconditional (eager lazy carrier).** For any `T`-query adversary, the probability
- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1662](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1662) — **CO25 Lemma 5.8, unconditional (eager lazy carrier).** For any `T`-query adversary, the probability

### `probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1622](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1622) — **The eager paper bound, conditional on the dedup reduction.** For any `T`-query adversary, the prob
- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1622](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1622) — **The eager paper bound, conditional on the dedup reduction.** For any `T`-query adversary, the prob

### `probEvent_E_eq_one` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge314.K1.probEvent_E_eq_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:106](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L106) — The combined bad event `E` fires with probability **1** in the eager logged game on the single-inver
- `lemma DuplexSpongeFS.Sponge314.K1.probEvent_E_eq_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:106](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L106) — The combined bad event `E` fires with probability **1** in the eager logged game on the single-inver

### `probEvent_eq_one_of_support_init` (2 declarations, 2 files)

- `lemma CheckClaim.probEvent_eq_one_of_support_init` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:105](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L105) — `OptionT`-level probability-one bridge with sampled initial state: if every output of the underlying
- `lemma CheckClaim.probEvent_eq_one_of_support_init` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:113](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L113) — `OptionT`-level probability-one bridge with sampled initial state: if every output of the underlying

### `probEvent_flag_final_le_sum` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_flag_final_le_sum` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:465](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L465) — **The accumulated flag bound**: a `T`-query computation, run from the empty cache with the flag down
- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_flag_final_le_sum` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:465](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L465) — **The accumulated flag bound**: a `T`-query computation, run from the empty cache with the flag down

### `probEvent_flag_final_toReal_le_lemma5_8Bound` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_flag_final_toReal_le_lemma5_8Bound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:545](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L545) — **The complete engine output for CO25 Lemma 5.8**: the final flag probability of any `T`-query compu
- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_flag_final_toReal_le_lemma5_8Bound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:545](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L545) — **The complete engine output for CO25 Lemma 5.8**: the final flag probability of any `T`-query compu

### `probEvent_salvage_le` (2 declarations, 2 files)

- `theorem Whir302SZ.probEvent_salvage_le` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:109](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L109) — **The per-round salvage probability bound** (the quantitative WHIR flip estimate): in any game that
- `theorem Whir302SZ.probEvent_salvage_le` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:180](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L180) — **The per-round salvage probability bound** (the quantitative WHIR flip estimate): in any game that

### `qIdx` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.Sponge314.K1.qIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L69) — The oracle index of the single adversary query: `p⁻¹(s₀)`.
- `abbrev DuplexSpongeFS.Sponge314.K1.qIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L69) — The oracle index of the single adversary query: `p⁻¹(s₀)`.

### `queryCap` (5 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.queryCap` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsCoincidence.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsCoincidence.lean#L148) — A mirror swap turns the answer-side capacity into the query-side capacity (for permutation entries;
- `def DuplexSpongeFS.Paper.queryCap` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean:76](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean#L76) — The query-side capacity segment (permutation entries only).
- `lemma DuplexSpongeFS.Paper.queryCap` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean:95](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean#L95) — (no docstring)
- `lemma DuplexSpongeFS.Paper.queryCap` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean#L99) — (no docstring)
- `lemma DuplexSpongeFS.Paper.queryCap` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean:103](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean#L103) — (no docstring)

### `reductionAppendPerfectCompletenessResidual_holds` (2 declarations, 2 files)

- `theorem Reduction.reductionAppendPerfectCompletenessResidual_holds` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessReductionDischarge.lean:90](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessReductionDischarge.lean#L90) — **Seam-direction-free discharge.** The appended seam round `m` is `pSpec₂`'s round `0` (`append_dir_
- `theorem Reduction.reductionAppendPerfectCompletenessResidual_holds` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessTotal.lean:78](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessTotal.lean#L78) — **`reductionAppendPerfectCompletenessResidual` is DISCHARGED** (seam-agnostic).

### `reduction_append_perfectCompleteness_msg` (2 declarations, 2 files)

- `theorem Reduction.reduction_append_perfectCompleteness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessMsg.lean:414](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessMsg.lean#L414) — **Append perfect completeness, residual-free (message-seam case).** The public composition theorem w
- `def Reduction.reduction_append_perfectCompleteness_msg` [ArkLib/Whir113Keystone.lean:17](../../../ArkLib/Whir113Keystone.lean#L17) — Residual for append perfect-completeness in the message-first case. The previous theorem body ended

### `redundantEntryDSPaper_forward_inversion` (2 declarations, 2 files)

- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_forward_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:35](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L35) — Inversion of `redundantEntryDSPaper` at a forward slot: the certificate is an earlier entry with the
- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_forward_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:35](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L35) — Inversion of `redundantEntryDSPaper` at a forward slot: the certificate is an earlier entry with the

### `redundantEntryDSPaper_hash_inversion` (2 declarations, 2 files)

- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_hash_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L77) — Inversion of `redundantEntryDSPaper` at a hash slot: an earlier copy of the same hash entry (unchang
- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_hash_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L77) — Inversion of `redundantEntryDSPaper` at a hash slot: an earlier copy of the same hash entry (unchang

### `redundantEntryDSPaper_iff_sameClass` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.redundantEntryDSPaper_iff_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:267](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L267) — The paper redundancy predicate is exactly "an earlier class member exists".
- `lemma DuplexSpongeFS.EagerLazyDS.redundantEntryDSPaper_iff_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:267](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L267) — The paper redundancy predicate is exactly "an earlier class member exists".

### `redundantEntryDSPaper_inverse_inversion` (2 declarations, 2 files)

- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_inverse_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:56](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L56) — Inversion of `redundantEntryDSPaper` at an inverse slot: the certificate is an earlier entry with th
- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_inverse_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:56](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L56) — Inversion of `redundantEntryDSPaper` at an inverse slot: the certificate is an earlier entry with th

### `redundantPaper_forward_capacity_prior` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.redundantPaper_forward_capacity_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:95](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L95) — A paper-redundant forward entry sharing a target capacity has an earlier **permutation** replacement
- `theorem OracleSpec.QueryLog.redundantPaper_forward_capacity_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:95](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L95) — A paper-redundant forward entry sharing a target capacity has an earlier **permutation** replacement

### `redundantPaper_inverse_capacity_prior` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.redundantPaper_inverse_capacity_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L118) — A paper-redundant inverse entry sharing a target capacity has an earlier **permutation** replacement
- `theorem OracleSpec.QueryLog.redundantPaper_inverse_capacity_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L118) — A paper-redundant inverse entry sharing a target capacity has an earlier **permutation** replacement

### `redundant_only_three` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.redundant_only_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:188](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L188) — No slot of `trc` other than `3` is redundant.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.redundant_only_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:188](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L188) — No slot of `trc` other than `3` is redundant.

### `redundant_three` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.redundant_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L184) — Entry 3 is in-tree-redundant: entry 2 is its same-direction swapped certificate.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.redundant_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L184) — Entry 3 is in-tree-redundant: entry 2 is its same-direction swapped certificate.

### `removeRedundantEntryDSPaper_pairwise_classDistinct` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_pairwise_classDistinct` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:627](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L627) — The dedup output is pairwise class-distinct.
- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_pairwise_classDistinct` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:627](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L627) — The dedup output is pairwise class-distinct.

### `removeRedundantEntryDSPaper_sublist` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:587](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L587) — The paper dedup output is a sublist of its input (each step erases one entry).
- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:587](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L587) — The paper dedup output is a sublist of its input (each step erases one entry).

### `removeRedundant_firstOcc` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundant_firstOcc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:975](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L975) — **Dedup positions are first occurrences.** There is an order embedding `f` of the dedup base trace i
- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundant_firstOcc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:975](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L975) — **Dedup positions are first occurrences.** There is an order embedding `f` of the dedup base trace i

### `removeRedundant_orderEmbedding` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundant_orderEmbedding` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:850](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L850) — The dedup base trace embeds into the raw log by a strictly monotone index map that preserves entries
- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundant_orderEmbedding` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:850](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L850) — The dedup base trace embeds into the raw log by a strictly monotone index map that preserves entries

### `sameClass` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L248) — Class membership: equal or the swap.
- `def DuplexSpongeFS.EagerLazyDS.sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L248) — Class membership: equal or the swap.

### `sameClass_of_entryKeys` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.sameClass_of_entryKeys` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:520](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L520) — An entry whose inserted pair is `(a, b)` is class-equal to the forward entry `⟨inr (inl a), b⟩`: it
- `theorem DuplexSpongeFS.EagerLazyDS.sameClass_of_entryKeys` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:520](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L520) — An entry whose inserted pair is `(a, b)` is class-equal to the forward entry `⟨inr (inl a), b⟩`: it

### `sameClass_refl` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_refl` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:251](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L251) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_refl` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:251](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L251) — (no docstring)

### `sameClass_symm` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_symm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:253](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L253) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_symm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:253](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L253) — (no docstring)

### `sameClass_trans` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_trans` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:258](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L258) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_trans` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:258](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L258) — (no docstring)

### `seqC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TimePCounter.seqC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L87) — The backtrack chain `sB → sA → sB`, then `sa → sb`, ending at `sT`.
- `def DuplexSpongeFS.Sponge316.TimePCounter.seqC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L87) — The backtrack chain `sB → sA → sB`, then `sa → sb`, ending at `sT`.

### `seqOne` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.seqOne` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:95](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L95) — Chain 1: the alternating loop `t1 → t2 → t1` on the first pair.
- `def DuplexSpongeFS.Sponge316.ForkCounter.seqOne` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:95](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L95) — Chain 1: the alternating loop `t1 → t2 → t1` on the first pair.

### `seqOne_ne_seqTwo` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.seqOne_ne_seqTwo` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:129](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L129) — The two chains are distinct (their `inputState` lists differ).
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.seqOne_ne_seqTwo` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:129](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L129) — The two chains are distinct (their `inputState` lists differ).

### `seqTwo` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.seqTwo` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:112](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L112) — Chain 2: the alternating loop `t3 → t4 → (cap t3 = cap t1)` on the second pair, ending at the same t
- `def DuplexSpongeFS.Sponge316.ForkCounter.seqTwo` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:112](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L112) — Chain 2: the alternating loop `t3 → t4 → (cap t3 = cap t1)` on the second pair, ending at the same t

### `slotList_length_le` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.slotList_length_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:160](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L160) — The slot list is at most twice the cache size.
- `lemma DuplexSpongeFS.EagerLazyDS.slotList_length_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:160](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L160) — The slot list is at most twice the cache size.

### `slots_pair_ASB` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_ASB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L114) — Entry 3 is the unique trace slot holding either orientation of the pair `(sA, sB)`.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_ASB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L114) — Entry 3 is the unique trace slot holding either orientation of the pair `(sA, sB)`.

### `slots_pair_asb` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_asb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L122) — Entry 1 is the unique trace slot holding either orientation of the pair `(sa, sb)`.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_asb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L122) — Entry 1 is the unique trace slot holding either orientation of the pair `(sa, sb)`.

### `step3` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step3` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:672](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L672) — Seam 2 (`firstChallenge ▷ …`, message seam: the right block opens with the first sum-check's leading
- `theorem Spartan.Spec.Bricks.step3` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:235](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L235) — Seam 2 (`firstChallenge ▷ …`, message seam: the right block opens with the first sum-check's leading

### `step4` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step4` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:634](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L634) — Seam 3 (`firstSumcheck ▷ …`, message seam: the right block opens with the bundled eval-claim `P_to_V
- `theorem Spartan.Spec.Bricks.step4` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:197](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L197) — Seam 3 (`firstSumcheck ▷ …`, message seam: the right block opens with the bundled eval-claim `P_to_V

### `step5` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step5` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:612](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L612) — Seam 4 (`sendEvalClaim ▷ …`, **challenge** seam: the right block opens with the linear-combination `
- `theorem Spartan.Spec.Bricks.step5` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:175](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L175) — Seam 4 (`sendEvalClaim ▷ …`, **challenge** seam: the right block opens with the linear-combination `

### `step6` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step6` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:571](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L571) — Seam 5 (`linearCombination ▷ …`, message seam: the right block opens with the second sum-check's lea
- `theorem Spartan.Spec.Bricks.step6` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:134](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L134) — Seam 5 (`linearCombination ▷ …`, message seam: the right block opens with the second sum-check's lea

### `step7` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step7` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:542](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L542) — Seam 6 (`prependRLCTarget ▷ …`, message seam through the 0-round left adapter).
- `theorem Spartan.Spec.Bricks.step7` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:105](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L105) — Seam 6 (`prependRLCTarget ▷ …`, message seam through the 0-round left adapter).

### `step8` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step8` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:517](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L517) — Seam 7 (`secondSumcheck ▷ finalCheck`, empty trailing seam).
- `theorem Spartan.Spec.Bricks.step8` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:80](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L80) — Seam 7 (`secondSumcheck ▷ finalCheck`, empty trailing seam).

### `stepCache` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.stepCache` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:51](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L51) — Fold one log entry onto a cache: first occurrence caches, repeats change nothing.
- `def DuplexSpongeFS.EagerLazyDS.stepCache` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:51](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L51) — Fold one log entry onto a cache: first occurrence caches, repeats change nothing.

### `stepCache_caches_fresh_hash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:113](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L113) — A fresh hash entry creates its record.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:113](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L113) — A fresh hash entry creates its record.

### `stepCache_caches_fresh_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:123](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L123) — A fresh forward permutation entry creates its pair.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:123](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L123) — A fresh forward permutation entry creates its pair.

### `stepCache_caches_fresh_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:134](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L134) — A fresh inverse permutation entry creates its (answer, query) pair.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:134](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L134) — A fresh inverse permutation entry creates its (answer, query) pair.

### `stepCache_fwdNodup` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_fwdNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:678](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L678) — One non-anchored fold step preserves forward-key distinctness.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_fwdNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:678](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L678) — One non-anchored fold step preserves forward-key distinctness.

### `stepCache_hash_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:315](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L315) — The hash cache only grows: an already-cached answer survives one fold step.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:315](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L315) — The hash cache only grows: an already-cached answer survives one fold step.

### `stepCache_hash_mono'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L53) — A cached hash record survives one fold step.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L53) — A cached hash record survives one fold step.

### `stepCache_hash_provenance` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1187](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1187) — **Hash-cache provenance (one step).** A hash answer present after a step was already cached or was i
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1187](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1187) — **Hash-cache provenance (one step).** A hash answer present after a step was already cached or was i

### `stepCache_noop_hash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:173](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L173) — A hash entry whose key is cached is a `stepCache` no-op.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:173](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L173) — A hash entry whose key is cached is a `stepCache` no-op.

### `stepCache_noop_of_classRedAt_consistent` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_of_classRedAt_consistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:419](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L419) — In a consistent log, a class-redundant slot is a `stepCache` no-op at its prefix fold. This is the c
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_of_classRedAt_consistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:419](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L419) — In a consistent log, a class-redundant slot is a `stepCache` no-op at its prefix fold. This is the c

### `stepCache_noop_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L184) — A forward entry whose key is cached is a `stepCache` no-op.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L184) — A forward entry whose key is cached is a `stepCache` no-op.

### `stepCache_noop_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:198](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L198) — An inverse entry whose key is cached is a `stepCache` no-op.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:198](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L198) — An inverse entry whose key is cached is a `stepCache` no-op.

### `stepCache_pair_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_pair_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L77) — A cached permutation pair survives one fold step.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_pair_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L77) — A cached permutation pair survives one fold step.

### `stepCache_pair_provenance` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_pair_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:716](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L716) — **Pair provenance (one step)**: a pair in the cache after a step was already there or was inserted b
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_pair_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:716](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L716) — **Pair provenance (one step)**: a pair in the cache after a step was already there or was inserted b

### `stepCache_perm_sublist` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_perm_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L300) — The permutation cache only grows (as a sublist) along one fold step.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_perm_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L300) — The permutation cache only grows (as a sublist) along one fold step.

### `step_determinism` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.step_determinism` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:76](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L76) — **U1 (step determinism, paper event)** — CO25 Claim 5.19, Eq. 44 step: off `EPaper`, two chain steps
- `theorem DuplexSpongeFS.Paper.step_determinism` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:76](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L76) — **U1 (step determinism, paper event)** — CO25 Claim 5.19, Eq. 44 step: off `EPaper`, two chain steps

### `step_determinism_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.step_determinism_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L300) — **Step determinism, paper event**: off `BadEventDSPaper.E`, two family chain steps whose output capa
- `theorem DuplexSpongeFS.Sponge316.step_determinism_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L300) — **Step determinism, paper event**: off `BadEventDSPaper.E`, two family chain steps whose output capa

### `stirInitReduction_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem StirIOP.Round3.stirInitReduction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Stir/InitAppendRbr.lean:123](../../../ArkLib/ProofSystem/Stir/InitAppendRbr.lean#L123) — RBR knowledge soundness of the initial block, phrased on `stirInitReduction`'s verifier.
- `theorem StirIOP.Round3.stirInitReduction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Stir/InitRbrSoundness.lean:109](../../../ArkLib/ProofSystem/Stir/InitRbrSoundness.lean#L109) — RBR knowledge soundness of the initial block, phrased on `stirInitReduction`'s verifier.

### `stirInitVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem StirIOP.Round3.stirInitVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Stir/InitAppendRbr.lean:84](../../../ArkLib/ProofSystem/Stir/InitAppendRbr.lean#L84) — **RBR knowledge soundness of the initial `[C_fold]` block, with zero error.** The verifier is a pure
- `theorem StirIOP.Round3.stirInitVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Stir/InitRbrSoundness.lean:70](../../../ArkLib/ProofSystem/Stir/InitRbrSoundness.lean#L70) — **RBR knowledge soundness of the initial `[C_fold]` block, with zero error.** The verifier is a pure

### `stirInitVerifier_toVerifier_eq` (2 declarations, 2 files)

- `theorem StirIOP.Round3.stirInitVerifier_toVerifier_eq` [ArkLib/ProofSystem/Stir/InitAppendRbr.lean:71](../../../ArkLib/ProofSystem/Stir/InitAppendRbr.lean#L71) — The initial block's relay verifier, seen as a non-oracle verifier, is the *pure* deterministic verif
- `theorem StirIOP.Round3.stirInitVerifier_toVerifier_eq` [ArkLib/ProofSystem/Stir/InitRbrSoundness.lean:57](../../../ArkLib/ProofSystem/Stir/InitRbrSoundness.lean#L57) — The initial block's relay verifier, seen as a non-oracle verifier, is the *pure* deterministic verif

### `stirInitVerifier_toVerifier_run` (2 declarations, 2 files)

- `theorem StirIOP.Round3.stirInitVerifier_toVerifier_run` [ArkLib/ProofSystem/Stir/InitAppendRbr.lean:58](../../../ArkLib/ProofSystem/Stir/InitAppendRbr.lean#L58) — Running the initial block's (oracle) verifier deterministically returns the fold challenge together
- `theorem StirIOP.Round3.stirInitVerifier_toVerifier_run` [ArkLib/ProofSystem/Stir/InitRbrSoundness.lean:44](../../../ArkLib/ProofSystem/Stir/InitRbrSoundness.lean#L44) — Running the initial block's (oracle) verifier deterministically returns the fold challenge together

### `stirInitVerify` (2 declarations, 2 files)

- `def StirIOP.Round3.stirInitVerify` [ArkLib/ProofSystem/Stir/InitAppendRbr.lean:51](../../../ArkLib/ProofSystem/Stir/InitAppendRbr.lean#L51) — The deterministic statement map computed by the initial block's relay verifier: read the fold challe
- `def StirIOP.Round3.stirInitVerify` [ArkLib/ProofSystem/Stir/InitRbrSoundness.lean:37](../../../ArkLib/ProofSystem/Stir/InitRbrSoundness.lean#L37) — The deterministic statement map computed by the initial block's relay verifier: read the fold challe

### `sum_lemma58StepBound_le` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.sum_lemma58StepBound_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:489](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L489) — The Gauss-sum domination: below half the state space, the accumulated step bounds sum to at most `2T
- `theorem DuplexSpongeFS.EagerLazyDS.sum_lemma58StepBound_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:489](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L489) — The Gauss-sum domination: below half the state space, the accumulated step bounds sum to at most `2T

### `sum_map_two_mul_sub_one` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.sum_map_two_mul_sub_one` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2KeystoneReindex.lean:183](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2KeystoneReindex.lean#L183) — Auxiliary: `∑_{l ∈ λ} (2 l - 1) = 2 c - (number of parts)` (truncated ℕ subtraction). The per-part s
- `theorem BCIKS20.HenselNumerator.sum_map_two_mul_sub_one` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/RestrictedFaaDiBrunoXiTelescope.lean:94](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/RestrictedFaaDiBrunoXiTelescope.lean#L94) — **The LHS `ξ`-denominator exponent of a partition (axiom-clean).** The assembled-series coefficient

### `sum_range_two_mul_add_one` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.sum_range_two_mul_add_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:481](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L481) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.sum_range_two_mul_add_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:481](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L481) — (no docstring)

### `support_flagged_logged` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.support_flagged_logged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:177](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L177) — **The master run correspondence**: every support element of the flagged run of the logged program ha
- `theorem DuplexSpongeFS.EagerLazyDS.support_flagged_logged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:177](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L177) — **The master run correspondence**: every support element of the flagged run of the logged program ha

### `support_oracleReduction_run` (2 declarations, 2 files)

- `theorem CheckClaim.support_oracleReduction_run` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:186](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L186) — **The pred-generic support collapse for the full honest `CheckClaim` oracle reduction**: the run onl
- `theorem CheckClaim.support_oracleReduction_run` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:169](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L169) — **The pred-generic support collapse for the full honest `CheckClaim` oracle reduction**: the run onl

### `support_simulateQ_subset'` (2 declarations, 2 files)

- `lemma CheckClaim.support_simulateQ_subset'` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:64](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L64) — Outputs of a simulated computation (into another `OracleComp`) are outputs of the original computati
- `lemma CheckClaim.support_simulateQ_subset'` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:72](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L72) — Outputs of a simulated computation (into another `OracleComp`) are outputs of the original computati

### `support_toVerifier_run` (2 declarations, 2 files)

- `theorem CheckClaim.support_toVerifier_run` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:160](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L160) — **The pred-generic support collapse for the compiled `CheckClaim` oracle verifier**: the run only ev
- `theorem CheckClaim.support_toVerifier_run` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:143](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L143) — **The pred-generic support collapse for the compiled `CheckClaim` oracle verifier**: the run only ev

### `swapEntry` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.swapEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:237](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L237) — The opposite-direction form of an entry (hash entries are self-paired).
- `def DuplexSpongeFS.EagerLazyDS.swapEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:237](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L237) — The opposite-direction form of an entry (hash entries are self-paired).

### `swapEntry_eq_mirrorOf` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.swapEntry_eq_mirrorOf` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L46) — The Correspondence-file `swapEntry` and the Engine-file `mirrorOf` are the same map.
- `theorem DuplexSpongeFS.EagerLazyDS.swapEntry_eq_mirrorOf` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L46) — The Correspondence-file `swapEntry` and the Engine-file `mirrorOf` are the same map.

### `swapEntry_swapEntry` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.swapEntry_swapEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:242](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L242) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.swapEntry_swapEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:242](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L242) — (no docstring)

### `swapKey_cached_after_consistent_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.swapKey_cached_after_consistent_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L248) — After a consistent forward step, the **inverse** key is cached: fresh creates `(a, b)` (serving the
- `theorem DuplexSpongeFS.EagerLazyDS.swapKey_cached_after_consistent_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L248) — After a consistent forward step, the **inverse** key is cached: fresh creates `(a, b)` (serving the

### `swapKey_cached_after_consistent_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.swapKey_cached_after_consistent_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:266](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L266) — After a consistent inverse step, the **forward** key is cached: fresh creates `(a, b)` (serving the
- `theorem DuplexSpongeFS.EagerLazyDS.swapKey_cached_after_consistent_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:266](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L266) — After a consistent inverse step, the **forward** key is cached: fresh creates `(a, b)` (serving the

### `take_inner_split` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.take_inner_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1314](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1314) — The inner split of `take (f j)` at an earlier position `f j'`.
- `theorem DuplexSpongeFS.EagerLazyDS.take_inner_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1314](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1314) — The inner split of `take (f j)` at an earlier position `f j'`.

### `take_split_getElem` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.take_split_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:399](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L399) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.take_split_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:399](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L399) — (no docstring)

### `totalDegree_ehQ_le` (2 declarations, 2 files)

- `lemma MvPolynomial.totalDegree_ehQ_le` [ArkLib/ToMathlib/RestrictedSumset.lean:265](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L265) — `ehQ Cset` has total degree at most `\|Cset\| + 1`.
- `lemma MvPolynomial.totalDegree_ehQ_le` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:316](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L316) — `ehQ h Cset` has total degree at most `deg(vdmX) + \|Cset\|`.

### `totalDegree_prod_sub_pow_le` (2 declarations, 2 files)

- `lemma MvPolynomial.totalDegree_prod_sub_pow_le` [ArkLib/ToMathlib/RestrictedSumset.lean:183](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L183) — **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{\|s\|}` by a pol
- `lemma MvPolynomial.totalDegree_prod_sub_pow_le` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:195](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L195) — **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{\|s\|}` by a pol

### `trc` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TimePCounter.trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:81](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L81) — The raw countermodel trace.
- `def DuplexSpongeFS.Sponge316.TimePCounter.trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:81](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L81) — The raw countermodel trace.

### `trc'` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TimePCounter.trc'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L84) — The dedup'd trace: entry 3 (`(p, sA, sB)`) is in-tree-redundant w.r.t. entry 2.
- `def DuplexSpongeFS.Sponge316.TimePCounter.trc'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L84) — The dedup'd trace: entry 3 (`(p, sA, sB)`) is in-tree-redundant w.r.t. entry 2.

### `trc'_noRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.trc'_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:218](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L218) — No slot of the 3-entry trace `trc'` is redundant.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.trc'_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:218](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L218) — No slot of the 3-entry trace `trc'` is redundant.

### `trcA` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.trcA` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L84) — Intermediate trace after erasing slot 2 first.
- `def DuplexSpongeFS.Sponge316.ForkCounter.trcA` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L84) — Intermediate trace after erasing slot 2 first.

### `trcA_redundant_only` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcA_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:218](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L218) — In `trcA`, only slot 3 is redundant.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcA_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:218](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L218) — In `trcA`, only slot 3 is redundant.

### `trcA_redundant_three` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcA_redundant_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:214](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L214) — In `trcA = [eH, q1, q3, q4]`, slot 3 is redundant (slot 2 is its certificate).
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcA_redundant_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:214](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L214) — In `trcA = [eH, q1, q3, q4]`, slot 3 is redundant (slot 2 is its certificate).

### `trcB` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.trcB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L87) — Intermediate trace after erasing slot 4 first.
- `def DuplexSpongeFS.Sponge316.ForkCounter.trcB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L87) — Intermediate trace after erasing slot 4 first.

### `trcB_redundant_only` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcB_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:249](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L249) — In `trcB`, only slot 2 is redundant.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcB_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:249](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L249) — In `trcB`, only slot 2 is redundant.

### `trcB_redundant_two` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcB_redundant_two` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:245](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L245) — In `trcB = [eH, q1, q2, q3]`, slot 2 is redundant (slot 1 is its certificate).
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcB_redundant_two` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:245](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L245) — In `trcB = [eH, q1, q2, q3]`, slot 2 is redundant (slot 1 is its certificate).

### `trcD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.trcD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L90) — The dedup fixpoint: both erasure orders converge here.
- `def DuplexSpongeFS.Sponge316.ForkCounter.trcD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L90) — The dedup fixpoint: both erasure orders converge here.

### `trcD_noRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcD_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:280](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L280) — No slot of the 3-entry trace `trcD` is redundant.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcD_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:280](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L280) — No slot of the 3-entry trace `trcD` is redundant.

### `trcF` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:81](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L81) — The raw countermodel trace.
- `def DuplexSpongeFS.Sponge316.ForkCounter.trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:81](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L81) — The raw countermodel trace.

### `trcF_redundant_four` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_four` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:175](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L175) — Slot 4 (`(p, t4, t3)`) is in-tree-redundant: slot 3 is its swapped certificate.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_four` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:175](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L175) — Slot 4 (`(p, t4, t3)`) is in-tree-redundant: slot 3 is its swapped certificate.

### `trcF_redundant_only` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:179](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L179) — No slot of `trcF` other than `2` and `4` is redundant.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:179](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L179) — No slot of `trcF` other than `2` and `4` is redundant.

### `trcF_redundant_two` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_two` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:171](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L171) — Slot 2 (`(p, t2, t1)`) is in-tree-redundant: slot 1 is its swapped certificate.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_two` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:171](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L171) — Slot 2 (`(p, t2, t1)`) is in-tree-redundant: slot 1 is its swapped certificate.

### `twoSurvivors_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.twoSurvivors_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:170](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L170) — One-step preservation: erasing a paper-redundant entry preserves the two-survivor shape (the guarded
- `lemma DuplexSpongeFS.Sponge316.twoSurvivors_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:170](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L170) — One-step preservation: erasing a paper-redundant entry preserves the two-survivor shape (the guarded

### `twoSurvivors_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.twoSurvivors_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:194](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L194) — **Two-survivor dedup transport**: both guarded slots survive paper dedup, in order.
- `lemma DuplexSpongeFS.Sponge316.twoSurvivors_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:194](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L194) — **Two-survivor dedup transport**: both guarded slots survive paper dedup, in order.

## Near-duplicate docstrings (Jaccard ≥ 0.85, 166 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `ArkLib.SeqComposeRbrKnowledge.idxToSigma_inl` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:69](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L69) vs `ArkLib.SeqComposeRbrSoundness.idxToSigma_inl` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:91](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L91)
    - a: `seqComposeChallengeIdxToSigma` along the `inl` embedding of a head challenge index lands in the fir
    - b: `seqComposeChallengeIdxToSigma` along the `inl` embedding of a head challenge index lands in the fir
- **1.00** `ArkLib.SeqComposeRbrKnowledge.idxToSigma_inr` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:96](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L96) vs `ArkLib.SeqComposeRbrSoundness.idxToSigma_inr` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:118](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L118)
    - a: `seqComposeChallengeIdxToSigma` along the `inr` embedding of a tail challenge index: the first compo
    - b: `seqComposeChallengeIdxToSigma` along the `inr` embedding of a tail challenge index: the first compo
- **1.00** `ArkLib.SeqComposeRbrKnowledge.seqComposeError_eq_append` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:130](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L130) vs `ArkLib.SeqComposeRbrSoundness.seqComposeError_eq_append` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:152](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L152)
    - a: **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global challenge inde
    - b: **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global challenge inde
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.append_dir_seam` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:200](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L200) vs `Binius.FRIBinius.FullFRIBinius.append_dir_seam` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:555](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L555)
    - a: Left-boundary direction transport for appended protocols: the appended protocol's direction at the s
    - b: Left-boundary direction transport for appended protocols: the appended protocol's direction at the s
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:98](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L98) vs `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:173](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L173)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:98](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L98) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:114](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L114)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:70](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L70) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:142](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L142)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:113](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L113) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:193](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L193)
    - a: Perfect completeness for the full Binary Basefold protocol (reduction)
    - b: Perfect completeness for the full Binary Basefold protocol (reduction)
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:47](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L47) vs `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:116](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L116)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:47](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L47) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:63](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L63)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.hammingDist_le_pair_fiberwiseDistance_mul_two_pow_steps` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorFar.lean:162](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorFar.lean#L162) vs `Binius.BinaryBasefold.hammingDist_le_pair_fiberwiseDistance_mul_two_pow_steps_farLiftLocal` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/SoundnessCase2FarLift.lean:321](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/SoundnessCase2FarLift.lean#L321)
    - a: Source Hamming distance is bounded by the number of bad quotient fibers times the fiber size. Local
    - b: Source Hamming distance is bounded by the number of bad quotient fibers times the fiber size. Local
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1467](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1467) vs `RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:492](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L492)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1309](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1309) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1513](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1513)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:668](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L668) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1307](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1307)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1320](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1320) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1516](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1516)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:173](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L173) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:114](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L114)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:116](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L116) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:63](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L63)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `CodingTheory.span_inf_ker_proj_of_eq_zero` [ArkLib/Data/CodingTheory/SubspaceDesign.lean:115](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean#L115) vs `CodingTheory.um_span_inf_ker_proj_of_eq_zero` [ArkLib/ToMathlib/UMSubspaceDesignProof.lean:263](../../../ArkLib/ToMathlib/UMSubspaceDesignProof.lean#L263)
    - a: The 1-dimensional subspace `span{a}` meets `ker(proj i)` in itself when `a i = 0`.
    - b: The 1-dimensional subspace `span{a}` meets `ker(proj i)` in itself when `a i = 0`.
- **1.00** `CodingTheory.span_inf_ker_proj_of_ne_zero` [ArkLib/Data/CodingTheory/SubspaceDesign.lean:124](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean#L124) vs `CodingTheory.um_span_inf_ker_proj_of_ne_zero` [ArkLib/ToMathlib/UMSubspaceDesignProof.lean:272](../../../ArkLib/ToMathlib/UMSubspaceDesignProof.lean#L272)
    - a: The 1-dimensional subspace `span{a}` meets `ker(proj i)` trivially when `a i ≠ 0`.
    - b: The 1-dimensional subspace `span{a}` meets `ker(proj i)` trivially when `a i ≠ 0`.
- **1.00** `Commitment.perfectCorrectness` [ArkLib/Commitments/Functional/Basic.lean:109](../../../ArkLib/Commitments/Functional/Basic.lean#L109) vs `CommitmentScheme.perfectCorrectness` [ArkLib/Commitments/Functional/CommitmentScheme.lean:74](../../../ArkLib/Commitments/Functional/CommitmentScheme.lean#L74)
    - a: A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
    - b: A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
- **1.00** `DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L49) vs `DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L286)
    - a: Transport a `List.getElem` along a `Nat` index equality.
    - b: Transport a `List.getElem` along a `Nat` index equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L49) vs `DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L286)
    - a: Transport a `List.getElem` along a `Nat` index equality.
    - b: Transport a `List.getElem` along a `Nat` index equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L49) vs `DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L286)
    - a: Transport a `List.getElem` along a `Nat` index equality.
    - b: Transport a `List.getElem` along a `Nat` index equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L49) vs `DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L286)
    - a: Transport a `List.getElem` along a `Nat` index equality.
    - b: Transport a `List.getElem` along a `Nat` index equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L53) vs `DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L292)
    - a: Transport a `List.getElem` along a list equality.
    - b: Transport a `List.getElem` along a list equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L53) vs `DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L292)
    - a: Transport a `List.getElem` along a list equality.
    - b: Transport a `List.getElem` along a list equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L53) vs `DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L292)
    - a: Transport a `List.getElem` along a list equality.
    - b: Transport a `List.getElem` along a list equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L53) vs `DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L292)
    - a: Transport a `List.getElem` along a list equality.
    - b: Transport a `List.getElem` along a list equality.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L354) vs `DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L263)
    - a: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
    - b: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L354) vs `DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L263)
    - a: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
    - b: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L354) vs `DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L263)
    - a: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
    - b: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L354) vs `DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L263)
    - a: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
    - b: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L365) vs `DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L274)
    - a: The combined bad event `E` does NOT fire on the countermodel trace.
    - b: The combined bad event `E` does NOT fire on the countermodel trace.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L365) vs `DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L274)
    - a: The combined bad event `E` does NOT fire on the countermodel trace.
    - b: The combined bad event `E` does NOT fire on the countermodel trace.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L365) vs `DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L274)
    - a: The combined bad event `E` does NOT fire on the countermodel trace.
    - b: The combined bad event `E` does NOT fire on the countermodel trace.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L365) vs `DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L274)
    - a: The combined bad event `E` does NOT fire on the countermodel trace.
    - b: The combined bad event `E` does NOT fire on the countermodel trace.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.trcA` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L84) vs `DuplexSpongeFS.Sponge316.ForkCounter.trcB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L87)
    - a: Intermediate trace after erasing slot 2 first.
    - b: Intermediate trace after erasing slot 4 first.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.trcA` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L84) vs `DuplexSpongeFS.Sponge316.ForkCounter.trcB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L87)
    - a: Intermediate trace after erasing slot 2 first.
    - b: Intermediate trace after erasing slot 4 first.
- **1.00** `DuplexSpongeFS.Sponge316.TimePCounter.index_step1` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:130](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L130) vs `DuplexSpongeFS.Sponge316.TimePCounter.index_step2` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:150](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L150)
    - a: The chain index of step 1 (pair `(sA, sB)`) is the raw slot `3`.
    - b: The chain index of step 2 (pair `(sa, sb)`) is the raw slot `1`.
- **1.00** `DuplexSpongeFS.Sponge316.TimePCounter.index_step1` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:130](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L130) vs `DuplexSpongeFS.Sponge316.TimePCounter.index_step2` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:150](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L150)
    - a: The chain index of step 1 (pair `(sA, sB)`) is the raw slot `3`.
    - b: The chain index of step 2 (pair `(sa, sb)`) is the raw slot `1`.
- **1.00** `DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_ASB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L114) vs `DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_asb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L122)
    - a: Entry 3 is the unique trace slot holding either orientation of the pair `(sA, sB)`.
    - b: Entry 1 is the unique trace slot holding either orientation of the pair `(sa, sb)`.
- **1.00** `DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_ASB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L114) vs `DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_asb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L122)
    - a: Entry 3 is the unique trace slot holding either orientation of the pair `(sA, sB)`.
    - b: Entry 1 is the unique trace slot holding either orientation of the pair `(sa, sb)`.
- **1.00** `DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L118) vs `DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L69)
    - a: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
    - b: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- **1.00** `DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L118) vs `DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L69)
    - a: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
    - b: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- **1.00** `DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L118) vs `DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L69)
    - a: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
    - b: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- **1.00** `DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L118) vs `DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L69)
    - a: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
    - b: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:306](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L306) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L203)
    - a: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
    - b: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:306](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L306) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L203)
    - a: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
    - b: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:227](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L227) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:330](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L330)
    - a: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
    - b: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:227](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L227) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:330](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L330)
    - a: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
    - b: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
- **1.00** `Groups.exists_zmod_power_of_generator` [ArkLib/Commitments/Functional/KZG/Algebra.lean:105](../../../ArkLib/Commitments/Functional/KZG/Algebra.lean#L105) vs `KZG.CommitmentScheme.binding_exists_zmod_power_of_generator` [ArkLib/Commitments/Functional/KZG/Binding.lean:167](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L167)
    - a: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
    - b: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
- **1.00** `Groups.orderOf_eq_prime_of_ne_one` [ArkLib/Commitments/Functional/KZG/Algebra.lean:61](../../../ArkLib/Commitments/Functional/KZG/Algebra.lean#L61) vs `KZG.CommitmentScheme.binding_order_of_eq_prime_of_ne_one` [ArkLib/Commitments/Functional/KZG/Binding.lean:157](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L157)
    - a: A nontrivial element of a prime-order group has order `p`.
    - b: A nontrivial element of a prime-order group has order `p`.
- **1.00** `KZG.CommitmentScheme.map_binding_instance_drag` [ArkLib/Commitments/Functional/KZG/Binding.lean:639](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L639) vs `KZG.CommitmentScheme.map_instance_drag` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:534](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L534)
    - a: Transition 3: dragging the map into the probability event.
    - b: Transition 3: dragging the map into the probability event
- **1.00** `Logup.simulateQ_optionT_failure'` [ArkLib/ProofSystem/Logup/Security/OuterRun.lean:52](../../../ArkLib/ProofSystem/Logup/Security/OuterRun.lean#L52) vs `ToyProblem.Spec.simulateQ_optionT_failure` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:643](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L643)
    - a: `simulateQ` commutes with `OptionT` `failure`.
    - b: `simulateQ` commutes with `OptionT` `failure`.
- **1.00** `Logup.simulateQ_optionT_pure'` [ArkLib/ProofSystem/Logup/Security/OuterRun.lean:44](../../../ArkLib/ProofSystem/Logup/Security/OuterRun.lean#L44) vs `ToyProblem.Spec.simulateQ_optionT_pure` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:636](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L636)
    - a: `simulateQ` commutes with `OptionT.pure`.
    - b: `simulateQ` commutes with `OptionT.pure`.
- **1.00** `Logup.simulateQ_simOracle2_leftQuery_oc'` [ArkLib/ProofSystem/Logup/Security/OuterRun.lean:129](../../../ArkLib/ProofSystem/Logup/Security/OuterRun.lean#L129) vs `ToyProblem.Spec.simulateQ_simOracle2_leftQuery_oc` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:733](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L733)
    - a: `simOracle2` oracle-statement-query collapse (`OracleComp` form), LEFT (oracle) family.
    - b: `simOracle2` oracle-statement-query collapse (`OracleComp` form), LEFT (oracle) family.
- **1.00** `OracleSpec.QueryLog.BadEventDS.E_removeRedundantEntryDS_iff` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:231](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L231) vs `OracleSpec.QueryLog.BadEventDSPaper.E_removeRedundantEntryDSPaper_iff` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:207](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L207)
    - a: The combined bad event only depends on the deduplicated base trace.
    - b: The combined bad event only depends on the deduplicated base trace.
- **1.00** `OracleSpec.QueryLog.BadEventDS.capacitySegmentDup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:208](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L208) vs `OracleSpec.QueryLog.BadEventDSPaper.capacitySegmentDup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L184)
    - a: The combined capacity segment collision event. This occurs if there is any capacity segment collisio
    - b: The combined capacity segment collision event. This occurs if there is any capacity segment collisio
- **1.00** `OracleSpec.QueryLog.BadEventDS.lemma_5_10` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:379](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L379) vs `OracleSpec.QueryLog.BadEventDSPaper.lemma_5_10` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:355](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L355)
    - a: CO25 Lemma 5.10, current trace-event form. If the combined bad event `E(tr)` does not occur, then th
    - b: CO25 Lemma 5.10, current trace-event form. If the combined bad event `E(tr)` does not occur, then th
- **1.00** `Probability.uniformSizeSubset_apply_mapEquiv` [ArkLib/Data/Probability/Combinatorial.lean:168](../../../ArkLib/Data/Probability/Combinatorial.lean#L168) vs `Probability.uniformSizedSubset_apply_mapEquiv` [ArkLib/Data/Probability/UniformSubset.lean:115](../../../ArkLib/Data/Probability/UniformSubset.lean#L115)
    - a: Uniform fixed-size subset sampling is invariant under equivalence of ambient finite types.
    - b: Uniform fixed-size subset sampling is invariant under equivalence of ambient finite types.
- **1.00** `Prover.processRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:491](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L491) vs `Prover.processRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:80](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L80)
    - a: Prover's function for processing the next round, given the current result of the previous round. Thi
    - b: Prover's function for processing the next round, given the current result of the previous round. Thi
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:60](../../../ArkLib/OracleReduction/Execution.lean#L60) vs `Prover.runToRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:524](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L524)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:60](../../../ArkLib/OracleReduction/Execution.lean#L60) vs `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:102](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L102)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `Prover.runToRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:524](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L524) vs `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:102](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L102)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `ProximityGap.RS_goodCoeffsCurve_finCongr` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:194](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L194) vs `ProximityGap.RS_goodCoeffsCurve_finCongr_core` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:1082](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L1082)
    - a: `RS_goodCoeffsCurve` is unchanged by a definitional reindexing of its `Fin (k + 1)` coefficient word
    - b: `RS_goodCoeffsCurve` is unchanged by a definitional reindexing of its `Fin (k + 1)` coefficient word
- **1.00** `ProximityPrize.HenselExistence.coeff_S_succ_of_le` [ArkLib/Data/Polynomial/HenselExistence.lean:197](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L197) vs `ProximityPrize.HenselSeriesCoeff.coeff_S_succ_of_le` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:275](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L275)
    - a: Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.
    - b: Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.
- **1.00** `ProximityPrize.HenselExistence.coeff_γ_eq_S` [ArkLib/Data/Polynomial/HenselExistence.lean:236](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L236) vs `ProximityPrize.HenselSeriesCoeff.coeff_γ_eq_S` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:312](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L312)
    - a: `γ` agrees with the `t`-th partial sum below order `t + 1`.
    - b: `γ` agrees with the `t`-th partial sum below order `t + 1`.
- **1.00** `ProximityPrize.HenselExistence.constantCoeff_γ` [ArkLib/Data/Polynomial/HenselExistence.lean:231](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L231) vs `ProximityPrize.HenselSeriesCoeff.constantCoeff_γ` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:307](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L307)
    - a: The constant coefficient of the Newton root is the prescribed root `c`.
    - b: The constant coefficient of the Newton root is the prescribed root `c`.
- **1.00** `Reduction.dsfs_lift_query_bridge_inl` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:166](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L166) vs `Reduction.dsfs_lift_query_bridge_inl₂` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:232](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L232)
    - a: Bridge: annotated vs direct lift of a single left-side query.
    - b: Bridge: annotated vs direct lift of a single left-side query.
- **1.00** `Reduction.dsfs_lift_query_bridge_inl` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:171](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L171) vs `Reduction.dsfs_lift_query_bridge_inl₂` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:226](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L226)
    - a: Bridge: annotated vs direct lift of a single left-side query.
    - b: Bridge: annotated vs direct lift of a single left-side query.
- **1.00** `Reduction.hcoh_right` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean:147](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean#L147) vs `Reduction.hcoh_right'` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges2.lean:130](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges2.lean#L130)
    - a: **`OptionT`-level lift transitivity through the `pSpec₂` challenge seam.** The `pSpec₂` analogue of
    - b: **`OptionT`-level lift transitivity through the `pSpec₂` challenge seam.** The `pSpec₂` analogue of
- **1.00** `Spartan.Spec.Bricks.composedPIOPTightPure_perfectCompleteness_of_leaves` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:285](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L285) vs `Spartan.Spec.Bricks.composedPIOP_Rc_perfectCompleteness_of_leaves` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:722](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L722)
    - a: **Composed Spartan PIOP perfect completeness, reduced to the eight leaf perfect-completenesses** (is
    - b: **Composed Spartan PIOP perfect completeness, reduced to the eight leaf perfect-completenesses** (is
- **1.00** `Spartan.Spec.Bricks.finalCheckTightC` [ArkLib/ProofSystem/Spartan/TightComposedComplete.lean:98](../../../ArkLib/ProofSystem/Spartan/TightComposedComplete.lean#L98) vs `Spartan.Spec.Bricks.finalCheckTightKS` [ArkLib/ProofSystem/Spartan/TightComposedFull.lean:66](../../../ArkLib/ProofSystem/Spartan/TightComposedFull.lean#L66)
    - a: Universe-pinned local alias of the tight terminal check.
    - b: Universe-pinned local alias of the tight terminal check.
- **1.00** `Spartan.Spec.Bricks.prependRLCTargetPC` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:281](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L281) vs `Spartan.Spec.Bricks.prependRLCTargetWTPC` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:38](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L38)
    - a: The honest RLC-target adapter pinned to the concrete oracle-interface universe used by the current a
    - b: The honest RLC-target adapter pinned to the concrete oracle-interface universe used by the current a
- **1.00** `Spartan.Spec.foldl_add_eq_sum` [ArkLib/ProofSystem/Spartan/FirstSumcheckMulVec.lean:36](../../../ArkLib/ProofSystem/Spartan/FirstSumcheckMulVec.lean#L36) vs `Sumcheck.Spec.SingleRound.foldl_add_eq_sum` [ArkLib/ProofSystem/Sumcheck/Spec/SimpleRoundCoherent.lean:78](../../../ArkLib/ProofSystem/Sumcheck/Spec/SimpleRoundCoherent.lean#L78)
    - a: A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
    - b: A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- **1.00** `Spartan.Spec.foldl_add_eq_sum` [ArkLib/ProofSystem/Spartan/FirstSumcheckZeroEval.lean:39](../../../ArkLib/ProofSystem/Spartan/FirstSumcheckZeroEval.lean#L39) vs `Sumcheck.Spec.SingleRound.foldl_add_eq_sum` [ArkLib/ProofSystem/Sumcheck/Spec/SimpleRoundCoherent.lean:78](../../../ArkLib/ProofSystem/Sumcheck/Spec/SimpleRoundCoherent.lean#L78)
    - a: A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
    - b: A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- **1.00** `StirIOP.MultiRound.TightnessCore.msgAns_zeroMsgs` [ArkLib/ProofSystem/Stir/CheckingRbrTightnessCore.lean:220](../../../ArkLib/ProofSystem/Stir/CheckingRbrTightnessCore.lean#L220) vs `Whir302Checked.msgAns_allZero` [ArkLib/ProofSystem/Whir/CheckedObliviousness.lean:55](../../../ArkLib/ProofSystem/Whir/CheckedObliviousness.lean#L55)
    - a: Every oracle answer of the all-zero messages is `0`.
    - b: Every oracle answer of the all-zero messages is `0`.
- **1.00** `StirIOP.MultiRound.askList` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:157](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L157) vs `Whir302Checked.askList` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:102](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L102)
    - a: Monadic map over a list with definitional `nil`/`cons` equations (avoiding `List.mapM`'s tail-recurs
    - b: Monadic map over a list with definitional `nil`/`cons` equations (avoiding `List.mapM`'s tail-recurs
- **1.00** `StirIOP.MultiRound.askMsg` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:148](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L148) vs `Whir302Checked.askMsg` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:56](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L56)
    - a: Query the `j`-th prover message oracle at a vector position.
    - b: Query the `j`-th prover message oracle at a vector position.
- **1.00** `StirIOP.MultiRound.chalFE` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:127](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L127) vs `StirIOP.MultiRound.chalFERep` [ArkLib/ProofSystem/Stir/RepWire.lean:175](../../../ArkLib/ProofSystem/Stir/RepWire.lean#L175)
    - a: Read the field element off a (length-`1`) vector challenge.
    - b: Read the `s`-th field element off a (length-`t`) vector challenge.
