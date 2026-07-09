# ZK payment-channel formalization roadmap

Status: 2026-07-09.  The companion implementation is the git submodule
[`external/zk-payments-confetti`](../../external/zk-payments-confetti), pinned at
`0d13b4211cd6aa76111b8d7b5c9aeb9097cb6e7b`.

## Scope and evidence

The submodule specifies a single-recipient, prepaid ZK payment-channel object
with `Setup`, `Open`, `Spend`, `Redeem`, `Close`, and `Dispute`; it has an
idealized ledger and an RLN-style double-spend/slashing mechanism.  It is not
yet a proof of a deployed protocol or a multi-hop payment-channel network.

The following status is based on the checked source, principally
[`Spec.md`](../../external/zk-payments-confetti/Spec.md),
[`OPEN-PROOFS.md`](../../external/zk-payments-confetti/OPEN-PROOFS.md), and the
Lean modules named below.  The submodule has its own Lean/VCV-io dependency
graph and pins Lean `v4.30.0`; ArkLib is currently pinned to `v4.30.0-rc2`.
Do not merge their Lake configurations without a deliberate version-alignment
task.

## What is already mechanized in the submodule

The ideal state-machine layer proves no overspend (T1), payee and payer balance
security (T2/T3), closure liveness (T5), and a fleet priced-divergence bound
(T6), in `Zkpc/Core/` and `Zkpc/Fleet/`.  The game layer proves a proof-free,
flat-instance session unlinkability theorem with advantage zero (T4), plus the
algebra behind RLN recovery.  It also has a conditional FRAME/T7 bound: if the
adversary's evidence distribution is independent of the hidden secret, its
slash probability is at most `1 / |F|`.

The recent `Zkpc/Games/T4Fires.lean` closes the non-vacuity concern for T4 by
showing a solvent, fresh singleton challenge actually emits a ticket batch.
Refund safety is mechanized for a single channel/close-dispute round.

These statements rely on the model boundary in `Zkpc/Assumptions.lean` and
`Spec.md`: ideal ledger, idealized cryptographic interfaces/random oracles, and
the frozen model choices.  Consequently, this is meaningful protocol-logic
coverage, but it is not a concrete SNARK, signature, Merkle, networking, or
smart-contract verification.

## Reusable ArkLib work

ArkLib contains strong ingredients, but no payment-channel, ledger, escrow, or
payment-network transition system.  The closest assets are:

| Need | Existing ArkLib asset | Gap to payment channels |
|---|---|---|
| Transcript zero knowledge | `ArkLib/OracleReduction/Security/ZeroKnowledge.lean`; Fiat--Shamir transfer and canonical coupling interfaces in `ArkLib/OracleReduction/FiatShamir/HVZKTransferReduction.lean` | Abstract HVZK/FS plumbing; no concrete ticket NIZK, simulator, or reduction against an interactive payment adversary. |
| Commitment and opening security | `ArkLib/Commitments/Functional/Basic.lean` | Generic functional commitment definitions, not the channel's identity/set commitment or deployed commitment scheme. |
| Membership-set soundness | `ArkLib/Commitments/Functional/MerkleTree/Extraction.lean` | Has deterministic position binding and a random-oracle extractability bound; needs adaptation to dynamic roots, membership proofs, and close/dispute semantics. |
| ROM bad-event accounting | VCV-io's query tracking and `StateSeparating/IdenticalUntilBad`, used by ArkLib's Fiat--Shamir/security work | The submodule does not yet encode the FRAME adversary with query bounds or connect its five caches to this machinery. |
| SNARK components | `ArkLib/ProofSystem/`, `ArkLib/OracleReduction/`, `ArkLib/Commitments/` | These prove components and reductions, not a relation/circuit asserting valid payment tickets or an end-to-end NIZK instantiation. |

## What remains for an end-to-end theorem

The work splits into four layers; all are required.

1. **Finish the existing ideal-model theorem.**
   - Discharge O1: prove `zkBridgeObligation` for a concrete full-ticket NIZK
     instance, so real proof-bearing ticket unlinkability is reduced to the
     proof-free T4 game plus the NIZK advantage.
   - Make T7 unconditional for query-bounded adversaries.  Instrument queries
     to `H_a`, `H_e`, and `H_id`, prove identical-until-bad, and obtain the
     advertised `(q_A + q_E + q_Id + 1) / |F|` bound.  This is the highest
     value proof debt.
   - Finish the B/refund obligations: adversary-issued genesis/receipt handling
     (O3), true-count close-view simulation (O4), the full refund cascade, and
     fleet-side refund settlement.

2. **Replace ideal cryptography with concrete assumptions.**
   Specify the ticket relation and a concrete NIZK/SNARK; prove completeness,
   knowledge soundness (or simulation extractability where the settlement
   argument requires it), and zero knowledge.  Bind all public inputs:
   root, epoch, gateway, amount/price, spend index/nullifiers, close state, and
   domain separators.  Instantiate identity and set commitments, Merkle
   membership, signatures/receipts, and collision/PRF/ROM assumptions.  The
   proof must preserve the submodule's session unlinkability game, not merely a
   one-ticket indistinguishability claim.

3. **Connect the model to an executable ledger protocol.**
   Give semantics for transactions and contracts, inclusion/finality/reorgs,
   authorization, timeout scheduling, watcher assumptions, censorship, and
   gateway replication.  Prove a refinement/simulation from implementation
   traces to the ideal `Open`--`Dispute` transition system; prove that
   on-chain verification enforces the exact relation from step 2.  Without
   this, `T1`--`T6` only hold for the ideal ledger.

4. **State the desired system boundary honestly.**
   The current object is single-recipient.  A multi-recipient or multi-hop
   result needs an explicit new ideal functionality and proofs of atomicity,
   route/relationship anonymity, liquidity, concurrent payment behavior,
   and failures/partitions.  This is a definition-design project, not a
   mechanical extension; it reopens the submodule's security-game review.

## Recommended order

1. Port/version-align the submodule only after deciding whether it remains an
   external proof artifact or becomes an ArkLib package.
2. Complete T7's query-bounded identical-until-bad proof using VCV-io.  It is
   self-contained, improves a stated theorem, and exercises the exact random
   oracle infrastructure the final system needs.
3. Define a concrete ticket NIZK and prove O1.  Reuse ArkLib's zero-knowledge
   and Fiat--Shamir interfaces only after fixing the concrete relation and
   adversary interface.
4. Add the ledger/contract refinement and then the refund/fleet closure work.
5. Treat a multi-recipient/network theorem as a separate, reviewed milestone.

## Literature anchors

The protocol shape is closest to [Bolt (Green--Miers,
2016)](https://eprint.iacr.org/2016/701), which gives anonymous payment
channels and game-based anonymity/balance claims.  [zkChannels
(
Akinyele et al., 2021)](https://www.cs.jhu.edu/~akinyelj/publication/2021-preprint-zkchannels)
is a 2PC-based realization direction.  Network privacy introduces materially
different requirements: [Fulgor/Rayo](https://eprint.iacr.org/2017/820),
[AMHL](https://eprint.iacr.org/2018/472), and the repaired
[A2L+/A2L-UC analysis](https://eprint.iacr.org/2022/942) are the relevant
privacy-definition precedents; the latter is a warning that a proved theorem
under an insufficient privacy definition can still admit insecure instances.
For variable-amount hub privacy, see
[BlindHub](https://eprint.iacr.org/2022/1735).  These are paper proofs, not
substitutes for the concrete-to-ideal refinement above.
