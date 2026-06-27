# Issue #464: every non-Paley angle strategic map

Date: 2026-06-26.

Status: **routing note and transfer-gate audit**, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The latest "ignore Paley" sweep asked whether the plain smooth-domain RS floor can be proved by
leaving the Gauss-period/Paley inequality behind.  The honest answer is now sharper:

```text
For plain smooth-domain RS, every currently viable route either:

1. proves an adjacent theorem for a different code/domain/model,
2. re-enters the same thin-subgroup Gauss-period L-infinity wall, or
3. needs an explicit transfer theorem strong enough to become a new floor proof by itself.
```

This note fills the KB path referenced by issue comment 103.  It does not claim that the sweep
closed the prize; it records where each non-Paley route lands in the current Lean surface.

## Adjacent Wins

The most valuable adjacent route is folded RS / subspace-design MCA to capacity.

Verified sources:

- Jeronimo--Liu--Rajpal, "Optimal Proximity Gap for Folded Reed--Solomon Codes via Subspace
  Designs", arXiv:2601.10047, https://arxiv.org/abs/2601.10047.
- Goyal--Guruswami, "Optimal Proximity Gaps for Subspace-Design Codes and (Random)
  Reed-Solomon Codes", ECCC TR25-166, https://eccc.weizmann.ac.il/report/2025/166/.
- Crites--Stewart, "On Reed--Solomon Proximity Gaps Conjectures", ePrint 2025/2046,
  https://eprint.iacr.org/2025/2046.

In-tree routing:

```lean
gg25_subspaceDesign_epsMCA_residual
frs_epsMCA_capacity_gg25_proven_of_t413
frs_epsMCA_capacity_gg25_proven_of_t413_cosetSep
frs_epsMCA_capacity_gg25_proven_of_t413_geomDomain
frs_epsMCA_capacity_gg25_frontier_proven_of_t413
```

The folded route is Paley-free because it uses the extra folded/subspace-design structure.  It is
not a plain smooth-RS floor proof.  The current KB pin is
`docs/kb/deltastar-464-folded-frs-capacity-route-pin-2026-06-26.md`.

## The Plain-to-Fold Transfer Block

The naive transfer from folded agreement to plain agreement is formally blocked in:

```text
ArkLib/Data/CodingTheory/ProximityGap/FoldingTransferNoGo.lean
```

Existing results:

```lean
foldedAgree_mul_le_plainAgree
folding_transfer_no_go
no_go_concrete
```

This pass added the threshold-level transfer condition and refuter:

```lean
PlainToFoldAgreementTransfer
UniversalPlainToFoldAgreementTransfer
not_plainToFoldAgreementTransfer_of_A_le_N_mul_d_of_T_pos
```

`PlainToFoldAgreementTransfer G N d A T` is the fixed-alphabet missing theorem shape for a
downward transfer: plain agreement at least `A` would have to force at least `T` fully agreeing
folded orbits.  `UniversalPlainToFoldAgreementTransfer N d A T` asks for this over every
nontrivial alphabet.  The one-corruption-per-orbit witness over `ZMod 5` refutes the universal
form for every nonzero folded threshold `T` whenever `A <= N*d`.  Thus folded capacity results
affect the plain prize only after a transfer theorem that survives per-orbit corruption; the simple
agreement-threshold transfer is dead.

## Paley Re-Entries

The non-Paley sweep also reclassified several routes that look different but still consume the
same hard object:

- Domain-blind Krawtchouk/MacWilliams/LP certificates forget the evaluation set.  The no-go surface
  is `Frontier/DelsarteLPNoGo.lean`; see
  `docs/kb/deltastar-464-krawtchouk-lp-certificate-verdict-2026-06-26.md`.
- Effective vertical Sato-Tate/Katz monodromy controls distributional moments only until the
  honest conductor term becomes vacuous.  The gate is
  `Frontier/_C5MonodromyMaxControlScissors.lean`.
- Random-domain and generic-locus theorems need a pointwise transfer to the fixed dyadic smooth
  domain.  The recent gates are `_D4PermutationInsdelRankTransferGate.lean` and
  `_D0HomologicalVanishingTransferGate.lean`.
- Support-ratio, appearance-fiber, and line-list routes now have exact scanner interfaces, but their
  missing estimates are production line-list or appearance-filtered fiber bounds, not a free
  folded/subspace-design import.

## Remaining Positive Shapes

The sweep leaves three honest proof shapes for the plain floor:

1. Prove the thin-subgroup Paley/BGK sup bound directly.
2. Prove a global stack/profile domination theorem that reduces every worst stack to a budgeted
   representative family.
3. Prove a genuinely new plain-to-adjacent transfer theorem stronger than
   `PlainToFoldAgreementTransfer`, strong enough to survive the one-corruption-per-orbit obstruction
   and still preserve the prize radius.

The first is the recognized analytic-NT core.  The second is the current off-BGK structural route.
The third is not impossible in logic, but the threshold version is now refuted, so any future claim
must state exactly what extra structure defeats per-orbit corruption.

## Verdict

This strategic pass does not prove the delta-star floor.  It does prevent a common misread:
folded-RS/subspace-design capacity MCA is a real adjacent theorem and useful for deployment-facing
folded codes, but it is not a Paley bypass for plain smooth-domain RS without an additional
unfolding transfer theorem.  The newly named threshold refuter makes that missing theorem explicit.
