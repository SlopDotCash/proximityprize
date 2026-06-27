# Issue #464: folded-FRS capacity route pin

Date: 2026-06-26.

Status: **route pin**, not a plain-RS delta-star proof.

## Thesis

The latest #464 "ignore Paley" sweep recommended banking the folded-RS/subspace-design
capacity-MCA route.  On this branch, that route is already present under the current file names:

- the GK16/T2.18 folded-RS subspace-design substrate is proved in `SubspaceDesign.lean`,
  `GK16FrsTransport.lean`, and `GK16Admissible.lean`;
- the T4.14/GG25 MCA capacity adapter is in `CapacityBounds.lean`;
- the order/inter-orbit, coset-separation, and GR08 geometric-domain front doors are in
  `CapacityBoundsAdmissible.lean`;
- the single remaining paper input is the public T4.13 residual
  `gg25_subspaceDesign_epsMCA_residual`, exposed in `CapacityBoundsProofs.lean`.

This is Paley-free because it is a folded/subspace-design theorem, not a theorem about the
unfolded smooth multiplicative-subgroup RS domain.  It therefore does not prove the prize
delta-star statement for plain RS.  The plain-RS subspace-design bypass is structurally blocked by
`Frontier/R2UnfoldedDesignFloor.lean`: for `s = 1`, the forced lower bound
`tau(r) >= (m - 1) / m` keeps the CZ25 route far below the prize capacity window.

## Lean Surface

New in `ArkLib/Data/CodingTheory/ProximityGap/CapacityBoundsAdmissible.lean`:

```lean
frs_epsMCA_capacity_gg25_frontier_of_orderOf_ge_of_inter_eta
frs_epsMCA_capacity_gg25_frontier_of_orderOf_ge_of_cosetSep_eta
frs_epsMCA_capacity_gg25_frontier_of_geomDomain_eta
```

These are compatibility wrappers for callers that want the older raw-bound
`FRSEpsMCACapacityGG25Frontier` API rather than the normalized
`FRSEpsMCACapacityGG25TLeFrontier` API.  They compose the existing direct constructors

```lean
frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_inter_eta
frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_cosetSep_eta
frs_epsMCA_capacity_gg25_tleFrontier_of_geomDomain_eta
```

with `FRSEpsMCACapacityGG25TLeFrontier.toFrontier`, so the raw `hBound` field is not a new
assumption; it is derived by the checked arithmetic bridge
`frs_capacity_realBound_of_t_le`.

The public Prop endpoints already available in the same file are:

```lean
frs_epsMCA_capacity_gg25_of_orderOf_ge_of_inter_eta
frs_epsMCA_capacity_gg25_of_orderOf_ge_of_cosetSep_eta
frs_epsMCA_capacity_gg25_of_geomDomain_eta
```

The T4.13-backed proof-supply wrappers in `CapacityBoundsProofs.lean` are:

```lean
frs_epsMCA_capacity_gg25_proven_of_t413
frs_epsMCA_capacity_gg25_proven_of_t413_cosetSep
frs_epsMCA_capacity_gg25_proven_of_t413_geomDomain
frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413
frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413_cosetSep
frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413_geomDomain
frs_epsMCA_capacity_gg25_frontier_proven_of_t413
frs_epsMCA_capacity_gg25_frontier_proven_of_t413_cosetSep
frs_epsMCA_capacity_gg25_frontier_proven_of_t413_geomDomain
```

Thus the folded-FRS route's current formal contract is:

```text
T4.13 subspace-design MCA residual
+ proved folded-RS T2.18/CZ25-profile substrate
+ eta coupling and t <= 2 / eta arithmetic
=> folded-RS MCA up to capacity.
```

This is the correct route to cite for "folded/subspace-design capacity-MCA is banked modulo
T4.13".  It should not be cited as a Paley bypass for plain smooth RS.

Follow-up: `FoldingTransferNoGo.lean` now also names the exact downward transfer predicate

```lean
PlainToFoldAgreementTransfer
UniversalPlainToFoldAgreementTransfer
```

and proves

```lean
not_plainToFoldAgreementTransfer_of_A_le_N_mul_d_of_T_pos
```

The first predicate is alphabet-specific; the second is the alphabet-uniform theorem shape needed
for a generic folded-to-plain transfer.  The theorem says that no alphabet-uniform positive
folded-orbit agreement threshold follows from any plain agreement threshold at or below the
one-corruption-per-orbit witness `N*d`.  Thus a future unfolding theorem must use stronger
structure than a bare plain-to-fold agreement implication.
