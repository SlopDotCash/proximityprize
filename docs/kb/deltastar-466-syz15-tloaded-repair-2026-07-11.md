# δ* / #466 — SYZ15: the T-loaded interface repair (BCIKS20 §5 branch handoff)

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ15TLoadedInterfaceRepair.lean`
Status: LANDED, axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`.

## The problem (recap)

SYZ14 (`_SYZ14BCIKS57Chunk2.lean`) reduced the whole [BCIKS20] Claim 5.7 per-cell disc-locus
package to a single named branch residual `HenselBranchSupply`, whose γ-representative field is
the **ground-line** identity

    hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp.

`ToMathlib/GenuinePpolyConverter.lean` (FINDING F6, `not_hrepG_of_two_le_natDegree`) proves this
is **unsatisfiable for `2 ≤ H.natDegree`**: `coeff 0 (polyToPowerSeries𝕃 H Ppoly)` sits on the
ground `F[Z]`-line while `coeff 0 (gammaGenuine) = α₀ = T/W` is off it. So the literal
`HenselBranchSupply`/`PlaceCurveSupply`/`DiscLocusCellData` are **vacuous at every monic curve of
interest** (`d_H = 2` is the in-tree regime). The package composed, but its terminal input was
empty — a satisfiability hole, not a `sorry`.

## The trace (why the repair is shallow)

Following `hrepG` down the constructor chain:

    DiscLocusCellData.hrepG
      → CellPackage.ofSurfaceRootDiscLocus  (CellPackageSupplyShrink.lean)
      → CellPackage.ofSurfaceRootShared
      → CellPackage.ofSurfaceRoot          (Hab25JohnsonPackageSupply.lean)

`ofSurfaceRoot` uses `hrepG` **exactly once**, in the `htail` leg, via

    Claim510SlicedComposition.gammaGenuine_eq_trunc_of_decoded_sliced … hrepG …
      → GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc … hrepG …

Every other occurrence of `Ppoly` is the numeric budget `Ppoly.natDegree` inside `hbig`. The
converter **already** ships the satisfiable replacement for that single consumer:
`GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected`, which takes the T-loaded
`hrepT : polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine` and tail index `max (deg P₀)(deg P₁)`.

**Shallowest correct level = the `htail` derivation.** No rework of Hab25's `CellPackage` *structure*
is needed (its `htail` field is a plain proof term); we only needed a T-loaded *smart constructor*
producing that same structure. Hab25JohnsonPackageSupply.lean was NOT edited.

## What was proven (all in the new file, all axiom-clean)

1. `gammaGenuine_eq_trunc_of_decoded_sliced_T` — T-loaded twin of the sliced truncation capstone.
   Proof: `hvanish_of_decoded_sliced … (max P₀.natDegree P₁.natDegree)` fed into
   `gammaGenuine_eq_trunc_of_graded_disc_corrected`. This is the core mathematical repair.
2. `CellPackage.ofSurfaceRootT` — T-loaded smart constructor producing a genuine `CellPackage`
   (verbatim `ofSurfaceRoot`, `htail` routed through (1), `hbig` budgeting `max (deg P₀)(deg P₁)`).
   This is where **satisfiability is restored**.
3. `DiscLocusCellDataT` (SYZ8 twin, `(Ppoly,hrepG)` → `(P₀,P₁,hrepT)`) + `CellPackage.ofDiscLocusDataT`.
4. `CellPackageSupplyDiscLocusT` + `cellPackageSupply_of_discLocusT : … → CellPackageSupply` —
   re-bases the entire Johnson floor lane on the **satisfiable** T-loaded form (feeds every existing
   consumer of `CellPackageSupply`, incl. `JohnsonDischargeStatement` and the `(1−ρ)/3 → 1−√ρ` jump).
5. `branch_field_gap_at_monic_quadratic` — non-vacuity: at monic `d_H = 2`, given the truncation
   identity `γ = trunc k γ`, the ground field is EMPTY (F6) while the T field is INHABITED
   (converter Claim 5.9 closure). Direct proof the repaired field escapes the SYZ14 obstruction.
6. `HenselBranchSupplyT` (SYZ14 twin) + `discLocusCellDataT_of_henselBranchT` — the branch residual
   assembled into `DiscLocusCellDataT` with `root` derived via `DecodedRootSupply.rootDecoded`.

## Non-vacuity evidence

`branch_field_gap_at_monic_quadratic` is the honest witness: it exhibits, at the in-tree monic
quadratic regime, the exact contrast — `hrepG_unsat_of_two_le_natDegree` (empty) vs
`exists_corrected_representative_of_monic_natDegree_le_two` (inhabited, with `[0,k)` coefficient
support). The only hypothesis is the truncation identity `γ = trunc k γ`, which is the Claim 5.8
counting content (see residual below), not part of the representative obstruction.

## Honest residual (named, mechanical)

The SYZ11–13 **carrier** structures (`PlaceCurveSupply`, `GradedYRootSupply`, `DiscBudgetSupply`,
`MatchingFoldSupply`, `HeavyPinSupply`) still carry the ground `(Ppoly, hrepG)` pair as a
pass-through field. **None uses it semantically** — the only semantic consumer is the `htail`
derivation, now repaired. Producing their `(P₀, P₁, hrepT)` twins is a purely mechanical field
rename (no new mathematics). Named residual: **`SYZ11-13 T-carrier rename`**.
`discLocusCellDataT_of_henselBranchT` therefore assembles `DiscLocusCellDataT` directly from the
branch residual + C4/C5/C6 numeric data, bypassing those pass-through carriers.

Also unchanged (pre-existing residuals, not touched here):
- the Claim 5.8 truncation identity `γ = trunc k γ` ab initio (finite coefficient support / counting);
- the #138 ground X-degree budget (`degreeX P₀/P₁` bounds), not produced by the converter;
- monic `d_H ≥ 3` per-coefficient T-form (span dichotomy) — open; non-unit leading coeff — false.

## Program scoreboard (BCIKS20 §5 branch lane)

- SYZ8: disc-locus reduction of the Johnson residual — LANDED (ground).
- SYZ11–13: C2→C6 interface stack composition into `DiscLocusCellData` — LANDED (ground, but
  terminal input `hrepG` was F6-empty).
- SYZ14: reduction to the single `HenselBranchSupply` residual — LANDED; flagged the F6 vacuity.
- **SYZ15 (this note): the F6 vacuity is REPAIRED.** The satisfiable T-loaded interface chain
  (`gammaGenuine_eq_trunc_of_decoded_sliced_T` → `ofSurfaceRootT` → `DiscLocusCellDataT` →
  `ofDiscLocusDataT` → `cellPackageSupply_of_discLocusT`) drives the named `CellPackageSupply`
  residual from **satisfiable** cell data, and the branch residual `HenselBranchSupplyT` assembles
  into it. The Johnson floor lane is now conditioned on a genuinely inhabitable §5 branch supply.

The open §5 mathematics is unchanged in *kind* (produce, over a large cell, `H`, `x₀`, the Y-root
divisor `w`, the disc/matching/heavy loci, and the T-loaded γ-representative). What SYZ15 fixes is
that the *interface* the producer must hit is now non-empty.
