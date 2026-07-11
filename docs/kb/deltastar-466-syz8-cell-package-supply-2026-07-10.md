# SYZ8: the disc-locus supply reduction of the Johnson-lane residual `CellPackageSupply` (2026-07-10)

## What `CellPackageSupply` actually is

`CellPackageSupply domain k δ T` (`Hab25JohnsonPackageSupply.lean`) is the **single named
residual** gating the production Johnson floor jump `(1−ρ)/3 ≈ 0.16667 → 1−√ρ ≈ 0.29289`.
As a Prop it reads: for every word stack `u`, every irreducible `R : (F₀[X])[X][Y]`, every
finite set `E` of decoded scalars with a common near-codeword divisor `P γ`, either the cell
is *small* (`E.card ≤ T`) or it carries a per-cell **§5 heavy-agreement package**
(`CellPackage`) — the [BCIKS20] Claim 5.7 data over a large cell:

* the GS place curve `H` (irreducible, positive degree, monic) and its `Hypotheses x₀ R H`;
* the centre `x₀` and the tail-vanishing of the genuine `α`-series;
* the Y-root divisor `w` with `(X − C w) ∣ R` and a rational root `root z` of `H̃'` at each `z`;
* per-coordinate **matching sets** with base agreement, separability, and fold agreement;
* the kill-target weight budget `W` and the cardinality lower bound `W·degH < |matchingSet j|`;
* a heavy **pinning set** `S₀` with base/separability and `max Bw 1 < |S₀|`.

The consumer chain from `CellPackage` down to `JohnsonDischargeStatement` is fully proven and
axiom-clean (`himpr_of_cellPackageSupply`, `johnsonDischargeStatement_of_packageSupply`,
`cell_improvement_of_pinning_package'` → `johnsonNumericBound_holds_of_himpr`). Supply is the
**exact** missing input.

## Verdict: GENUINELY OPEN (not formalizable-known in one pass)

`CellPackageSupply` encodes [BCIKS20] Claim 5.7 — the *production* of the place curve, its
centre, the Y-root divisor, and the disc-non-vanishing matching/heavy loci over a large cell.
This is the heavy algebraic-geometry engine of BCIKS20 §5–§6 (Guruswami–Sudan surface
construction, Newton-polygon/Hensel branch selection, discriminant geometry counting). It is
mathematically known but **not** of one-session formalizable size, and it is not a
plug-a-lemma gap: it is the substantive content of the paper's main technical claim. Faking a
discharge would be dishonest. The honest move is to **shrink the residual** and leave the open
core precisely stated.

## What was landed (SYZ8): the disc-locus reduction, lifted to supply level

`CellPackageSupplyShrink.lean` (#389) already shrank the *per-cell constructor* three ways,
ending at `CellPackage.ofSurfaceRootDiscLocus`, which pins the truncation set to the
discriminant non-vanishing locus, discharges the cover leg (`Finset.mem_filter`), and collapses
the four redundant base/separability legs (`hbaseA/hsepA/hbase₀/hsep₀`) to a single certificate
over the disc locus. SYZ8 **lifts that gain from the constructor to the supply Prop itself**.

New file: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ8CellPackageSupply.lean`
(namespace `BCIKS20.CellPencilJohnson`, then `ProximityGap.ProductionRegime`). Verbatim
statements:

* `structure DiscLocusCellData ... (domain) (k) (δ) (u) (R) (H) [Fact (Irreducible H)]
  [Fact (0 < H.natDegree)] : Type` — bundles exactly the inputs of
  `CellPackage.ofSurfaceRootDiscLocus`. **Strictly smaller surface than `CellPackage`**: no
  free `truncSet`; no `hcover`; base + separability given ONCE over `disc.eval z ≠ 0` (not four
  times over the matching/heavy loci); matching/heavy membership is the local disc-non-vanishing
  statement `∀ j, ∀ z ∈ matchingSet j, disc.eval z ≠ 0` and `∀ z ∈ S₀, disc.eval z ≠ 0`.
* `noncomputable def CellPackage.ofDiscLocusData (d : DiscLocusCellData …) :
  CellPackage domain k δ u R H` — rebuilds the full package field-by-field via
  `ofSurfaceRootDiscLocus`.
* `def CellPackageSupplyDiscLocus domain k δ T : Prop` — the disc-locus supply Prop: every
  cell is small or carries `Nonempty (DiscLocusCellData …)`.
* `theorem cellPackageSupply_of_discLocus (h : CellPackageSupplyDiscLocus domain k δ T) :
  CellPackageSupply domain k δ T` — **the reduction** (via `Nonempty.map ofDiscLocusData`).
* `theorem johnsonDischargeStatement_of_discLocusSupply (hsupply : … →
  CellPackageSupplyDiscLocus domain k δ (max …)) : JohnsonDischargeStatement` — the Johnson
  discharge off the smaller residual.
* `theorem production_good_johnson_of_discLocusSupply (hsupply : … CellPackageSupplyDiscLocus …)
  … : δ ≤ mcaDeltaStar (ReedSolomon.code domain k) εstar` — the production floor jump
  `(1−ρ)/3 → 1−√ρ` conditioned on `CellPackageSupplyDiscLocus` in place of `CellPackageSupply`.

All axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only) — see `#print axioms` block.

## Exact remaining gap to the Johnson floor

Unchanged in mathematical content, sharpened in shape. To land
`firstPrime_rateHalf_ladder_floor_johnson` (floor `0.16667 → 0.29289`) it now suffices to prove

    ∀ n k m …, 2≤k → k+1≤n → 12≤m → δ≤1 →
      CellPackageSupplyDiscLocus domain k δ (killBudget n k m)

i.e. for each *large* cell produce: an irreducible positive-degree monic `H` with its
`Hypotheses`; the graded degree data `D, hd2, hdHD, hD_Rx0, hRgrade` and the `γ`-series
representation `Ppoly, hrepG`; the rational-root section `root`; the Y-root divisor `w` with
`(X−C w) ∣ R`; a nonzero discriminant `disc` with the budget `gradedCardBudget + deg disc < |F₀|`
and single base/separability certificates over its non-vanishing locus; per-coordinate matching
sets living in that locus, folding correctly, with `killBudget·degH < |matchingSet j|`; and a
heavy set `S₀` in that locus with `max Bw 1 < |S₀|`. This is [BCIKS20] Claim 5.7 — **genuinely
open** algebraic geometry, not a Lean plumbing gap.

`discLocus_card_ge` (already in-tree) supplies the counting slack: the disc-non-vanishing locus
has `≥ |F₀| − deg disc` points, so the `hcard`/`hS₀` cardinality legs are *achievable* once the
production geometry is in place.

## SYZ7 map update (item 1)

The SYZ7 map's item (1) "[FLOOR, highest value] Discharge `CellPackageSupply` at production
shape" is now re-based: the residual to discharge is the **strictly-smaller**
`CellPackageSupplyDiscLocus`, with `johnsonDischargeStatement_of_discLocusSupply` /
`production_good_johnson_of_discLocusSupply` as the wiring. The open mathematics (Claim 5.7
surface production) is unchanged; the *interface* an implementor must satisfy is the smaller one.

## Files

* New: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ8CellPackageSupply.lean`
* Consumed: `CellPackageSupplyShrink.lean` (`ofSurfaceRootDiscLocus`, `discLocus_card_ge`),
  `Hab25JohnsonPackageSupply.lean` (`CellPackage`, `CellPackageSupply`,
  `johnsonDischargeStatement_of_packageSupply`), `ProductionRegimeBracket.lean`
  (`production_good_johnson_of_packageSupply`).
