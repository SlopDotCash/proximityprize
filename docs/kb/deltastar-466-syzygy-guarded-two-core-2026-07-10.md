# SYZ wave: guarded two-core and external-anchor pair channels

Date: 2026-07-10.  Scope: coding/syzygy/incidence row (7.1--7.10) of the ten-by-ten assault.

## Verdict

This wave does **not** prove the Paley/BGK sup-norm conjecture and does not close the P1
rate-quarter predecessor.  It produces a new axiom-clean pair-channel classification brick for
the latter:

```text
Frontier/_SYZGuardedKernelTwoCore.lean
```

After the two global polynomial-pencil directions are gauged away, the support of every nonzero
degree-`<K` divided-difference syzygy is a guarded hypergraph two-core.  For a label subset `U`,
the external two-coverage of `j in U` consists of coordinates containing `j` and two distinct
labels outside `U`.  Every such coordinate is a root of the `j` component.  Hence

```text
j in support(q)  ->  externalTwoCoverage(U,j).card < K.
```

The static producer

```text
AnchorAvoidingTwoCoreFree support K a b
```

therefore implies the exact current rank residual

```text
DegreeAnchoredKernelRigid domain support label K a b.
```

This is a useful support certificate but not the genuinely new survivor: it is a static form of
the already-recorded two-parent bootstrap and is too strong for the known miniature.  Indeed, for
`U = univ ∖ {a,b}`, its external two-coverage is exactly the `(a,b,j)` triple core.  Therefore
the `N=64,K=16` abstract family, whose every distinct triple has size at most `15`, fails this
criterion for every anchor pair even though its complete divided-difference matrix was full rank
in the existing probes.

A second, strictly stronger pair guard is also proved.  If a zero external label `r` meets two
components `i,j` on at least `K` common coordinates, interpolation lifts the local row to the
global relation

```text
(label j - label r) * q_i + (label r - label i) * q_j = 0.
```

Two distinct zero external labels `r,s`, each with `K`-coverage of the same internal pair, force
`q_i=q_j=0`; the determinant is

```text
(label j - label i) * (label s - label r) != 0.
```

Thus a nonzero syzygy pair has at most one critical external-anchor channel.  The theorem
`criticalExternalAnchors_card_le_one` packages the literal count.  This is the genuinely new
survivor: it detects pair structure that the vertexwise two-core test does not; no coordinate
needs to contain two zero labels simultaneously.

## Actual SYZ1--SYZ3 branch audit and current gate

The current checkout is at `0611ab30a`, while the completed SYZ chain lives on side refs and the
campaign fork.  Read-only audit of commits `3167ea341`, `0744ce79c`, and `68b0fef67` gives:

1. **SYZ1 -- exact analogue falsifier.**  The executable degenerate-subset channel constructs
   `D` overlapping subsets, each donating `n-t` bad scalars through
   `gamma_x=-(u0-v0)/(u1-v1)`.  Exact `n=32,64` instances exceed the proposed `n` budget.  At
   this stage the production transfer was a precise residual, not yet a Lean refutation.
2. **SYZ2 -- channel formalized at production.**  The per-point `mcaEvent` theorem, family-union
   count, constructed-stack theorem, and RS interpolation uniqueness are axiom-clean.  One
   production degenerate subset gives `520,093,695` bad scalars.  Three-subset additivity was
   isolated as `OverBudgetDegenerateStackExists`.
3. **SYZ3 -- production cap refuted.**  The explicit three-subset stack carries
   `3 * 31 * 2^24 = 1,560,281,088 > 2^30` distinct bad scalars and proves
   `firstPrime_predecessor_cap_refuted`.  Therefore the universal `31/64` predecessor-count
   hypothesis is false.  A valid guard must **charge** the excluded degenerate-pencil fibers; it
   cannot simply delete them.

Downstream side refs SYZ4--SYZ6 turn the same channel into unconditional rate-half ceilings,
ending at

```text
mcaDeltaStar <= 358612991 / 2^30 ~= 0.33398,
```

approaching the channel's `1/3` lattice infimum.  The exact rate-half threshold remains open; the
old `31/64` pin is no longer the gate.  Separately, the literal rate-quarter predecessor remains
the degree-bounded divided-difference/kernel gate attacked by the new pair-channel theorem here.

## Matrix cells 7.1--7.3 audit

These are cells 7.1--7.3 of
`deltastar-466-ten-by-ten-paley-assault-2026-07-10.md`, distinct from the SYZ branch labels above.

1. **SYZ1, guarded predecessor count -- residual with a new exact pair-channel implication.**
   The old prose instruction was to quotient the three-subset/pencil syzygies before counting.  The correct
   quotient is the two-dimensional global polynomial-pencil kernel, already represented by the
   two-anchor gauge.  Static two-core-freeness implies `DegreeAnchoredKernelRigid`, but the known
   all-small-triples miniature refutes this as a universal producer.  The surviving guard is
   instead pairwise: quotient critical three-label channels by their external anchor; each nonzero
   internal pair has at most one critical class.  Missing: charge the subcritical channels and the
   single exceptional class inside every over-budget literal-P1 support family.
2. **SYZ2, distinct witness-codeword count -- structural reduction already exists, no closure.**
   `MCAWitnessSpreadCodeword.badCount_le_witnessCodeword_card` injects bad scalars into distinct
   witness codewords for `delta<1/2` on full-support directions.
   `witnessCodeword_packing_bound` gives the exact zero-coordinate degradation otherwise, and
   `LineListIncidenceMultiplicity` records the complete incidence graph.  The remaining bound on
   the actual line list is itself the list-decoding/prize core; quotienting codewords does not
   bound it.  Pencils can still donate multiple scalars through zero coordinates.
3. **SYZ3, syzygy-module classification -- exact gate, partially sharpened.**
   `supportDividedDifference` is the concrete module map; unrestricted rigidity is refuted by the
   domain-vanishing polynomial; `DegreeAnchoredKernelRigid` is the corrected target.
   `GaugedTensorSpanFull` and maximal-minor certificates are exact equivalent producer surfaces.
   Projected Hall safety alone is refuted over `F_7`.  The new two-core and pair-channel theorems
   classify necessary support geometry of any surviving kernel vector, but do not yet exclude all
   such vectors on literal P1 supports.

## Witness-codeword quotient falsifier and guarded survivor

The exact companion probe is:

```bash
python3 scripts/probes/probe_syzygy_witness_quotient.py
```

with checked output in `scripts/probes/_out_syzygy_witness_quotient.txt`.  It gives three useful
separations.

* **Raw distinct-codeword injection is false.**  In the displayed smooth `RS[32,8]/F_97`
  certificates there are 36 scalar labels but only 33 decoded polynomials.  The displayed
  scalar--codeword witness graph has maximum matching 29; eight labels have the singleton
  neighbour `{0}`, and the zero polynomial certifies 16 labels.  This is an exact Hall
  obstruction for the displayed graph.  The repeated-codeword counterexample itself is
  unconditional; the matching number is not claimed for every possible alternative witness.
* **The failure is production-sized.**  In the P1 common-factor source pencil, the zero polynomial
  symbolically carries `480,946,860` labels.  Thus `#bad <= #distinct decoded witnesses` is not a
  repair of SYZ3.
* **The guarded affine-pencil quotient survives the tested constructions.**  If a pencil has
  common core `D` and every predecessor witness uses at least two fresh coordinates, disjoint
  petals give `L*(T-|D|)+|D|<=N`, hence
  `L<=1+floor((N-T)/2)`.  At the P1 rate-quarter predecessor this is `240,473,430` labels per
  pencil; four pencils contribute at most `961,893,720<N`, with slack `111,848,104`.  This is the
  arithmetic already consumed by the existing guarded four-pencil extraction residual, not a
  proof that every over-budget family admits such a cover.

## Ten coding/syzygy/incidence subangles

| Cell | First decisive object | Audit disposition |
|---|---|---|
| 7.1 Guarded predecessor | Contract the global-pencil kernel and count external-anchor channels | **Survivor / formal brick.** Each nonzero internal pair has at most one critical external channel. Converting this into the event count is open. |
| 7.2 Witness-codeword quotient | Scalar--codeword incidence projection | **Reduction, not closure.** Injective below half on full support; exact packing otherwise; line-list bound remains open. |
| 7.3 Syzygy module | Degree-`<K` kernel modulo pencils | **Survivor / exact gate.** New pair-channel determinant restricts circuits; full classification open. |
| 7.4 Matroid circuit growth | Minimal support of a gauged kernel vector | **Reframed.** Every circuit support is a guarded two-core, but core-freeness is too strong. Ordinary projected Hall/matroid rank is insufficient by the exact `F_7` counterexample. |
| 7.5 Secant defectivity | Plucker determinants of polynomial lines | **No-go alone.** `_R396PolynomialLinePluckerSyzygy` is exact, but the common-locator sunflower saturates its full root budget. Needs the new external-channel input. |
| 7.6 Tensor flattenings | Local parity vector tensor Vandermonde row | **Exact residual.** `GaugedTensorSpanFull` is correctly gauged and fully wired; coarse maximal recoverability is refuted. Explicit P1/event span remains viable. |
| 7.7 Internal projection | Two-anchor gauge/contraction | **Valid only internally.** Changing the code/domain proves nothing; the existing gauge is the admissible quotient and is already used by this wave. |
| 7.8 List recovery | Coordinate affine lists / appearing codewords | **Known reduction.** It can consume a sharp RS list-recovery theorem, but no available theorem has the production parameters; generic list recovery rephrases the line-list wall. |
| 7.9 Rank-stratified incidence | Stratify by guarded core and external-anchor channels | **New actionable stratification.** A nonzero pair has at most one critical external channel. A quantitative census over actual P1 supports is open. |
| 7.10 Puncture and lift | Peel a vertex with `K` external-two roots | **No-go as a universal route.** The all-small-triples miniature blocks the first step for every anchor pair. Pair-channel/block elimination is required. |

## Exact implication versus residual

Proved implications:

```text
nonzero gauged degree-<K kernel
  -> anchor-avoiding guarded two-core

AnchorAvoidingTwoCoreFree
  -> DegreeAnchoredKernelRigid

two distinct K-covered zero external anchors for one nonzero pair
  -> contradiction

number of K-covered zero external anchors for one nonzero pair
  <= 1.
```

The first displayed producer is already known to be unavailable on the all-small-triples
miniature.  The live producer is instead:

```text
over-budget nonjoint P1 predecessor event
  + nonzero gauged kernel support U
  -> there exist distinct i,j in U and distinct r,s outside U
       with K <= |common(i,j,r)| and K <= |common(i,j,s)|
  -> contradiction.
```

The middle producer is false for abstract incidence/Hall data: the `N=64` certificate has every
triple below `K`, hence every critical-anchor set is empty.  It must use actual event and decoded
polynomial structure.  If two-critical forcing is also too strong there, the next precise target
is decomposition of `q` into one-external-anchor star generators, since the proved count says
each internal pair supports at most one critical star.  A favorable star is the degenerate
collinear/pencil family controlled by the existing mismatch charge.

Nothing in this file supplies the
asymptotic nonprincipal Gauss-period maximum bound, so there is no claimed Paley implication.

## Literature cross-check

The higher-order-MDS literature validates the tensor/matroid vocabulary but does not discharge
the fixed roots-of-unity specialization here.  The generalized GM-MDS theorem proves higher-order
MDS behavior for generic polynomial-code columns and its list-decoding applications use suitable
or random puncturings; it does not say that this prescribed literal-P1 divided-difference topology
is maximally recoverable.  Likewise, the hypergraph-orientation proofs of capacity concern random
evaluation choices, while MR tensor-code regularity is known to be sufficient only in restricted
topologies.  Relevant primary sources:

* Brakensiek--Dhar--Gopi, [Generalized GM-MDS: Polynomial Codes are Higher Order
  MDS](https://arxiv.org/abs/2310.12888).
* Alrabiah--Guruswami--Li, [Randomly punctured Reed--Solomon codes achieve list-decoding capacity
  over linear-sized fields](https://eccc.weizmann.ac.il/eccc-reports/2023/TR23-125/) (including the
  hypergraph-orientation formulation).
* Brakensiek--Gopi--Makam, [Lower Bounds for Maximally Recoverable Tensor Codes and Higher Order
  MDS Codes](https://arxiv.org/abs/2107.10822).
* Lovett, [A proof of the GM-MDS conjecture](https://eccc.weizmann.ac.il/report/2018/047/).

## Validation

```bash
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZGuardedKernelTwoCore.lean
```

passes.  All eight audited declarations use only `propext` in the printed output (hence are within
the campaign's standard axiom-clean set); there is no `sorry` or new `axiom`.
