# Rate-quarter predecessor: local divided-difference rigidity

## Status

The one-coordinate algebra of the support-dependent divided-difference operator is now complete
and axiom-clean.  It neither proves nor refutes the predecessor count, but it sharply locates the
remaining information: only the global degree-`<K` coupling can supply rank beyond coordinatewise
affine-stack consistency.

Formal kernel:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/
  _SupportDividedDifferenceLocalRigidity.lean
```

## Exact local theorem

Fix two anchors `a,b` with distinct labels.  For scalar values `v_i`, the row equation

```text
(gamma_b-gamma_i) v_a
  + (gamma_i-gamma_a) v_b
  + (gamma_a-gamma_b) v_i = 0
```

is equivalent to `v_i` lying on the unique affine function of `gamma_i` through the anchor
values.  The file proves both directions and packages simultaneous vanishing as an iff.

The operator-facing theorem `eval_eq_local_affine_of_mem_ker` applies this pointwise to polynomial
evaluations in the existing `supportDividedDifference` kernel.

## Semantic completeness of the local rows

Suppose every coordinate support has two distinctly labelled anchors.  Then

```text
q in ker(supportDividedDifference)
  iff
there exist received rows u0,u1 such that
  q_i(x) = u0(x) + gamma_i u1(x)
on every prescribed support incidence.
```

This is theorem `mem_ker_iff_exists_supportedAgreement`.  The reverse implication reuses the
existing `mem_ker_of_supportedAgreement`; the new forward implication constructs `u0,u1` from the
two-anchor affine interpolants.

## Consequence for the exact-pin route

There is no unextracted local constraint hidden in the divided-difference rows.  Locally, their
kernel is exactly the original affine-stack consistency condition and has the expected two affine
degrees of freedom.  Therefore summing local row counts or reproving local rank cannot discharge
the predecessor residual.

The live target is the genuinely global statement: degree-`<K` polynomials couple evaluations
across coordinates through the block-Vandermonde matrix.  A successful GM-MDS, determinant
selection, or matroid-union argument must prove that this coupling kills every gauged kernel
family (or forces one of the already sufficient structured alternatives).  That global step
remains open; no exact delta-star pin is claimed here.

## First global propagation brick

The companion file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/
  _SupportDividedDifferencePencilPropagation.lean
```

proves a conditional overlap consumer for gluing two candidate polynomial pencils.  Let
`(base0,slope0)` and `(base1,slope1)` have degree `<K`.  If, on `K` injective domain points, their
affine evaluations agree at a supplied pair of distinct scalar labels at each point, then

```text
base0 = base1  and  slope0 = slope1.
```

The two labels may vary with the coordinate.  Consequently the pencils agree at every scalar
label.  The proof first applies affine two-point pinning at each coordinate, then polynomial
interpolation on the `K` points separately to the base and slope.  The fixed-label declarations
are specializations.  The theorem proves sufficiency of this certificate; it neither proves
minimality nor extracts the certificate from the P1 support family.

This advances the global route but does not supply the overlap.  The next combinatorial target is
to extract, from an over-budget predecessor family, a connected collection of local source-pencil
charts whose adjacent charts share two labels across at least `K` domain points, or an equivalent
full-rank minor.  A propagation network covering the family would collapse to one global joint
pencil and contradict the MCA event.

### Exact cardinality obstruction to propagation

The follow-up `_P1RateQuarterPropagationPlotkinNoGo.lean` prevents over-crediting this consumer.
Forced secant cores have weight `K`, but at the exact P1 values

```text
K^2 <= N*(K-1),
2K <= N,
N-2K = 2^29.
```

Thus the second-stage constant-weight Plotkin denominator is nonpositive, and even two disjoint
`K`-cores fit with half the domain unused.  Core cardinalities alone cannot force the `K`-point
overlap consumed by propagation.  This agrees with the existing forced-secant consolidation
ledger: a successful extraction still needs polynomial geometry or the support-dependent
determinant invariant.  The propagation theorem is a reusable gluing brick, not a new unconditional
closure route.

## Validation

```text
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SupportDividedDifferenceLocalRigidity.lean
```

passes, and all five audited declarations depend only on the standard
axiom-clean set `{propext, Classical.choice, Quot.sound}`.

The propagation companion also passes `pg-iterate.sh`; all four audited declarations depend only
on the standard axiom-clean set.

The P1 Plotkin no-go companion passes `pg-iterate.sh`; all three arithmetic declarations report
only `propext`.
