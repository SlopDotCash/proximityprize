# Rate-quarter predecessor: abstract incidence barrier and divided-difference rank invariant

## Status

This note separates two statements that must not be conflated.

1. **Abstract barrier, proved probabilistically:** the currently extracted
   agreement-set, pair-core, fresh-petal, root-cap, and source-line packing
   constraints admit `N+1` events at the literal P1 parameters.  Those
   constraints alone therefore cannot prove the desired `#bad <= N` bound.
2. **Polynomial realizability, checked on one support miniature:** the finite
   abstract witness below cannot be realized by nonjoint Reed--Solomon
   explanations for any of 18 tested full label assignments over three smooth
   domains.  A six-label subsystem is exhaustive in two labels over `F_193`.
   These exact ranks support, but do not prove, a label-uniform theorem.

This is not a Reed--Solomon counterexample, not a proof of the predecessor
bound, and not an unconditional delta-star pin.  The durable contribution is
the identification of a missing global algebraic invariant: the rank of a
support-dependent divided-difference/Vandermonde operator.

The reproducing probe is

```text
scripts/probes/probe_rate_quarter_p1_abstract_incidence_rank.py
```

## 1. The abstract two-point-line model

Let `A_i` be the agreement set selected for event `i`.  Give every unordered
pair `{i,j}` its own source line and define its core by

```text
D_ij = A_i intersect A_j.
```

No source line contains a third selected event.  This synthetic model
automatically has the following properties.

* The two fresh petals `A_i \ D_ij` and `A_j \ D_ij` are disjoint.
* If `|A_i|,|A_j| >= T`, then inclusion-exclusion gives

  ```text
  2T - |D_ij| <= N.
  ```

  Thus the exact two-point line-packing inequality holds whenever
  `|D_ij| <= T-2`.
* Cores of two adjacent pair-lines meet in a triple event intersection.
  Cores of two disjoint pair-lines meet in a fourfold intersection, which is
  contained in a triple intersection.  Hence a uniform triple cap `K-1`
  supplies the usual distinct-line root cap.
* The pair-partition identity is exact: `C(M,2)` two-point lines contribute
  `2 C(M,2)=M(M-1)` ordered pairs.

A distinguished near-code direction can also be included abstractly.  Fix a
coordinate set `R` of size `A1star+1`, declare it to be the agreement set of
that direction, give every pair-line a distinct direction whose agreement set
is `D_ij`, and require

```text
|R intersect D_ij| <= K-1.
```

This retains the root-cap consequence of the structured-direction branch but
does not impose simultaneous polynomial interpolation.

### Exact finite certificate

At the exact `m=4` values for `N,K,z,T`, with the P1 direction cutoff
rounded to `A1star=20`,

```text
N=64, K=16, z=34, T=z+2=36, M=65, A1star=20,
```

the probe embeds 65 deterministic 64-bit masks and verifies:

| Quantity | Exact result |
|---|---:|
| event size | `36` for all 65 events |
| coordinate multiplicity | `33..40` |
| pair-core range | `14..24` |
| triple-intersection range | `3..15` |
| two-point packing left side | `48..58 <= 64` |
| structured direction size | `21` |
| `R`--pair-core intersection range | `1..13` |
| thin pairs with core `<16` | `12` |
| thin-graph clique number | `2` |
| two-point source lines | `2080` |

The integral five-set forcing inequality is satisfied with margin

```text
20T - (6N + 20(K-1)) = 36 > 0.
```

Thus the large-overlap graph condition is not merely satisfied; its thin
complement contains no triangle.  Nevertheless `M=N+1`.  The certificate
hash, using little-endian 64-bit masks in event order, is

```text
4786879f2d5063f9894067cd55a313b60bcbf601eb469d640d806149f61bcfb7
```

## 2. Literal P1 probabilistic countermodel

The miniature is not a small-parameter accident.  At the literal values

```text
N = 2^30,
M = N+1,
K = 2^28,
T = 592794966,
A1star = 327272220,
```

fix `R` with `|R|=A1star+1` and independently include each coordinate in each
event set with probability

```text
p = 9/16.
```

The relevant means are

```text
E|A_i|                 = 603979776,
E|A_i intersect A_j|   = 339738624,
E|A_i intersect A_j intersect A_k| = 191102976,
E|R intersect A_i intersect A_j|   = 26509049901/256.
```

All four means have linear margin from their forbidden thresholds.  Hoeffding
plus a union bound over all events, pairs, and triples gives the following
base-10 logarithms for the failure contributions:

| Failure event | `log10` upper bound |
|---|---:|
| some `|A_i| < T` | `-101188.906` |
| some pair core exceeds `T-2` | `-51802263.483` |
| some triple intersection reaches `K` | `-4837666.778` |
| some `R`--pair-core intersection reaches `K` | `-72154697.990` |

The total failure probability is therefore below `10^-101188`.  In
particular it is strictly below one, proving existence of an integral family
with all four properties and `M=N+1`.  The exact five-set forcing margin is

```text
20T - (6N + 20(K-1)) = 44739276 > 0.
```

Assigning every pair to its own two-point source line now satisfies all of the
abstract conditions listed above.  Consequently those listed incidence axioms,
together with universal finite-set identities, do not entail `#bad<=N`.  This
does not rule out an additional inequality whose validity depends on polynomial
realizability rather than on the abstract sets alone.

The construction deliberately does **not** claim that these sets are zero
patterns of Reed--Solomon explanations.

## 3. The missing global interpolation invariant

For actual decoded polynomials `q_i`, scalar labels `gamma_i`, and a received
stack `(u0,u1)`, agreement at coordinate `x` means

```text
q_i(x) = u0(x) + gamma_i*u1(x).
```

Therefore, if `S_x={i:x in A_i}`, the values `q_i(x)` restricted to `S_x`
must be affine in `gamma_i`.  Choose two anchors `a,b in S_x`.  Every other
`i in S_x` obeys the second divided-difference equation

```text
(gamma_b-gamma_i) q_a(x)
+ (gamma_i-gamma_a) q_b(x)
+ (gamma_a-gamma_b) q_i(x) = 0.                 (DD_xabi)
```

Write every `q_i` in the degree-`<K` monomial basis.  Equations `(DD_xabi)`
over all coordinates form a block-Vandermonde linear operator.  Its obvious
kernel consists of the globally joint pencils

```text
q_i = a + gamma_i*r,       deg(a),deg(r)<K.
```

Quotient this `2K`-dimensional kernel by gauging `q_0=q_1=0`.  The exact
finite certificate then has

```text
rows = sum_x (|S_x|-2) = MT-2N = 2212,
columns = (M-2)K = 1008.
```

The probe performs modular row reduction on the actual order-64 multiplicative
subgroup in each field, first for consecutive pairwise-distinct labels and then
for five deterministic random distinct-label assignments per field:

| Field | Rows | Columns | Rank | Nullity |
|---:|---:|---:|---:|---:|
| `F_193` | 2212 | 1008 | 1008 | 0 |
| `F_257` | 2212 | 1008 | 1008 | 0 |
| `F_449` | 2212 | 1008 | 1008 | 0 |

These are exact finite-field computations, not floating-point ranks.  For the
tested consecutive labels, every polynomial realization of the required
incidences lies in the globally joint pencil.  Every coordinate belongs to at
least 33 event sets, so two distinct labels then force `(u0(x),u1(x))` to equal
that pencil at every coordinate, contradicting event nonjointness.  All 15
additional full-size trials also have rank `1008` and nullity zero.  For the
first six events, fixing labels `0,1,2,3` and exhausting all `35,532` ordered
distinct choices of the final two labels over `F_193` always gives full gauged
rank `64`.  Rank could still depend on the remaining labels or field/domain;
these computations are not a uniform theorem.

## 4. Consequence for the exact-pin programme

The source directions of different pair-lines cannot be assigned
independently.  They are secants of one common polynomial point family and
obey the cocycle

```text
q_i-q_j + q_j-q_k + q_k-q_i = 0,
```

together with degree-`<K` interpolation across every coordinate.  Pairwise
root caps retain only a small shadow of this simultaneous constraint.

A direct replacement for the four-pencil extraction target is therefore:

> classify the nonzero **degree-`<K`** kernel of the support-dependent
> divided-difference operator at `M>N` and agreement threshold `T`, modulo the
> global pencil.

An injectivity theorem would immediately rule out an over-budget nonjoint
family.  A weaker theorem showing that every nonzero kernel vector creates a
joint event or a favorable four-pencil cover would also discharge the same
predecessor residual.  The matrix has a Vandermonde tensor structure, so
GM-MDS, matroid-union, or determinant-selection methods are more directly
aligned with the missing information than another second-moment inequality.

The degree restriction is essential.  The unrestricted two-anchor kernel is
never rigid once a third label exists: the polynomial vanishing on the whole
finite domain has degree `N`, evaluates to zero in every operator row, and can
be placed in one non-anchor component.  This is formally refuted and repaired
by `DegreeAnchoredKernelRigid` in
`Frontier/_SupportDividedDifferenceUnrestrictedKernelRefuted.lean`.  At P1,
the decoded degree is `<K<N`, so this counterexample is excluded from the
corrected source space rather than ignored.

The first rank bootstrap is also formal.  A component is forced to zero when
it shares at least `K` support coordinates with two already-zero components;
iterating this along any well-founded parent ranking proves the corrected
degree-restricted rigidity.  Thus one concrete sufficient target is a
two-parent coverage ordering of the decoded labels.  Whether every
over-budget P1 support family contains such an ordering remains open.

The rank data above is evidence for this route only.  It checks one support
family and three small smooth primes, with partial rather than complete label
exhaustion.  It establishes neither label-uniform rank for the full miniature
nor a universal rank theorem at the prize prime.

## 5. Reproduction

Run:

```bash
python3 scripts/probes/probe_rate_quarter_p1_abstract_incidence_rank.py
```

The probe verifies the embedded mask hash and all finite incidence statistics,
performs the 18 full-size exact modular ranks and the `35,532`-case six-label
exhaustion, and recomputes the literal-P1 Hoeffding ledger.  NumPy is the only
non-stdlib dependency.

Related interfaces and barriers:

* `docs/kb/deltastar-466-rate-quarter-saturated-predecessor-reduction-2026-07-10.md`
* `Frontier/_SupportDividedDifferenceOperator.lean`
* `Frontier/_SupportDividedDifferenceUnrestrictedKernelRefuted.lean`
* `Frontier/_P1RateQuarterProjectiveExtremeZeroSplit.lean`
* `Frontier/_P1RateQuarterAgreementOverlapGraph.lean`
* `Frontier/_P1RateQuarterForcedSecantMatching.lean`
* `Frontier/_FSMA_SecondMomentPairPartition.lean`
* `Frontier/_P1RateQuarterPredecessorGenericSplit.lean`
