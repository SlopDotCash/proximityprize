# Rate-quarter predecessor: maximal-minor ideal certificate

## Status

The support-dependent rank route now has an axiom-clean algebraic consumer which can use any finite
family of maximal minors, including all of them, rather than betting on one distinguished GM-MDS
minor.  It matches the finite probe evidence, where individual minors vanish at some distinct-label
assignments but three adjacent minors have no common zero in one finite label sweep.

Formal kernel:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MaximalMinorIdealCertificate.lean
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SupportDividedDifferenceMaximalMinorBridge.lean
```

This is a reduction, not an exact delta-star pin.  To use it, the remaining producer task is to
prove the stated ideal certificate for the full symbolic operator of every surviving P1 support
family, or prove an additional theorem reducing that full-operator obligation to smaller
restrictions.  A distinct-label common zero of all maximal minors of a full operator in the
relevant target field would instead refute universal full rank for that support family.

## Certificate

Let `M` be a rectangular matrix over a commutative coefficient ring `R`, with columns indexed by
the gauged polynomial coefficients.  For each square row selection `s` in a supplied finite
family, write `D_s` for the corresponding maximal minor.  Suppose

```text
delta^e = sum_s c_s * D_s.
```

For any ring specialization `phi : R -> E` into a field such that `phi(delta) != 0`, at least one
specialized `D_s` is nonzero.  Its square submatrix has injective `mulVec`, hence the entire
specialized rectangular matrix has injective `mulVec` and full column rank.

The file proves this in three reusable steps:

```text
exists_map_generator_ne_zero_of_pow_mem_span
mulVec_injective_of_submatrix_det_ne_zero
mulVec_injective_of_maximalMinor_certificate
```

For the divided-difference application, `R` is a polynomial ring in the scalar labels and `delta`
is their Vandermonde product.  Every injective label assignment keeps `delta` nonzero.

The symbolic specialization layer is also complete:

```text
vandermondeProduct
vandermondeProduct_ne_zero
symbolicVandermonde
eval₂Hom_symbolicVandermonde
mulVec_injective_of_symbolicVandermonde_certificate
```

Thus evaluating the symbolic Vandermonde is formally connected to the concrete finite product,
and label injectivity automatically discharges its nonvanishing.  The companion bridge now
constructs the exact concrete gauged coefficient matrix and proves that its injectivity implies
`DegreeAnchoredKernelRigid`.  It also composes a symbolic certificate with an explicit
specialization equality.  A future P1 producer must still construct a symbolic lift of that
concrete matrix, prove the specialization equality, and construct the polynomial Bézout identity;
the coefficient reconstruction and injectivity-to-rigidity plumbing are complete.

## Why a family of minors is necessary

The existing finite support probe reports successive common-zero counts `189 -> 1 -> 0` for three
adjacent maximal minors in its `F_193` six-label sweep.  This is consistent with the behavior that
an ideal certificate would enforce and shows why those individual fixed minors are insufficient.
It does not prove that the localized maximal-minor ideal is the unit ideal: absence of common
finite-field rational zeros in one sweep is not a polynomial Bézout certificate.

## Exact remaining statement

For each surviving P1 support family, let `M_support` be its full symbolic gauged degree-`<K`
block-Vandermonde operator.  Construct an exponent and coefficients proving

```text
Vandermonde(labels)^e in ideal(all maximal minors of M_support).
```

The concrete `M_support` is now `gaugedCoefficientMatrix`: its columns are non-anchor
`(label, Fin K)` pairs, and `gaugedCoefficientMatrix_mulVec_gaugedCoefficientVector` identifies its
action exactly with the degree-restricted gauged `supportDividedDifference` operator.  The theorem
`degreeAnchoredKernelRigid_of_gaugedCoefficientMatrix_injective` closes the concrete matrix-to-kernel
step, while `degreeAnchoredKernelRigid_of_symbolicVandermonde_certificate` closes the conditional
symbolic consumer.  What is not constructed is a P1 symbolic lift, the proof that it specializes to
this concrete matrix, or the maximal-minor Bézout certificate.

Such a certificate gives universal full column rank for that fixed support family.  To close the
predecessor residual, one must also cover every over-budget nonjoint support family and connect the
resulting injectivity to the existing event contradiction.

`_P1RateQuarterSmallSubsetRankLocalization.lean` proves only that the combinatorial Hall budgets
are automatically safe outside the remaining singleton and pair cases.  It does not prove that
certificates for those restricted suboperators imply full rank, or ideal membership, for the full
operator.  Using symbolic elimination only on those small restrictions therefore requires an
additional explicit-domain GM-MDS or local-to-global determinantal theorem.  Alternatively, one
can construct the full-operator certificate directly.  A common zero of all full-operator maximal
minors away from the Vandermonde locus decisively refutes this universal-rank route for that support
family.

## Singleton leaf minor

`_ScaledVandermondeMinor.lean` closes the algebra of a singleton elimination leaf.  It defines

```text
scaledVandermonde(node,weight) = diagonal(weight) * vandermonde(node)
```

and proves that its determinant is `(product weight) * det(vandermonde node)`.  Distinct domain
nodes and nonzero row weights therefore give an injective coefficient block.  For a
divided-difference singleton leaf, each weight is a difference of two anchor labels, so label
injectivity supplies its nonvanishing even when the anchor pair varies with the coordinate.

This does not triangularize the global matrix by itself.  Other polynomial components occurring
in the selected rows must already be eliminated, or placed compatibly in a block-triangular
maximal minor.  The remaining singleton-side object is an elimination ordering or matroid
matching, not Vandermonde algebra.

### Two-anchor elimination ordering is not universal

`_TwoAnchorBootstrapFirstStepNoGo.lean` isolates a sharp obstruction to the most direct
triangularization.  At a minimal positive rank, every strictly lower-rank parent has rank zero and
therefore is one of the two gauge anchors.  Hence the usable-coordinate set for the first new
component is contained in its fixed triple intersection with those anchors.  If that triple has
cardinality below `K`, the required `K` roots cannot be obtained and the bootstrap cannot start.

Generic support families can have every distinct triple overlap below `K` while satisfying the
global Hall budgets; this is also the regime targeted by the existing abstract-incidence
countermodels.  Thus coordinate-by-coordinate two-parent bootstrap is not a universal route from
Hall safety to full rank.  A viable proof must permit simultaneous/block elimination, a genuinely
global maximal minor, or an ideal certificate involving several minors.

### Unique support matching: valid criterion, wrong granularity for dense blocks

`_UniqueMatchingMinor.lean` proves a clean simultaneous determinant producer: if exactly one
permutation in a square minor avoids zero entries, the Leibniz expansion has one surviving term,
so nonzero matched entries imply a nonzero determinant.  This requires no sequential bootstrap.

However, the same file proves the exact dense `2 × 2` obstruction.  If all four entries are
nonzero, both the identity and transposition matchings survive, so support-level uniqueness is
impossible.  Each P1 polynomial component contributes a dense Vandermonde block on the nonzero
roots-of-unity domain.  Therefore a raw bipartite unique-matching theorem cannot certify the
actual minors: it throws away the algebraic cancellation control supplied by the Vandermonde
determinant.  A viable simultaneous criterion must treat whole Vandermonde blocks as matroid
elements, or return to the multi-minor ideal certificate.

## Validation

```text
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MaximalMinorIdealCertificate.lean
```

passes; all seven audited declarations depend only on the standard axiom-clean set.

The scaled-Vandermonde companion also passes `pg-iterate.sh`; all four audited declarations depend
only on the standard axiom-clean set.

The maximal-minor bridge passes `pg-iterate.sh`; its coefficient reconstruction, concrete-matrix
consumer, and symbolic-certificate consumer depend only on the standard axiom-clean set.

The two-anchor first-step no-go passes `pg-iterate.sh`; both audited declarations depend only on
the standard axiom-clean set.

The unique-matching companion passes `pg-iterate.sh`; its determinant producer and dense-block
no-go are axiom-clean.

## Exact tensor/maximal-recoverability formulation

`_SupportDividedDifferenceCoefficientFactorization.lean` proves the coefficient-level identity
behind the probe matrix.  Every degree-`<K` divided-difference row is

```text
sum_{d<K} dividedDifferenceCoeff(d) * domain(x)^d.
```

Equivalently, it is a local label-parity functional tensored with the Vandermonde row
`(1,x,...,x^(K-1))`.  The degree-`<K` and raw-natural-degree forms are both axiom-clean.

The local functional is now explicit as the sparse `labelParityVector` supported on the row's
three labels.  The file proves both local parity checks exactly:

```text
sum_j labelParityVector(j) = 0
sum_j label(j) * labelParityVector(j) = 0.
```

It also proves `dividedDifferenceCoeff_eq_labelParity_dotProduct` and the fully concrete
`dividedDifferenceAt_eq_sum_parity_dotProduct_mul_pow`.  Thus the local space is formally wired to
the parity-check side of the dimension-two Reed--Solomon code in the label variable, rather than
only described heuristically.

The coordinate-local submodule `localParitySpace` is defined as the span of all concrete triple
row vectors at that coordinate.  The bridge is two-sided:

```text
q in ker(supportDividedDifference)
  iff
for every coordinate x and ell in localParitySpace(x),
  ell dot (q_j(domain(x)))_j = 0.
```

This is theorem `mem_ker_iff_forall_localParity_measurement_eq_zero`, with separate forward and
reverse declarations.  Consequently the Tanner/tensor-code formulation now has exact semantics,
not merely a sufficient relaxation of the original operator kernel.

`_TensorRowSpanCriterion.lean` packages the exact sufficient property.  If

```text
span_x { ell tensor V(domain(x)) : ell in localParity(x) } = full coefficient dual,
```

then every coefficient array killed by all local measurements is zero; equivalently, identical
measurement syndromes imply identical coefficient arrays.  This is the block-level
maximal-recoverability condition respected by the dense Vandermonde blocks.

The P1 projected Hall inequalities are necessary dimension inequalities for this span equality,
but no implication from Hall safety to tensor-span fullness is claimed.  Such an implication would
assert maximal recoverability for every Hall-admissible Tanner/product-code topology and is false
in that generality.  For the explicit roots-of-unity domain, proving this tensor span is precisely
the remaining algebraic problem, equivalent in finite dimension to a nonzero maximal minor and
captured uniformly by the Vandermonde-saturated maximal-minor ideal certificate.

Both factorization and tensor-span files pass `pg-iterate.sh`; their audited declarations are
axiom-clean.

## Gauged tensor target

`_GaugedLocalParityTensorModel.lean` removes the unavoidable global-pencil directions explicitly.
For anchors `a,b`, it defines the remaining label type `NonAnchor a b`, restricts every concrete
`localParitySpace(x)` to those coordinates, and tensors it with the finite Vandermonde row
`domain(x)^d`, `d : Fin K`.

The named proposition

```text
GaugedTensorSpanFull domain label support a b K
```

is exactly “the projected local-parity/Vandermonde tensor rows span the full non-anchor coefficient
dual.”  Every concrete triple row is proved to land in the projected space.  The file also defines
`gaugedCoeffArray` and proves:

```text
GaugedTensorSpanFull + all tensor measurements zero
  -> gaugedCoeffArray = 0,

gaugedCoeffArray = 0 + degree< K
  -> every non-anchor polynomial is zero.
```

Thus the two gauge anchors account for the full `2K` polynomial-pencil kernel rather than asking
an impossible ungauged tensor span to be top.  The remaining wiring lemma is the finite-sum
identity transferring full local-parity measurement vanishing to the restricted tensor
measurement when the two anchor polynomials are zero.  After that identity,
`GaugedTensorSpanFull` directly supplies `DegreeAnchoredKernelRigid`.

The gauged tensor model passes `pg-iterate.sh`; all three audited declarations are axiom-clean.

### Wiring completed

The finite-sum transfer is now proved.  `eval_eq_sum_fin_coeff_mul_pow` converts every degree-`<K`
evaluation to its `Fin K` Vandermonde expansion; `sum_nonAnchor_eq_filter` and
`sum_filter_nonAnchor_eq_sum` remove the two zero anchor summands.  The resulting theorem is

```text
tensorMeasurement_gaugedCoeffArray_eq_parityEvalMeasurement.
```

It is consumed by

```text
polynomial_family_eq_zero_of_gaugedTensorSpanFull
```

which proves, axiom-cleanly:

```text
GaugedTensorSpanFull
+ degree-<K family
+ supportDividedDifference kernel membership
+ q(a)=q(b)=0
----------------------------------------------
q=0.
```

This is the concrete statement of `DegreeAnchoredKernelRigid`; no operator-to-tensor wiring gap
remains.  The sole mathematical producer is now `GaugedTensorSpanFull` for every support family
arising from a hypothetical over-budget P1 predecessor stack (or an alternative event-level
argument avoiding universal span fullness).

## Concrete refutation of coarse maximal recoverability

`_GaugedTensorSpanConcreteRefutedF7.lean` gives an exact six-coordinate, five-label certificate
over `ZMod 7`, with degree bound `K = 2` and anchors `0,1`.  The nodes `1,...,6` and labels
`0,...,4` are distinct, and every label is incident to at least two coordinates.  Nevertheless the
non-anchor family

```text
q₂ = 4 + X,    q₃ = 5 + 6X,    q₄ = 2 + X
```

(with `q₀=q₁=0`) is nonzero, has degree `<2`, and satisfies a supported affine agreement on every
coordinate.  Hence it lies in the support divided-difference kernel.  The completed gauged tensor
wiring then proves

```text
¬ GaugedTensorSpanFull domain label support 0 1 2.
```

The Lean theorem `projectedHall_safe` additionally checks, for every subset `U` of the three
non-anchor labels, the exact local codimension-two budget inequality

```text
2 * |U| <= sum_x min (|support(x) intersect U|) (|support(x)| - 2).
```

This closes the tempting route “distinct scalars + all projected Hall budgets imply maximal
recoverability.”  Crucially, this is not a P1 event counterexample: a successful producer must
exploit additional predecessor/event geometry, or prove span fullness only for the narrower family
of supports actually realizable by P1.
