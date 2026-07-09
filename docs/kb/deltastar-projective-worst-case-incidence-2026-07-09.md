# The production worst-case incidence core is exactly projective

Date: 2026-07-09

## Result

`ProjectiveWorstCaseIncidence.lean` replaces the affine bad-scalar count by the intrinsic
`|F| + 1`-slot projective census from `MCAProjectiveEquivariance.lean`.  It defines

```text
ProjectiveWorstCaseIncidenceBounded C delta E :=
  forall u, badSlotCount C delta (u 0) (u 1) <= E
```

and proves, for `E < |F|`,

```text
WorstCaseIncidenceBounded C delta E
  <-> ProjectiveWorstCaseIncidenceBounded C delta E.
```

This is an exact equivalence, not an affine-to-projective estimate with an extra slot.

The substrate now also exposes `rowMixSlotEquiv`, the explicit Mobius permutation induced by
an arbitrary invertible `2 x 2` row mix, together with `badSlot_row_mix_iff` and
`badSlotCount_row_mix`.  Thus the projective census is formally independent of the chosen
ordered generators of a rank-two pencil.

## Proof mechanism

The projective census decomposes as the affine bad-scalar count plus an indicator for the
infinity slot.  The easy direction drops that indicator.

For the other direction, suppose infinity is bad.  The affine hypothesis gives at most `E`
bad scalars, and `E < |F|`, so there is a good affine slot `gamma`.  Rebase the row pair by

```text
(u0, u1) |-> (u1, u0 + gamma * u1).
```

The explicit equivalence `rebaseSlotEquiv gamma : Option F ~= Option F` transports every
projective slot and moves the chosen good slot to infinity.  Therefore the projective bad
count is unchanged, while for the rebased pair it equals the entire affine count.  Applying
the universal affine hypothesis to that rebased stack proves the projective budget with no
`+1` loss.

The strict budget condition is used exactly once: to ensure a good affine slot exists.  It is
the relevant regime for normalized error thresholds below one, including the prize budget.

## Sharpness

The boundary section of `ProjectiveWorstCaseIncidence.lean` proves that the strict inequality
cannot be relaxed.  Over `F_2`, the zero code on three coordinates at radius `2/3` has a row pair whose
three projective slots are all bad.  At `E = |F_2| = 2`, every affine census is nevertheless
at most two by cardinality.  Consequently

```text
WorstCaseIncidenceBounded C delta |F_2|
```

holds universally while `ProjectiveWorstCaseIncidenceBounded C delta |F_2|` fails.  The
hypothesis `E < |F|` is therefore sharp, not a proof artifact.

## Operational consumers

The module also proves

```text
epsMCA C delta <= E / |F|
  <-> ProjectiveWorstCaseIncidenceBounded C delta E
```

under the same `E < |F|` condition.  It then supplies:

- a direct projective lower-bound consumer for `mcaDeltaStar`;
- the specialization at budget `E / |F|`;
- `mcaDeltaStar_eq_of_projective_jump`, which gives an exact pin when every radius below
  `delta0` meets the projective budget and `delta0` is its first failure.

The last theorem turns a projective combinatorial jump directly into the operational
threshold, so a future incidence proof does not need to reconstruct affine probability
plumbing.

## Quotient descent and the rank-two core

`MCAProjectiveEquivariance.lean` now proves that translating either row by a codeword preserves
every projective slot and hence the full census.  In particular,

```text
badSlotCount_eq_of_quotient_mk_eq
```

shows that the census depends only on the ordered pair of classes in `(ι -> A) / C`.

`ProjectiveWorstCaseIncidence.lean` then splits the quotient-rank strata.  If the two quotient
classes are linearly dependent, their projective census is at most one.  Consequently, for every
production budget `E >= 1`,

```text
ProjectiveWorstCaseIncidenceBounded C delta E
  <-> the same bound on RowsIndependentModCode pairs only.
```

Thus the universal production condition has no unresolved rank-zero or rank-one part.  Its entire
content lies on genuine two-dimensional quotient pencils.

`ProjectiveRankTwoAPI.lean` connects this campaign predicate to standard Mathlib geometry:

```text
RowsIndependentModCode C u0 u1
  <-> LinearIndependent F ([u0], [u1])
  <-> finrank F (quotientPencil C u0 u1) = 2.
```

Downstream incidence arguments can therefore use the ordinary `Submodule` and `finrank` APIs.

## Exact support-subspace dictionary

`ProjectiveQuotientSupport.lean` packages the remaining event without a choice of pencil basis.
For a coordinate witness set `S`, define

```text
V_S = {e : e vanishes on S}
B_S = image(V_S -> (ι -> A) / C)
P   = span{[u0], [u1]}.
```

The theorem `mcaEventProj_iff_quotientPencilSupport` proves exactly

```text
mcaEventProj C delta u0 u1 alpha beta
  <-> exists admissible S,
        [alpha*u0 + beta*u1] in B_S and not (P <= B_S).
```

The first membership says that the selected projective class has a representative supported off
`S`; the failed inclusion says that the whole pencil is not jointly explainable there.  On the
rank-two stratum, a bad slot is therefore a projective point on the line associated to `P`, selected
by a proper intersection `P ∩ B_S`.  This is an exact theorem-level dictionary, not the missing
incidence estimate.

## Metric and finite-ball forms

`ProjectiveCosetWeight.lean` descends relative distance from a word to its quotient class.  It
proves the unconditional metric envelope

```text
badSlotCount C delta u0 u1 <=
  #{projective slots z : cosetRelWeight C z <= delta}.
```

If the row pair is not jointly close at radius `delta`, the local no-joint clause is automatic on
every admissible witness, and the inequality is an equality.  For independent quotient rows, the
normalized slot map is injective and its image has exactly `|F| + 1` points.  Thus the projective
census is a genuine line intersection count, not a parametrization with repeated quotient points.

`ProjectiveQuotientBall.lean` packages the union of the support subspaces `B_S` as the finite
`quotientSyndromeBall C delta`.  It proves, without an extra hypothesis,

```text
badSlotCount C delta u0 u1 <= projectiveBallIncidence C delta u0 u1.
```

For a `PencilJointFar` pencil, meaning no admissible `B_S` contains the whole pencil, this is an
equality.  The projective incidence splits into its affine chart plus the infinity indicator, and
`affineBallIncidence_spectral` instantiates the generic Fourier identity
`LineIncidenceSpectral.lineIncidence_spectral` on the actual quotient syndrome ball.  This is the
first direct theorem-level bridge from the MCA projective census to that spectral API.

`ProjectiveMetricUnification.lean` proves that the two descriptions and exactness hypotheses are
the same:

```text
q in quotientSyndromeBall C delta
  <-> cosetRelWeight C q <= delta,

PencilJointFar C delta (quotientPencil C u0 u1)
  <-> not jointProximity C (u0,u1) delta,

projectiveBallIncidence C delta u0 u1
  = #{projective slots z : cosetRelWeight C z <= delta}.
```

Thus the conditional metric and finite-ball census equalities are one theorem in two coordinate
systems.  The basis-free condition still does not follow from quotient rank two alone; the
jointly-close branch remains outside the exact line-ball identity and retains the local no-joint
clause from `mcaEventProj_iff_quotientPencilSupport`.

## A necessary no-go

A blanket claim `badSlotCount <= block length` is false.  The axiom-clean theorem
`genericQuotient_epsMCA_lower_bound` in
`Frontier/_GenericQuotientInterpolationSpread.lean` constructs a stack with normalized affine
incidence at least `choose(s,r) / p` on block length `s*m`, whenever
`choose(choose(s,r),2) < p`.  Taking `s=8`, `m=1`, `r=3`, and `p=4129` gives numerator
`choose(8,3)=56`, far above the block length `8` (and `choose(56,2)=1540 < 4129`).

The field-size-free second-moment version gives the broader obstruction
`(M - M^2/p)/p <= epsMCA`.  Any useful projective estimate must therefore exploit the production
budget and the special RS support geometry; projectivity alone cannot force an `O(n)` census.

## What remains open

This result does not prove the production incidence bound.  It identifies the exact object
that must be bounded and removes a chart artifact from that task.

The next unformalized specialization is the MDS/RS circuit dictionary.  For a rank-two quotient
pencil `P`, let `D_P` be its inverse image in the word space, a two-dimensional supercode extension
of `C`.  The support-subspace theorem suggests indexing bad projective labels by low-support,
support-minimal words of `D_P / C`; these are expected to correspond to short circuits after
projecting parity-check columns along `P`.  The shallow support layers admit elementary packing
bounds, but the binding layer can contain many private supports, as the 56-slot construction
demonstrates.  Controlling that deep layer for every smooth-domain RS pencil is the same worst-case
list-incidence wall that remains open.

## Validation

The substrate, downstream equivalence, rank-two reduction, sharpness section, quotient-support
dictionary, metric envelope, quotient-ball spectral bridge, and metric unification typecheck in the
stable Lean overlay.  Every new exported theorem's axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.
