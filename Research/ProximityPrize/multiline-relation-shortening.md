# Multi-line relation rank and shortening

This research result narrows the affine-head incidence route in issue #164.
The Lean module proves the global rank-to-shared-support bridge and its affine
code-head application. The exact probes test stronger numerical consequences
whose universal counting arguments remain handwritten below. No new production
threshold, sponsor-equivalence theorem or matching bounds are claimed.

## Kernel-checked statements

The module is `Frontier/_IncidenceDependencyArithmetic.lean` in namespace
`ProximityGap.IncidenceDependencyArithmetic`. It imports Mathlib only and has no
dependency on PR #224. Its twenty-one exported theorems are audited in the focused
workflow. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.

Let `W_i` be finite-dimensional subspaces of `F^n` supported on `Q_i`. Let `A`
be the kernel of summation from their external product. Write `a_i` for the
dimension of the image of `A` in `W_i`, `h = dim A`, and `Vcore` for the span
of every component of every relation. Then:

1. `relation_core_dimension` proves `dim Vcore + h = sum_i a_i`.
2. `relation_core_shared_support` proves `Vcore` is supported on `S`, the
   coordinates belonging to at least two `Q_i`.
3. `projected_relation_shortening` proves
   `D + sum_i a_i <= card(S) + 3 + h`, provided `sum_i a_i >= h+3`,
   the code has distance at least `D`, and each `W_i <= C + P` with `dim P <= 2`.

The incidence-budget form also proves
`2(D + sum_i a_i) <= sum_i card(Q_i) + 6 + 2h`.
Here the shared-support cardinality is eliminated by double counting its two
required incidences. This is a necessary weighted rank constraint, with the
same rank-activity and received-space hypotheses.

The proof graph is shortened Singleton, received-space shortening, relation-core
support and the exact rank identity, followed by projected-relation shortening.
The rank identity constructs a linear equivalence between the original relation
kernel and the summation kernel on the product of its projection images.

`affine_head_relation_shortening` specializes the result to
`W_i = span(u0-U_i,u1-V_i)`. Code membership of `U_i,V_i` is derived from two
distinct code heads `U_i+a_i V_i` and `U_i+b_i V_i`. The received space is
`span(u0,u1)`, and the support is explicitly the set where either coefficient
differs. The rank-activity condition remains an argument.

`three_head_support_budget` proves `2 card(Q_i) <= 3t` from three distinct
parameters and their actual error sets of cardinality at most `t`. The module
also proves the coordinate arithmetic and finite summation lemma for the earlier
minimal-dependency ledger. Its structural counting inputs remain explicit.

`affine_heads_of_small_error_relation` gives a direct geometric transfer.
For actual code heads w_i at parameters gamma_i, let their errors have supports
Q_i of size at most t. If a relation among these errors has every coefficient
nonzero and m*t < 2D, then all heads lie on one code-valued affine line.
Two distinct selected parameters determine its coefficients. The theorem derives
this conclusion from error agreement, the relation and code distance, without a
rank-activity assumption or a received-quotient independence assumption.
At m=4 and 2t<D it rules out a full four-error relation spanning different
head lines. It does not rule out a four-head configuration on one line or a
relation having zero coefficients. Those require their separate geometric caps.

## Exact first-sponsor arithmetic

Both probes use integer arithmetic, with `Fraction` for the weighted cube:

```
python3 scripts/probes/probe_multiline_pair_difference_cap.py
python3 scripts/probes/probe_multiline_triple_anchor.py
```

The literal parameters are `n=1073741824`, `k=536870912`,
`D=n-k+1=536870913`, `t=221512374`. The statements apply to abstract linear
codes under the displayed hypotheses. They do not rely on a small-field transfer
or assert a new Reed-Solomon instance. The comparison floor is the one in #224.

### Pair-difference inequality

Assume the selected error planes are pairwise disjoint and all selected errors
are nonzero. For each ordered pair of different planes and each of the three
selected parameters on the first plane, take the difference of their affine
errors. These are nonzero codewords, giving `3L(L-1)` words of weight at least D.

At a coordinate let `a` be the number of active planes and `k` the number whose
selected parameters include the zero direction. Put `z=L-a`, `e=3a-k`. There
are at least `3z(z-1)+kz` zero differences, so the number of nonzero differences
is at most `B=3L(L-1)-3z(z-1)-kz`. The exact identity

```
(5L-2)e-e^2-2B = (a-k)(3L-3a+k)+2k >= 0
```

holds for `0<=k<=a<=L`. Summation, Cauchy and the total error bound `E<=3Lt`
give `6L(L-1)Dn <= (5L-2)nE-E^2`. For `2t<=n`, this right side is increasing
up to `E=3Lt`. Consequently

```
L(2Dn-5tn+3t^2) <= 2n(D-t).
```

At the literal parameters this forces `L<=6`. The probe checks 47904 coordinate
cases and exact arithmetic, not the universal codeword-counting construction.
Using cap three and disjoint triple blocks gives at most 36 ordered distinct
collinear triples. Substitution in the current cube bound improves the floor
by zero Hamming steps.

### A triple anchor limits the whole family to 26 witnesses

Assume the standard partial-spread/cap-three hypotheses of the full affine
bad-witness model. Fix a three-head line with support `Q`, `q=card(Q)`, and let
`s` denote the number of witnesses outside the line. Each external witness has
a nonzero codeword difference from the line head at its scalar. Its support is
contained in `Q union E_j`, hence

```
card(E_j intersect Q) <= q+t-D.
```

Set `A=D-t`, `B=n-D`. The support budget gives `A<=q<=floor(3t/2)`. Jensen on Q
and its complement bounds the total cubed agreement count below by

```
s^3 (A^3/q^2 + B^3/(n-q)^2).
```

Indeed, if the average error mass in Q is `a<=q+t-D`, the lower expression is
`(q-a)^3/q^2 + (n-q-t+a)^3/(n-q)^2`. It decreases up to `a=tq/n`.
The literal inequality `n(q+t-D)<=tq` therefore allows substitution of the
error cap. The resulting expression decreases up to
`q=n(D-t)/(n-t)`, beyond the maximum allowed q. Thus its minimum occurs at
`qmax=floor(3t/2)`.

The outside-family cube deficit from pair-union lower bounds and disjoint
cap-three blocks is at most `3t s^2+(D-t)s`. For

```
gain = A^3/qmax^2 + B^3/(n-qmax)^2 - B
```

we obtain `gain*s^2 <= 3t*s+(D-t)`. Exact rational arithmetic gives `s<=23`,
hence at most 26 witnesses in a family containing a triple line. In particular,
an overbudget family of at least `n+1` witnesses would contain no triple lines.
The universal partial-spread and cube transfer into these inputs have not yet
been formalized in this module. The probe is an exact numerical certificate
for the displayed reduction, not a kernel-checked canonical witness bound.

## Remaining production obligations

- Connect extraction of the entire canonical bad-witness family to the module,
  including the independent-received-quotient case and rank activity.
- Formalize pairwise disjointness and the nonzero difference-codeword counts.
- Formalize the universal weighted two-region cube transfer above.
- Bound the remaining family outside triple lines. Even the line-free cube
  bound leaves the comparison floor at `221512374/1073741824`.

This contributes the structural linear algebra and reproducible exact research
reductions to #164. It does not close that issue or claim a SlopCash award.

## Verification

The focused hosted workflow runs both independent probes and checks the Lean
source with `lake env lean`, followed by an exact twenty-one-declaration axiom
audit. Local builds are unnecessary. The module is also imported by the
research umbrella for normal repository validation.
