# Issue #464: MacMahon margin-encoding gate

Date: 2026-06-26.

Status: **encoding-only unless a new fiber budget is proved**, not a delta-star proof.

External source: arXiv:2606.27323, "Amplified moments of the Riemann zeta function"
<https://arxiv.org/abs/2606.27323>.

## Thesis

The issue's D3 lead proposed importing the matrix-pair / prescribed-margin technology behind
amplified zeta moments.  The appeal is real: the paper proves asymptotic formulae for two-piece
amplified second and fourth moments of zeta, then uses them to obtain lower bounds for joint zeta
moments consistent with random-matrix predictions.  The combinatorial constant in that world can
be viewed through weighted matrix-pair counts with row/column margins.

For #464, the analogous hope is:

```text
wraparound defect W_r(p)
  = weighted count of matrix pairs with prescribed margins
  = constant term / MacMahon Omega expression
  <= prize budget.
```

The gate is that the first two equalities are only an encoding.  If all weights are nonnegative,
then a margin decomposition is a reindexing of the same count until it supplies one of the
following load-bearing inequalities:

```text
sum_over_margins fiberMass(m) <= B_prize
```

or a uniform fiber cap plus a margin-count bound strong enough that

```text
#margins * cap <= B_prize.
```

Without that inequality, the margin polytope can have the right shape and still hide a huge fiber
over one margin.

## Lean Surface

New in
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_D4MacMahonMarginEncodingGate.lean`:

```lean
EncodesByMargins
bound_of_margin_encoding_and_budget
total_bound_of_uniform_margin_cap
one_heavy_margin_refutes_support_only
same_margin_shape_allows_bound_and_spike
```

The positive theorem is intentionally tautological: once an exact margin encoding is given, the
prize bound follows exactly from a margin-side total budget.  The countermodels are the point:
even a one-point margin space can carry mass `B + 1`, and the same margin shape supports both a
bounded statistic and a spike.

## Verdict

The MacMahon/matrix-pair language remains useful as a bookkeeping layer for the wraparound defect,
especially if it exposes a hidden signed cancellation or a sharp finite-field fiber cap.  But as a
plain nonnegative margin count, it does not evade the already-landed moment ladder.  A winning
variant must prove a new beyond-diagonal fiber-mass inequality at `r ~ log q`; otherwise the
MacMahon expression is only a change of coordinates for the Paley/DC-subtracted Wick wall.
