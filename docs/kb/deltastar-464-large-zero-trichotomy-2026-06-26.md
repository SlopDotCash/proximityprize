# Issue #464: large-zero trichotomy for the line-list route

Date: 2026-06-26.

Status: critique-and-tool iteration.  This is not a delta-star proof.

## The failed optimistic essay

The previous line-list route had a seductive shape:

```text
bad scalars <= appearing codewords * per-codeword heavy-scalar budget.
```

For nowhere-zero directions this is clean.  For directions with zeros, the corrected per-codeword
denominator is:

```text
support(u1) / (a - #zero(u1)).
```

That looked like a tolerable local repair, but it hid a sharp discontinuity.  When
`#zero(u1) >= a`, the denominator disappears.  If a codeword already agrees with the offset on `a`
zero coordinates, every scalar is bad.  That is not a proof artifact; it is a full-field
saturation mechanism.

The first repair named zero-direction safety.  The second repair named the large-zero safe residual.
The new critique is that even those two names are not enough unless the failure side is exact.

## The new tool

`LineListReduction.lean` now has the subfield-budget trichotomy:

```lean
not_uniformLineBadScalarsBudgeted_iff_eligible_or_unsafe_or_largeZero_safe
```

For `B < |F|`, failure of

```lean
UniformLineBadScalarsBudgeted dom k a B
```

is equivalent to one of three concrete scanner witnesses:

```text
1. eligible overbudget:
   exists u0 u1,
     SupportEligibleLineDirection a u1
     and B < #lineBadScalars(dom,k,a,u0,u1)

2. unsafe zero direction:
   exists u0 u1,
     not ZeroDirectionSafeLine dom k a u0 u1

3. large-zero safe overbudget:
   exists u0 u1,
     not SupportEligibleLineDirection a u1
     and ZeroDirectionSafeLine dom k a u0 u1
     and B < #lineBadScalars(dom,k,a,u0,u1)
```

The converse directions matter.  An unsafe zero direction refutes every subfield-size budget because
it forces `lineBadScalars = univ`.  A large-zero safe overbudget line is therefore a genuinely
different failure mode, not merely "zero saturation in disguise."

## What the PDF/library sweep says

The local library contains 327 PDFs under `/Users/shawwalters/papers/arklib` and the curated
Paley-spectrum corpus under `docs/references/proximity-gap-paley-spectrum/`.  The directly relevant
first-page checks still point the same way:

- BGK gives qualitative subgroup exponential-sum cancellation where Stepanov methods do not apply,
  but not the square-root worst-period estimate needed at the prize scale.
- Heath-Brown--Konyagin is a Gauss-sum theorem for kth powers in the intermediate range, not the
  thin `n = p^(1/4)` endpoint closure.
- di Benedetto et al. explicitly assume subgroup size `> p^(1/4)`; the prize is on the boundary.
- Kowalski's 2024 note is an exposition of BGK, useful for quantifier hygiene but not a new
  exponent.
- Kim--Yip--Yoo supplies shifted-subgroup structure and the Paley-graph conjectural lever, not a
  proved worst-period bound.
- The newer Burgess-type finite-extension papers are about multiplicative character sums over
  boxes.  They do not directly bound the additive Gauss-period sup over one dyadic multiplicative
  subgroup in a prime field.

So the line-list branch is still useful only if it creates a genuinely coding-theoretic obstruction
that bypasses the Paley sup norm.  The trichotomy says exactly what that obstruction has to beat.

## Why this matters

The trichotomy turns "prove the line-list route" into three smaller statements:

```text
A. eligible-direction line-list theorem plus support-fit arithmetic,
B. zero-direction safety,
C. large-zero safe residual bound.
```

Part A may be attacked by affine-subspace list-decoding style arguments.  Part B is a near-code
avoidance theorem on the zero set.  Part C is the new hard case: many zeros, no saturating codeword,
but still too many bad scalars.

The large-zero safe case has the shape of a punctured RS problem.  Delete the zero coordinates.
Every codeword has fewer than `a` agreements on the deleted part, but a scalar can still become bad
by combining some deleted agreements with enough moving-support agreements.  A proof must control a
stratified union over the deleted-agreement count:

```text
t = #zero-agreements(c,u0,u1), 0 <= t < a
need at least a - t moving-support agreements
```

This suggests the next invented tool:

```text
PuncturedZeroStratifiedLineList
```

It should bound, for every large-zero direction, the sum over strata `t < a` of codewords with
exactly `t` zero agreements times their moving-support heavy-scalar budget.  If that tool collapses
to the existing line-list theorem, it is only bookkeeping.  If it proves that high `t` strata have
small codeword multiplicity because the zero set already behaves like a high-rate RS restriction,
then it would be a real off-BGK input.

## Refutation pressure

The proposed tool will fail if one can build an offset `u0` and a large zero set `Z` such that many
RS codewords nearly interpolate `u0` on `Z` without any one reaching `a` points, while the moving
support fibers align across many scalars.  That is exactly what a scanner should now search for:

```text
not support eligible,
zero-direction safe,
bad scalar count > B.
```

If such a witness exists, the line-list route reduces back to global worst-case incidence.  If it
does not, the missing theorem is not a character-sum bound but a punctured near-code packing theorem.
That is the next precise mathematical question.
