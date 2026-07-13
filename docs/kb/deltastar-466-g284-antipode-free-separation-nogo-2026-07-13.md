---
id: deltastar-466-g284-antipode-free-separation-nogo-2026-07-13
issue: 466
tags: [proximity-gap, delta-star, CORE, sponsor-covariance, polarity, convexity, separation, no-go]
date: 2026-07-13
author: Sol
status: landed
supersedes: []
---

# G284: antipode-free does not imply strict separation

## One-line

G280's sponsor-profile family is antipode-free, so polarity does not algebraically forbid an odd
certificate, but antipode-freeness alone supplies no sign or margin: the exact set
`{(1,0),(0,1),(-1,-1)} ⊂ ℚ²` is antipode-free while its points sum to zero, hence no linear
functional is strictly positive on all of it.

## Frontier context

G280 proved the CORE covariance is an odd real signed pairing,
`B(W,-R)=-B(W,R)`, and its recorded sponsor-profile family contains no exact antipodal pair. This
correctly leaves a sponsor-specific odd certificate logically possible. A tempting strengthening is
that an antipode-free family should lie in some strict positive half-space:

```text
C ∩ (-C) = ∅  ->  exists ell and eta > 0, forall c in C, ell(c) >= eta.
```

That implication is false. Antipode exclusion is only pairwise. Strict separation from zero is a
convex property and requires the stronger premise `0 ∉ convexHull C`, plus a quantitative separator.

## Exact countermodel

Let

```text
C = {(1,0), (0,1), (-1,-1)} ⊂ ℚ².
```

No point's negative belongs to `C`, so `C` is antipode-free. But

```text
(1,0) + (0,1) + (-1,-1) = 0.
```

For every rational linear functional `ell`, linearity gives

```text
ell(1,0) + ell(0,1) + ell(-1,-1) = 0.
```

Therefore the three values cannot all be strictly positive. In particular there are no `ell` and
`eta>0` with `eta <= ell(c)` for every `c∈C`. Geometrically, zero is the equal-weight barycenter of
`C` even though `C` has no antipodal pair.

## Formal payload

`Frontier/_G284AntipodeFreeSeparationNoGo.lean` contains:

- `zero_sum_blocks_positive_linear_separator`, the dimension-free abstract obstruction for any
  rational module;
- `AntipodeFree` and `StrictlySeparated`, the exact two certificate predicates;
- `countermodel_sum_zero` and `countermodel_antipodeFree`, exact certified facts for the three-point
  set;
- `countermodel_not_strictlySeparated` and the packaged
  `antipodeFree_not_imply_strictlySeparated` countermodel.

The result is theorem-level and r-uniform. It is not a finite-depth sponsor census, a weakened CORE
goal, or a wrapper around an open proposition.

## What closes and what survives

- **Closed:** upgrading G280's pairwise antipode exclusion, by itself, into a strict odd separator or
  positive margin.
- **Still possible:** an independently specified arithmetic normal `ell_r` on the actual sponsor
  family, together with a proof of `ell_r >= eta_r > 0` and a comparison
  `|B_r-ell_r| < eta_r`. Such input would establish the missing convex pointedness rather than infer
  it from antipode-freeness.
- **Honest boundary:** no sponsor-prime covariance is bounded here. CORE remains OPEN / ON-BGK.
