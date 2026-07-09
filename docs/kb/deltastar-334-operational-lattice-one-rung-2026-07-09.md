# Delta-star operational/lattice one-rung bridge (2026-07-09)

## Result

The exact relationship between the operational threshold and the faithful lattice threshold is
now formalized in
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_KKH26InteriorCeilingLatticeBridge.lean`.

Suppose `0 < s <= n`, every real radius `delta < s/n` is good
(`epsMCA C delta <= epsilon*`), and the boundary `s/n` is bad
(`epsilon* < epsMCA C (s/n)`). Then:

* the operational supremum is `mcaDeltaStar C epsilon* = s/n`;
* the boundary is not itself good;
* the faithful lattice threshold is the preceding index `s - 1`.

The combined theorem is
`mcaDeltaStar_and_mcaThreshold_eq_pred_of_good_below_bad_at_lattice`. Its operational half
uses `MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump`; its discrete half uses downward
closure and `mcaThreshold_unique`. No supremum argument is duplicated in the new bridge.

The four-rate aggregator
`mcaPrizeLatticeResolved_of_good_below_bad_at_lattice` packages four instances of this pattern
directly into `mcaPrizeLatticeResolved`.

The corollary
`not_nonempty_GrandMCAResolution_of_good_below_bad_at_lattice` also proves that no
`GrandMCAResolution C epsilon*` can encode this jump. A proposed cutoff at or above `s/n`
contradicts the bad boundary by monotonicity; a cutoff below `s/n` has a larger good radius
between it and the boundary, contradicting the resolution's maximality field. This formally
closes the old T2 modeling loophole for F4129-style and KKH-style unattained jumps.

## KKH26 index

For the KKH26 parameters

```text
n = 2^mu * m
delta0 = 1 - r / 2^mu,
```

the bad boundary is exactly

```text
delta0 = (n - r*m) / n.
```

Thus the two threshold values are deliberately different:

```text
operational mcaDeltaStar = (n - r*m) / n
lattice mcaThreshold.val = n - r*m - 1.
```

The KKH specialization is
`kkh26_mcaThreshold_eq_pred_ceiling_of_bad`. The endpoint-bad input is supplied by
`kkh26_epsMCA_lower_bound` whenever the target budget lies strictly below the KKH26 bad-scalar
mass.

This one-rung distinction is not cosmetic. An interior `GrandMCAResolution` requires its stated
boundary to be good, so it cannot represent this unattained jump. The operational supremum and
the faithful maximal-good lattice index are the appropriate objects.

## Exact-rate enlargement

The original KKH capstone is written for

```text
evalCode g n ((r - 2) * m).
```

`Ownership.evalCode_eq_rsCode` identifies degree at most `d` with Reed--Solomon dimension
`d + 1`. Hence the KKH dimension is

```text
k_original = (r - 2) * m + 1.
```

Taken literally, this has the `+1 mod m` mismatch previously noted against an exact dyadic
prize dimension. However, that is not the largest code supported by the KKH witness.
`SubCeilingLadder.subceiling_epsMCA_lower_bound` already proves the same witness spread for
every degree `D` in the full window

```text
(r - 2) * m <= D < (r - 1) * m.
```

The endpoint

```text
D = (r - 1) * m - 1
```

has Reed--Solomon dimension exactly `(r - 1) * m`. The gap-expansion codeword still has degree
at most `(r - 2)*m`, while the direction has degree `(r - 1)*m` and therefore cannot agree with
any endpoint-code polynomial on `r*m` points. The new exact-rate wrappers are in
`Frontier/_KKH26ExactRateCeiling.lean`.

At formal prize rate `rho_j = 1 / 2^(j+1)`, choose

```text
r - 1 = 2^mu / 2^(j+1).
```

Then `(r - 1)*m = n/2^(j+1)` exactly and the bad boundary is

```text
1 - r/2^mu = 1 - rho_j - 1/2^mu.
```

When `2^mu = Theta(log n)`, this is the intended `Theta(1/log n)` gap below capacity.

The current degree-decoupled theorem inherits the original size hypothesis
`p > (2^mu)^(2^(mu-1))`.  It is therefore an exact-rate structural bridge, **not yet a deployed
`p < 2^256` prize ceiling** (already `2^mu = 128` asks for `p > 2^448`).  The polynomial-field
KKH/TZ route uses the separate collision-resultant nondivisibility theorem.  A corresponding
degree-decoupled `of_not_dvd` consumer still has to be proved before the exact-rate enlargement
can be advertised in that regime.

The basic sign-subset theorem assumes `r <= 2^(mu-1)`, so this direct endpoint covers the
formal rates `1/4`, `1/8`, and `1/16`. At rate `1/2`, the exact choice is
`r = 2^(mu-1)+1`, one past that range. `KKH26StratifiedSpread.kkh26_stratified_count` already
supports the full range `2 <= r <= 2^mu` and has nonzero strata beyond the half-way point; a
degree-decoupled stratified wrapper is the remaining packaging opportunity for the half-rate row.

## Verification

```text
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_KKH26InteriorCeilingLatticeBridge.lean
```

passed on 2026-07-09.  In `_KKH26ExactRateCeiling.lean`, the degree-window, witness-spread,
and operational-ceiling theorems elaborated and printed axiom-clean.  The final
`exactRate_evalCode_eq_rsCode` proof was then simplified, but its post-edit whole-file rerun is
pending repair of a concurrently deleted shared `MCALowerBound.olean`; do not yet cite that last
identity as kernel-checked.  The successfully audited theorems use only the repository-standard
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.
