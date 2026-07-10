# Delta-star rate quarter: thickened isolated-fibre upper bound (2026-07-10)

## Status

> **Superseded later on 2026-07-10.**  The private-thickening endpoint below
> is a valid intermediate construction, but it is not the strongest endpoint.
> A coordinated common-factor / multi-hole trade amplifies it to agreement
> `592,794,965` while retaining `n+2` bad scalars, giving the stronger radius
> `480,946,859 / 1,073,741,824 = 43/96 + 1/(3n)`.  See
> `deltastar-466-rate-quarter-common-factor-amplifier-2026-07-10.md` and
> `_RateQuarterCommonFactorOwnershipAmplifier.lean`.  The earlier claim in
> this note that common factors categorically cannot improve the construction
> was false because it held the hole count fixed.

The smooth three-line construction is not confined to the last lattice point
below radius `1/2`.  At the first certified prize prime it can be thickened for
`(m-1)/3` lattice steps and still beats the exact `n`-challenge budget.

Put

```text
m = 2^26,
n = 16m = 2^30,
k = 4m = 2^28,
r = (m-1)/3 = 22,369,621.
```

Then there is an explicit received pair with at least `n+2` nonjoint bad
scalars at agreement threshold

```text
t = 2k+r+1 = (25m+2)/3 = 559,240,534.
```

The corresponding bad radius is

```text
delta_bad = 1-t/n
          = (23m-2)/(48m)
          = 23/48 - 2/(3n)
          = 514,501,290 / 1,073,741,824.
```

Thus the first-prime operational rate-quarter threshold satisfies
`deltaStar <= delta_bad`.  The complete connector now lands in
`_P1RateQuarterScaleBadCount.lean` and `_P1RateQuarterScaleFinalConsumer.lean`.
Lean checks the billion-scale domain parametrically: the `N-1` covered
coordinates give injective labels `gamma=-x`, the three hole labels are
injective and disjoint by their `N`th powers, and all `N+2` labels fire the
literal `mcaEvent`.  The resulting operational upper bound is unconditional
and contains no named residual.

The principal final theorems are

```text
badScalar_filter_card_ge_N_add_two
firstPrime_rateQuarter_mcaDeltaStar_le_delta
rateQuarter_mcaDeltaStar_le_twentyThree_over_fortyEight_correction
```

Their axiom audits contain no `sorryAx`; only `propext`, `Classical.choice`,
and `Quot.sound` occur.

## Thickening the old hole

The original construction has three cores `D_i` of size `8m=2k`, whose union
has size `15m`, and an uncovered `m`-point fibre `H0`.  On `H0` the three line
factors have distinct constant values `t_i`.

Choose disjoint subsets

```text
R_1, R_2, R_3 subset H0,
|R_i| = r,
H = H0 \ (R_1 union R_2 union R_3).
```

Because `m=3r+1`, the residual hole `H` is a singleton.  Assign the received
pair on `R_i` to polynomial line `i` and enlarge

```text
D_i' = D_i union R_i.
```

Then

```text
|D_i'| = 8m+r = t-1,
|D_1' union D_2' union D_3'| = 15m+3r = n-1,
|H| = 1.
```

Every covered coordinate `x` is missed by at least one source core.  If it is
owned by line `j` and source line `i` misses it, the old witness remains

```text
gamma = -x,
q(X) = f_i(X)(X-x).
```

At `x`, both sides vanish:

```text
u0(x)-x*u1(x) = x*t_j-x*t_j = 0 = q(x).
```

The distinct values `t_i` show that a transferred point is a genuine mismatch
for every other source line.  Hence the `t-1` core plus `x` is a nonjoint
`t`-agreement witness.  The `n-1` covered coordinates give `n-1` distinct
safe labels `-x`.

The one remaining hole point keeps the three old Möbius labels `c_i*x`.  The
already checked P1 certificates

```text
c_i^n != 1,
(c_i/c_j)^m != 1
```

put those labels outside the smooth domain and separate them from one another.
The final count is therefore

```text
(n-1) + 3 = n+2.
```

More generally, thickening by any `0 <= s <= (m-1)/3` gives

```text
core size       = 8m+s,
threshold       = 8m+s+1,
residual hole   = m-3s,
bad labels      = (15m+3s) + 3(m-3s) = 18m-6s.
```

## Refutation loop

The small `F_97`, `mu_32`, `[32,8]` counterexample has `m=2`.  It cannot move
one point into each of three cores, which explains why its exact
Guruswami--Sudan census has no list element at agreement `18`: that finite
example is sharp locally but does not predict the prize-scale lattice.

A common factor by itself, with the hole count held fixed, does not improve
the challenge count: every new common root is dead.  However, the stronger
categorical conclusion originally written here was false.  Two dead common
roots can be paid for by turning one singleton coordinate into a new isolated
hole.  The ownership budget changes by `-2 + 3 = +1` relative to those three
coordinates, and the exact coordinated trade keeps the global count at
`n+2` while increasing every core.  Iterating this trade to the degree limit
produces the superseding `43/96 + 1/(3n)` construction cited above.

The next possible improvement must enlarge *pairwise but not all-line* core
overlap.  The present `mu_16` seed has three pair blocks of size `3m`.  In a
three-line primitive cluster, pair blocks as large as `k-2` would move the
construction toward the combinatorial limiting radius `5/12`; whether the
smooth dyadic domain admits such a split-locator triangle is a genuine
cyclotomic `S`-unit problem.

Exact searches performed so far:

* `mu_16` has 160 disjoint collinear cubic-locator triples; the universal seed
  is one of them.
* `mu_16` also has quartic triples, but their degree lifts to `k`, too large for
  the primitive direction `(X,1)`.
* Doubling the cubic seed to `mu_32` and appending one separate root to each
  block has no solution.  In fact the coefficient comparison explains this:
  three linearly dependent degree-six polynomials can remain dependent after
  separate linear multiplication only when the appended roots coincide.
* An exhaustive `F_193` search over all degree-seven blocks of the structured
  form “four-coset + antipodal pair + singleton” found no disjoint locator
  triangle among 268,255,680 exact affine tests.
* All 72 degree-four boundary triangles on `mu_16` survive the cross-prime
  check.  After lifting them to degree eight on `mu_32`, neither a common
  divided difference nor a common polar derivative produces three disjoint
  split degree-seven images.  Exhausting all 50 lifted boundary directions
  against all `C(32,7)=3,365,856` locator points finds 48 two-point collision
  lines, but no three-point locator line at all.
* Four split-cubic polynomial lines on `mu_16` exist abundantly, but their six
  pair-agreement budgets total only `18` base incidences.  Even the optimal
  collision partition gives average core density at most `33/64`, below the
  three-line thickened density `25/48`.

These negative searches do not prove optimality.  They isolate the next target:
either construct a larger dyadic split-locator triangle, or prove that the
`3m` universal pair blocks are extremal in the P1 cyclotomic field.

## Reproducible artifacts

* `scripts/probes/probe_rate_quarter_prize_p1_isolated_counterexample.py`
  now checks both the original `9n/8` half-predecessor count and the maximal
  thickening arithmetic (`n+2` at the displayed threshold).
* `scripts/probes/probe_rate_quarter_smooth_next_lattice_gs.py` is the exact
  small-field agreement-18 census.
* `scripts/probes/probe_rate_quarter_mu16_locator_sizes.py` exhausts equal-size
  locator triangles on small dyadic groups.
* `scripts/probes/probe_rate_quarter_locator_doubling_extension.py` checks the
  failed `mu_16 -> mu_32` one-root extension.
* `scripts/probes/probe_rate_quarter_mu16_cubic_four_clique.py` checks four-line
  cubic cliques and their collision partitions.
* `scripts/probes/probe_rate_quarter_mu32_structured_locator.cpp` performs the
  268-million-test structured degree-seven search.
* `scripts/probes/probe_rate_quarter_locator_degree_lowering.py` and
  `scripts/probes/probe_rate_quarter_mu32_boundary_direction_lines.cpp` test
  the degree-lowering/boundary-direction escape routes.
