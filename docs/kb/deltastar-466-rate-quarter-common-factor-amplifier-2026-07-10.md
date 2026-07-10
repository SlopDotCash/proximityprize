# Delta-star rate quarter: common-factor ownership amplifier (2026-07-10)

## Status

The maximally thickened smooth rate-quarter construction admits a second,
much larger amplification.  At the first prize prime `P1`, an exact compressed
certificate now gives `n+2` nonjoint bad scalars at agreement threshold

```text
t = 592,794,965 = (53m-2)/6,
n-t = 480,946,859 = (43m+2)/6,
```

where

```text
m = 2^26,
n = 16m = 2^30,
k = 4m = 2^28.
```

Thus the certified bad radius is

```text
delta_bad = (n-t)/n = 43/96 + 1/(3n).
```

The general amplifier arithmetic, polynomial identities, degree bounds,
root preservation, fresh-witness identity, scaled-hole agreement, nonjointness,
Möbius injectivity, and one-hole finite-field avoidance are kernel checked in

```text
Frontier/_RateQuarterCommonFactorOwnershipAmplifier.lean.
```

The actual P1 threshold/radius arithmetic and all six unsafe-coset
identifiers are kernel checked in

```text
Frontier/_P1RateQuarterCommonFactorArithmetic.lean.
```

An independent executable check is

```text
scripts/probes/probe_rate_quarter_common_factor_trade.py.
```

The last composition into the full P1 received stack and operational
`deltaStar` ledger is not yet landed.  Accordingly this is an exact executable
P1 certificate plus axiom-clean abstract Lean infrastructure, not yet a single
kernel theorem asserting the operational upper bound.  It is an upper
construction only; it does not supply the matching lower bound needed to solve
the prize.

### Discovery chain now formalized

The amplifier emerged from a sequence of exact obstructions rather than an
unguarded construction guess.

* `_RateQuarterNextLatticeFourCoreBarrier.lean` proves that three next-lattice
  one-fresh cores force a pair intersection at least `3m+1` by
  inclusion--exclusion.  It also proves by the sharp constant-weight Plotkin
  inequality that any four old-size cores force the same overlap once
  `r>=13`.
* `_RateQuarterNextLatticeSplitLocatorNecessity.lean` proves that such a pair
  intersection forces a monic split factor of degree at least `3m+1` in both
  decoded-line difference components, leaving quotient degree `<m`.  Three
  pair factorizations obey a polynomial-coefficient locator-cycle syzygy.  It
  explicitly does **not** infer constant-coefficient locator collinearity.
* `_RateQuarterNextLatticeOwnershipLedger.lean` proves the exact identity
  `B+A=n+2H`.  At the next core threshold, either one proper pair cell grows
  past `3m`, or the named `MultiHoleTripleTradeResidual` holds:
  `H>=2`, `H+2<=2A`, and `A<2H`.
* The same file red-teams the residual with the exact Venn-cell witness
  `H=A=2`, all proper pair cells `3m`, and all singleton cells `7r+1`.  This
  showed that no stronger cardinal-only argument could close the branch and
  directly suggested multiplying by a common quadratic while creating a
  second hole.  Iterating that trade gives the amplifier below.

## 1. Correction to the fixed-hole common-factor red team

An earlier red team correctly observed that adding a common root while keeping
the hole set fixed is harmful: an all-three coordinate is missed by no source
line and supplies no fresh label.

The mistaken extrapolation was that a common factor can never improve the
construction.  A coordinated trade changes both sides of the ledger.  If `H`
is the number of holes and `A` the all-three core size, then the exact
three-line one-fresh capacity is

```text
B = n + 2H - A.
```

Adding two dead common roots while adding one hole leaves `2H-A` unchanged.
This is the amplifier.

## 2. General `d`-step cell trade

Write `m=3r+1`.  After maximal private thickening, the smooth `mu_16` cell has

```text
holes                 1,
triple core           0,
proper pair cells     3m each,
singleton cells       7r+2 each,
core size             8m+r,
ownership budget      n+2.
```

For any admissible integer `d`:

1. select `d` singleton coordinates owned by line zero and `d` owned by line
   one;
2. let `G` be their monic degree-`2d` locator;
3. multiply every old line factor `f_i` by `G`;
4. set the received pair to zero on those `2d` roots, making them common to
   all three cores;
5. remove `d` singleton coordinates owned by line two and use them as new
   isolated holes.

The new cells are exactly

```text
H = d+1,
A = 2d,
proper pair cells = 3m each,
singleton cells = 7r+2-d each.
```

Hence

```text
universe size = (d+1)+2d+3(3m)+3(7r+2-d) = 16m,
core size     = (7r+2-d)+2(3m)+2d = 8m+r+d,
bad labels    = 3(7r+2-d)+3(3m)+3(d+1) = 16m+2.
```

These are the Lean theorems
`amplified_cell_universe_size_of_d_le`, `amplified_core_size`, and
`amplified_ownership_budget`.

## 3. Amplified polynomial lines

The old universal cell uses factors

```text
f_0 = 0,
f_1 = (1-lambda) p_A(X^m),
f_2 = p_C(X^m),
```

whose three pair differences have disjoint `3m`-point split root sets.  Put

```text
h_i = G f_i,
c_i = (X h_i, h_i).
```

At a root of `G`, all three pairs evaluate to `(0,0)`.  Away from `G`, equality
of two amplified lines is equivalent to equality of the corresponding old
factor values.  Therefore amplification adds exactly the selected common
roots and preserves all three old proper pair blocks; it creates no accidental
pair roots.  This is kernel checked by
`amplifiedLine_eval_eq_zero_of_common_root` and
`amplifiedLine_eval_eq_iff_factor_eval_eq`.

At any nondead covered coordinate `x`, choose a source line missing `x` and
use

```text
gamma = -x,
q(X) = h_i(X)(X-x).
```

The polynomial identity

```text
q = (X h_i) + gamma h_i
```

is `amplifiedFreshWitness_eq_affineLine`; `q(x)=0` is also checked.  Thus all
nondead owned coordinates give distinct labels inside `mu_n`.

If `deg G=2d`, then the line intercept and fresh witness have degree at most

```text
3m+2d+1.
```

They remain degree `<k=4m` whenever `2d+1<m`.  At the saturated choice

```text
d_max = (m-2)/2 = 33,554,431,
```

the degree is exactly `4m-1`.  The Lean endpoint identities are
`saturated_d_degree_and_cell_available`, `saturated_threshold_identity`, and
`saturated_error_identity`.

## 4. Scaled-hole cancellation

At a hole coordinate `x`, write

```text
ell = G(x) != 0,
t_i = f_i(x),
h_i(x) = ell*t_i.
```

If the received pair is `(alpha*x,beta)`, the isolated scalar is

```text
gamma_i = x (ell*t_i-alpha)/(beta-ell*t_i).
```

Choose quotient-fibre row parameters `alpha_0,beta_0` and scale the received
row by `ell`:

```text
alpha = ell*alpha_0,
beta  = ell*beta_0.
```

Then the common factor cancels exactly:

```text
gamma_i = x (t_i-alpha_0)/(beta_0-t_i).
```

This is `scaledHoleGamma_scaled_rows`.  Its agreement and genuine nonjointness
corollaries are `scaledHoleGamma_scaled_rows_agreement` and
`scaledHole_scaled_received_pair_ne_line`.

The more general Möbius theorem `eq_of_scaledHoleGamma_eq` says that distinct
old values `t_i` give distinct labels whenever `x`, `ell`, and
`beta-alpha` are nonzero and the denominators are nonzero.

There is also a kernel-checked avoidance fallback.  Given any forbidden set
`B` of scalars, `exists_scaledHole_parameters_avoiding` chooses a hole row
whose three labels are distinct and avoid `B` under the sharp elementary
conditions

```text
3 < |F|,
3|B|+1 < |F|.
```

For fixed `beta`, each forbidden target excludes exactly one `alpha` on each
of the three lines.  This makes sequential global hole-label selection
available even without multiplicative coset symmetry.

## 5. Compressed saturated P1 certificate

The maximum construction does not enumerate `33,554,431` roots or holes.
It uses quotient fibres:

```text
common roots: first d_max points of private fibre 4  (line 0),
              first d_max points of private fibre 11 (line 1),
new holes:    first d_max points of private fibre 13 (line 2),
old hole:     the residual point in fibre 15.
```

All three old factor values are distinct on fibres `4,11,13,15`, and
`d_max<m`, so every chosen cell is available.  The common-root and hole fibres
are disjoint, hence `G` is nonzero on every hole.

For both hole fibres the probe finds the tiny scaled-row choice

```text
alpha_0 = 1,
beta_0  = 2.
```

On fibre 13, the three exact coset constants are

```text
182687704666362864775460604089535377560070782976,
357427157257065199771064609774836810806559371356,
 48131014922838568432685688908340148811467554291.
```

The probe verifies:

* every constant has nonunit `n`th power, so its whole label coset is outside
  `mu_n`;
* every pairwise constant ratio has nonunit `m`th power, so the three
  fibre-13 label cosets are disjoint;
* all nine ratios from the three residual fibre-15 labels to the three full
  fibre-13 cosets have nonunit `m`th power, so the old hole labels are also
  disjoint from every new label;
* the four quotient-fibre factor-value triples are nondegenerate where used;
* the exact core, threshold, radius, degree, and `n+2` count identities hold.

The final saturated ledger is

```text
d                  = 33,554,431,
holes              = 33,554,432,
triple core         = 67,108,862 = m-2,
proper pair each    = 201,326,592 = 3m,
core size           = 592,794,964,
agreement threshold = 592,794,965,
error count          = 480,946,859,
bad scalars          = 1,073,741,826 = n+2.
```

## 6. Red-team audit and remaining work

The following possible failure modes were checked explicitly.

* **Dead common roots:** charged exactly by the `-A` term in `n+2H-A`; the
  simultaneous new holes pay for them.
* **Accidental pair roots:** ruled out away from `G` by cancellation of the
  nonzero common-locator value.
* **Degree overflow:** the saturated intercept and witness degree is `4m-1`,
  not `4m`.
* **Hole accidentally joining a core:** the scaled denominator
  `ell(beta_0-t_i)` is nonzero, so the received direction row differs from
  every decoded line.
* **Within-hole collision:** ruled out by Möbius injectivity.
* **Collision with safe labels:** all isolated cosets lie outside `mu_n`,
  whereas safe labels are `-x` with `x in mu_n`.
* **Cross-hole/cross-line collision:** certified by the exact `m`th-power
  tests described above.
* **Insufficient private coordinates:** `d_max<m`, while each selected
  private quotient fibre has size `m`.

What remains is integration, not another informal arithmetic step:

1. instantiate the common locator and reclassified core sets inside the P1
   scale-construction Lean module;
2. connect every safe and isolated witness to the nonjoint bad-event API;
3. connect the resulting `n+2` family at threshold `t` to the operational
   `deltaStar` ledger;
4. independently seek a matching uniform lower bound.  Nothing here proves
   optimality of `43/96+1/(3n)`.

## 7. Multi-line frontier after saturation

`_RateQuarterSaturatedFiveCoreBarrier.lean` sharpens the earlier quadratic
six-core Plotkin cutoff using integer coordinate multiplicities.  For five
cores let `s_x` be the number containing coordinate `x`.  The pointwise law

```text
5 s_x <= s_x^2 + 6
```

and exact incidence double counting give

```text
20z <= 6n + 20lambda
```

when each core has size at least `z` and every pair intersection is at most
`lambda`.  Substituting `n=16m`, `lambda=4m-2`, and `6z=53m-8` is already
contradictory for `m>10`.  Inside a primitive collapsed cluster the factor
degree supplies precisely this pair cap, so the axiom-clean theorem
`not_five_saturated_cores_in_primitive_cluster` rules out five or more
saturated source lines.  Only clusters of at most four source lines remain;
this argument is independent of the particular `mu_16` locator pattern.
