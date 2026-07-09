# Weighted puncture recurrence for the global MCA good side (2026-07-09)

## Result

The new frontier file
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_WeightedPunctureBadScalarRecurrence.lean`
keeps a multiplicity which the existing `BelowUDRPuncture` induction discarded.

For a dimension-`k+1` RS code on `m+1` points at exact error radius `w/(m+1)`, write

```text
B = {gamma : gamma is MCA-bad for (u0,u1)}
Z = {i : u1(i)=0}.
```

Every bad scalar has a witness `S` of size at least `m+1-w`.  Hence

```text
|S intersect Z| >= |Z|-w.
```

For every `i` in this intersection, the existing theorem `mcaEvent_puncture` sends the
*same* scalar to the punctured `(m,k,w)` instance.  Double counting the incidence pairs
`(gamma,i)` proves

```text
|B| (|Z|-w) <= sum_{i in Z} |B_i|.                 (1)
```

The file contains:

- `weighted_puncture_badScalars`: (1);
- `weighted_puncture_badScalars_le_div`: its divided form for `w < |Z|`;
- `weighted_puncture_badScalars_le_of_child_cap`: if every child is at most `M`, then
  `|B| <= |Z| M / (|Z|-w)`;
- `weighted_puncture_badScalars_mul_sub_le_of_zero_floor`: if additionally `K <= |Z|`
  and `w < K`, then the cleaner dimension-floor recurrence
  `|B| (K-w) <= K M`.

The first three theorems were independently checked by `scripts/pg-iterate.sh` before a
concurrent build deleted `MCAThresholdLedger.olean`.  The arithmetic heart of the final
dimension-floor corollary was then extracted as `weighted_recurrence_floor_arith` and checked
in a standalone Mathlib-only file.  A full-file rerun after adding that corollary still awaits
restoration of the shared dependency cache.  No source-level error is being hidden: the failed
rerun stopped at the missing dependency before elaborating this file.

## Why this is a real improvement

The old induction only used

```text
B subset union_{i in Z} B_i,
```

and therefore paid the raw factor `|Z|`.  Equation (1) pays only
`|Z|/(|Z|-w)`.  Under iteration, it accumulates a falling-factorial ratio rather than a
raw branching power.  This is exactly the weighted-fibre correction suggested by the
large-zero branch of the line-list reduction.

Coset invariance makes the dimension-floor form natural.  After subtracting an RS
codeword interpolating the direction on `K` coordinates, the shifted direction has at
least `K` zeros.  Therefore whenever `w<K`, the recurrence applies to *every* stack, not
just a specially sparse direction.

## Adversarial audit: why it does not yet close the prize

Iterating through `t` dimensions has the schematic cost

```text
K.descFactorial(t) / (K-w).descFactorial(t).
```

If one runs until the zero surplus is exhausted, this becomes a binomial-size factor.
At production parameters it is still far above the `q*2^-128` budget.  The recurrence
therefore relocates the residual cleanly but does not manufacture cancellation: after
the surplus is exhausted one still needs a bound for the punctured child family.  This
is the same global line-list/incidence obstruction, now with no lost zero multiplicity.

The most useful regime is the exact-rate `rho=1/2` lane.  There the successor agreement
has error count strictly below the code dimension, so Lagrange interpolation guarantees
the zero surplus for every direction.  For `rho<1/2`, the near-capacity error count is
larger than the dimension, and this recurrence cannot cover the far/middle directions by
itself.

## Independent refutation: the quotient ceiling is not automatically the first jump

The new generic quotient construction is an excellent bad-side family, but a matching
good-side claim must compare it with the already-proved overlap-packing family.

Put

```text
n = s*m
d = (r-1)*m - 1                 -- exact dimension (r-1)*m
t = r*m + 1                     -- one agreement point above the quotient witness
b = (s-r)*m
c = (s-2r)*m.
```

Substituting `(base,c,t)=(b,c,t)` into
`PackingEnvelope.overlap_packing_epsMCA_lower_bound` makes all five arithmetic window
conditions identities or monotone consequences.  Subject only to its explicit fresh-scalar
hypotheses, it gives

```text
epsMCA >= (n+c)/p = 2(s-r)m/p
```

at radius

```text
1 - (r*m+1)/(s*m) = 1-r/s-1/n.
```

Thus whenever `2r<s`, this is strictly more than `n/p`: an earlier bad point than the
quotient radius at the tight budget `B=q*epsilon*=n`.  The required `2c` fresh scalars
exist by the elementary complement count once `p-n >= 2c`; production fields are vastly
larger than this.  This does **not** refute the quotient crossover when `B >> n` (for
example `B=2^40` with `n=2^30`), because overlap packing never supplies much more than
`2n`.  It does refute any unqualified assertion that the quotient rung is the first jump.

## Exact packing lattice point at budget `B = floor(p/2^128)`

Let `Q = 2^128`, let `p` be an odd prime, and put

```text
B = floor(p/Q),       k = n/R,       d = k-1,       D = n-k,
R in {2,4,8,16}.
```

Write the lattice radius as `delta=e/n`, so its agreement threshold is `t=n-e`.
The complete packing construction (bisimplex on the shoulder, tuned overlap in the deep
half) supplies

```text
W(e) = 2e+2 bad scalars
```

exactly throughout its arithmetic window

```text
D/2 <= e <= D-1.                                      (2)
```

Here `D/2` is integral at the dyadic prize parameters with `k>=2`.  Since `p` is odd,
`p/Q` is not integral, and therefore

```text
W(e)/p > 1/Q  iff  W(e) >= B+1.
```

Consequently the **first packing-bad lattice point** is

```text
e_pack = max(D/2, floor(B/2)),
delta_pack = e_pack/n,                                (3)
```

provided

```text
B <= 2D-1.                                            (4)
```

If (4) fails, packing has no bad point below capacity for that budget.  Rate by rate,
the exact existence windows are:

| rate `k/n` | packing errors `e` | largest budget covered |
|---|---:|---:|
| `1/2` | `n/4 <= e <= n/2-1` | `B <= n-1` |
| `1/4` | `3n/8 <= e <= 3n/4-1` | `B <= 3n/2-1` |
| `1/8` | `7n/16 <= e <= 7n/8-1` | `B <= 7n/4-1` |
| `1/16` | `15n/32 <= e <= 15n/16-1` | `B <= 15n/8-1` |

The fresh-scalar requirement is also exact.  If `e_pack <= n/2-1`, the disjoint
bisimplex proves (3) with no tuned scalars.  If `e_pack >= n/2`, set

```text
s = e_pack+1,       c = 2e_pack-n+2,       t = n-e_pack.
```

The overlap theorem needs two disjoint `c`-sets of scalars outside `-mu_n`.  Its six
freshness hypotheses are satisfiable **iff**

```text
p-n >= 2c.                                            (5)
```

Indeed injectivity and the cross-disjointness force `2c` distinct elements of the
complement, and any such choice supplies the two functions.  At the deployed exact
conductor `p=nQ+1`, one has `B=n`, `e_pack=n/2`, `c=2`, so (5) asks only for four
fresh scalars and is automatic.  The resulting rate table is:

| rate | first packing-bad point when `B=n` | count | preceding point |
|---|---:|---:|---:|
| `1/2` | **none** (`B=n` exceeds the `n-1` window) | at most `n` | -- |
| `1/4` | `delta=1/2` | `n+2` | `1/2-1/n` |
| `1/8` | `delta=1/2` | `n+2` | `1/2-1/n` |
| `1/16` | `delta=1/2` | `n+2` | `1/2-1/n` |

Thus the earlier informal comparison with the quotient ceiling is valid only for the
three rates below `1/2`; the headline rate `1/2` has no packing overflow at the tight
budget.

## Audit of existing upper bounds at the immediately preceding point

At the preceding point `delta=(e_pack-1)/n`, the natural agreement integer is

```text
a = n-e_pack+1.
```

No currently unconditional production theorem certifies this point, but the failure modes
can be stated exactly.

1. **BCIKS / true unique decoding.**  The in-tree bound is `epsMCA <= n/p`, so its
   numeric budget requires `B>=n`.  Its radius condition at the preceding point is
   `2(e_pack-1) < n-k+1`.  Combining these with (3) leaves only

   ```text
   k=2 and B in {n,n+1}.
   ```

   Hence BCIKS really does close the adjacent point for the toy exact-rate instances
   `(n,k)=(8,2),(16,2),(32,2)` at rates `1/4,1/8,1/16`, for fields with
   `n <= floor(p/Q) <= n+1`, an order-`n` element, and (5).  Together with packing this
   gives an exact adjacent pin there.  It gives no such pin at rate `1/2`, and none at
   production dimension `k>>2`.

2. **GKL24 1.5-Johnson.**  Even when its cubic-root radius reaches the adjacent point,
   its explicit bad-count numerator contains `(n+6)/eta`.  In the packing window the
   allowed radius slack is too small for this to fit a budget `B<2(n-k)<=2n`.
   At deployed `B=n`, rate `1/4` is outside the cubic-root radius; rate `1/8` has only
   `eta=O(1/n)` and hence an `Omega(n^2)` count; rate `1/16` permits only
   `eta < 1/16+O(1/n)` and hence already pays more than `16n` before the positive
   second term.  Thus no prize-scale rate/field subwindow is certified.

3. **BCHKS25/Hab25 Johnson.**  Its multiplicity is always at least `m=3`, so the first
   positive term alone is

   ```text
   [2(7/2)^5 / (3 rho_plus^(3/2))] n.
   ```

   This is more than `900n` uniformly over the four rates at `n>=32` (and asymptotically
   about `2801n`, `7923n`, `22409n` at rates `1/4`, `1/8`, `1/16`).  Packing can bite
   only while `B<2n`, so the published Johnson numerator never clears the relevant
   budget.  At rate `1/4` the available Johnson slack is additionally only `O(1/n^2)`.

4. **Line-list weld.**  Its arithmetic fit must hold at the adversarial zero count
   `z=a-1`; there the support multiplier is

   ```text
   (n-z)/(a-z) = e_pack.
   ```

   Therefore a budget `B` at the first packing point requires `L*e_pack<=B`, hence
   essentially `L<=2` (and sometimes `L<=1`).  No in-tree theorem proves this far-line
   list cap or the accompanying large-zero cap.  The unconditional per-word incidence
   cap `C(n,k)/C(a,k)` is exponential at production parameters, and unioning it along
   the `p` words of a line is even weaker.  The line-list machinery is therefore the
   correct interface, but not an upper certificate for the adjacent point.

The only genuine adjacent closure found in this audit is the finite `k=2` BCIKS window.
For the deployed constant-dimension-fraction codes, the exact residual remains a uniform
bad-scalar / far-line-list bound at `delta=1/2-1/n` for rates `1/4,1/8,1/16`; one must
not infer that the packing lower bound is the exact jump.

## Exact remaining target

The good side is still the following uniform coloured-secant problem.  For every stack,
each bad scalar owns a large agreement set; on every non-explainable `(k+1)`-core of that
set the divided-difference ratio determines the scalar.  Existing subset ownership is
sharp for one scalar, and equation (1) is now sharp about puncturable zeros.  What is
missing is a **global stability theorem across scalar colours**:

> If more than `B` colours each contain an agreement clique of successor size, then either
> (i) their weighted puncture children already exceed the child budget, or (ii) the colour
> classes organize into one of the explicit quotient/packing families.

Proving that statement with a quantitative child induction would supply the global good
side.  A raw relation count, a support/L1 envelope, or a per-affine-cluster cap cannot do
so: the new R327, maximal-L1-shell, and design-matrix counterexamples respectively rule
out those three weakenings.
