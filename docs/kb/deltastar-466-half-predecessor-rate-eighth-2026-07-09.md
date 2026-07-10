# A weighted half-predecessor theorem at rate at most `1/8`

Date: 2026-07-09
Campaign: #466
Status: machine-checked, including the literal bad-event bound, normalized
`epsMCA` bound, and exact operational `mcaDeltaStar = 1/2` pin

## 1. Result

Let `F` be a field, let `alpha_1,...,alpha_n` be distinct, and let
`RS(alpha,k)` be the corresponding Reed--Solomon code.  Assume

```text
    n = 2h,       h >= 1699,       1 <= k <= h/4,
```

and set `t=h+1`.  For every two-row stack
`(u0,u1)`, at most `2h=n` scalars `gamma` have a nonjoint degree-`<k`
witness agreeing with `u0+gamma*u1` on at least `t` coordinates.
Equivalently, the nonjoint MCA numerator at error radius

```text
(h-1)/(2h) = 1/2 - 1/n
```

is at most `n`.

The overlapping `c=0` packing attains `n`, so this is sharp.  This extends
the rate-`1/16` third-moment theorem to rate `1/8`.  The new ingredient is a
two-level weighted stratification of line cores:

* an ultra-large core would make the complements of the outside agreements
  a constant-weight code beyond its Plotkin threshold;
* after ultra-large cores are excluded, every selected line has at most 100
  points;
* the Johnson inequality for the cores themselves shows that at most 15
  selected lines have five or more points;
* all remaining lines have at most four points, and their aggregate
  third-moment correction fits inside the exact rate-`1/8` margin.

The proof is field- and domain-independent after distinctness of the
evaluation points.  It does not use smoothness, characteristic zero, a
higher-MDS conjecture, incidence-vector independence, or a divisibility
assumption on `h`.

## 2. Inherited rich-point geometry

Choose one full agreement set `A_P` for every allegedly bad scalar and lift
its scalar and witness polynomial to a distinct affine point `P`.  The
notation and the following facts are proved in
`Frontier/_HalfPredecessorLineCoreGeometry.lean` and explained in the
rate-`1/16` note.

Put

```text
U = {1,...,2h},       |A_P| >= h+1,       d = h/4-1.
```

Using the largest allowed `d` only weakens the estimates when `k<h/4`.
For a selected affine line `ell`, let

```text
D_ell = common agreement core,
z_ell = |D_ell|,
L_ell = number of selected points on ell.
```

Then:

```text
A_P intersect A_Q = D_ell                           (G1)
```

for distinct `P,Q` on `ell`, and the fresh fibres are disjoint.  Nonjointness
therefore gives

```text
L_ell * max(1,h+1-z_ell) + z_ell <= 2h.             (G2)
```

In particular, every selected line has at most `h` points.  If `R` is off
`ell`, the polynomial root bound gives

```text
|A_R intersect D_ell| <= d.                         (G3)
```

A noncollinear selected triple has common agreement at most `d`; a
collinear triple on `ell` has common agreement exactly `z_ell`:

```text
|A_P intersect A_Q intersect A_R| <= d              (G4)
```

unless `P,Q,R` are collinear.

Distinct selected lines with at least two points have cores meeting in at
most `d` points:

```text
|D_ell intersect D_m| <= d.                         (G5)
```

Indeed, choose a selected point of `ell` which is not on `m`; its agreement
contains `D_ell`, and `(G3)` for `m` applies.

## 3. The universal core ceiling `z <= h-4`

Assume for contradiction that the number of selected points is

```text
N >= 2h+1.                                          (C0)
```

Fix a selected line `ell` with core size `z`.  By `(G2)`, there are at least
`N-h >= h+1` selected points outside it.  For an outside point `P`, `(G3)`
gives

```text
|A_P \ D_ell| >= h+1-d.
```

For three outside points, the three-set Bonferroni inequality in the
`2h-z` coordinates outside `D_ell` gives common agreement at least

```text
3(h+1-d) - 2(2h-z) = 2z-h+3-3d.
```

If `2z>h+4d-3`, this is greater than `d`; `(G4)` says that every outside
triple is collinear.  Fixing two outside points then puts all outside points
on one affine line.  The selected configuration lies on two lines, each of
size at most `h`, contradicting `(C0)`.

Since `d=h/4-1`, every line in a counterexample must therefore satisfy

```text
2z <= 2h-7,
z <= h-4.                                           (C1)
```

Write

```text
z = h-c.                                            (C2)
```

Then `c>=4`, and `(G2)` becomes the exact packing law

```text
L_ell(c+1) <= h+c.                                  (C3)
```

## 4. Ultra-core exclusion by an outside-complement code

We prove that a counterexample cannot contain a line with

```text
100c <= h.                                          (U0)
```

Fix such a line.  Let

```text
V = U \ D_ell,              |V| = h+c,
O = selected points outside ell,
M = |O| >= h+1.
```

For `P in O`, define its outside agreement and its complement by

```text
B_P = A_P \ D_ell,
C_P = V \ B_P.
```

From `(G3)` and `|A_P|>=h+1`,

```text
|B_P| >= h+1-d = 3h/4+2,
|C_P| <= b := h/4+c-2.                              (U1)
```

Put

```text
s := 2c-7,
r := b-s = h/4-c+5.                                 (U2)
```

### 4.1 Pair intersections are at most `s`

If `P,Q,R` are noncollinear, `(G4)` implies

```text
|C_P union C_Q union C_R| >= |V|-d = 3h/4+c+1.
```

But

```text
3b-s = 3h/4+c+1 = |V|-d.                            (U3)
```

If `|C_P intersect C_Q|>s`, then for every `R`

```text
|C_P union C_Q union C_R|
  <= |C_P|+|C_Q|+|C_R|-|C_P intersect C_Q|
  < 3b-s,
```

so the triple must be collinear.  Thus all points of `O` lie on the line
through `P,Q`; together with `ell` this contradicts `(C0)`.  Consequently,

```text
|C_P intersect C_Q| <= s                            (U4)
```

for every distinct `P,Q in O`.

### 4.2 Every block has size at least `r`

If `|C_P|<r=b-s`, then for any `Q,R`

```text
|C_P union C_Q union C_R| < (b-s)+2b = 3b-s.
```

Again every triple containing `P` is collinear, hence all of `O` lies on one
line and the two-line contradiction follows.  Therefore

```text
r <= |C_P| <= b.                                    (U5)
```

### 4.3 Weighted Plotkin inequality

For `x in V`, let `rho_x` be the number of blocks `C_P` containing `x`, and
put `I=sum_x rho_x`.  From `(U4)` and `(U5)`,

```text
Mr <= I <= Mb,
sum_x rho_x^2
  = I + 2 sum_{P<Q}|C_P intersect C_Q|
  <= Mb + sM(M-1).
```

Cauchy--Schwarz gives `I^2 <= |V| sum_x rho_x^2`, hence

```text
M(r^2-|V|s) <= |V|(b-s) = |V|r.                    (U6)
```

Under `c>=4` and `(U0)`,

```text
r >= 6h/25,
s <= h/50,
|V| <= 101h/100,
r^2-|V|s >= 187h^2/5000,
|V|r <= (101h/100)(h/4+1).
```

Also `(U0)` and `c>=4` imply `h>=400`.  With `M>=h+1`, the left side of
`(U6)` is already larger than its right side (even the weaker comparison
`187h^3/5000 > 101h^2/200` suffices).  This contradiction proves

```text
100c > h                                             (U7)
```

for every selected line in a counterexample.

Combining `(U7)` with `(C3)`,

```text
L_ell(c+1) <= h+c < 101c < 101(c+1),
L_ell <= 100.                                       (U8)
```

This is the first stratification layer.

## 5. At most fifteen lines have size at least five

Call a selected line exceptional if `L_ell>=5`.  From `(C3)`,

```text
5(c+1) <= h+c,
4c+5 <= h,
z=h-c >= (3h+5)/4.
```

As `h` is divisible by four and `z` is integral,

```text
z >= Z := 3h/4+2.                                   (J1)
```

For each exceptional line choose a `Z`-subset `E_ell` of its core.  By
`(G5)`, distinct `E_ell` meet in at most `d=h/4-1` points.  If there are `m`
exceptional lines and `sigma_x` is the number of their chosen cores through
coordinate `x`, then

```text
sum_x sigma_x = mZ,
sum_x sigma_x^2 <= mZ + dm(m-1).
```

Cauchy--Schwarz now gives the constant-weight Johnson inequality

```text
m(Z^2-2hd) <= 2h(Z-d).                              (J2)
```

The quantities are exact:

```text
Z^2-2hd = h^2/16+5h+4,
2h(Z-d) = h^2+6h.
```

If `m>=16`, the left side of `(J2)` is at least

```text
h^2+80h+64 > h^2+6h,
```

a contradiction.  Hence

```text
m <= 15.                                            (J3)
```

Together, `(U8)` and `(J3)` say that every line has size at most 100, and
all but at most fifteen lines have size at most four.

## 6. Weighted third-moment upper bound

Let

```text
T = sum_i choose(m_i,3),
m_i = number of selected agreement sets containing coordinate i.
```

Double counting triples gives

```text
T <= d choose(N,3) +
  sum_ell choose(L_ell,3)(z_ell-d).                 (M1)
```

By `(C1)`,

```text
z_ell-d <= 3h/4-3.                                  (M2)
```

For a nonexceptional line, `L<=4`, so

```text
choose(L,3) <= (2/3) choose(L,2).
```

Every pair of selected affine points determines one line, whence

```text
sum_ell choose(L_ell,2) = choose(N,2).
```

Thus all nonexceptional lines together contribute at most

```text
(2/3)(3h/4-3) choose(N,2)
  = (h/2-2) choose(N,2).                            (M3)
```

There are at most fifteen exceptional lines and each has size at most 100,
so their total contribution is at most

```text
15 choose(100,3)(3h/4-3),
choose(100,3)=161700.                               (M4)
```

Multiplying `(M1)`--`(M4)` by six yields

```text
6T <= (h/4-1)N(N-1)(N-2)
    + (3h/2-6)N(N-1)
    + 90*161700*(3h/4-3).                           (M5)
```

## 7. Exact Jensen comparison

The total incidence is at least `N(h+1)`.  The discrete Jensen theorem in
`Frontier/_HalfPredecessorThirdMomentJensen.lean`, with

```text
a = N(h+1)/(2h),
```

gives

```text
2h*a(a-1)(a-2) <= 6T.                               (M6)
```

After subtracting the first two terms of `(M5)`, the lower bound factors as

```text
N Q_h(N),

Q_h(N) = (7/4 + 3/(4h) + 1/(4h^2))N^2
       - (9h/4 + 3/(2h))N
       + 3h-2.                                      (M7)
```

The quadratic is increasing for `N>=2h+1`.  At the endpoint,

```text
4h^2 Q_h(2h+1) = 10h^4+43h^3+3h^2+h+1 > 0.         (M8)
```

The full endpoint margin, after subtracting the exceptional correction and
clearing `4h^2`, is

```text
20h^5+96h^4-43658951h^3+174636005h^2+3h+1.         (M9)
```

Writing `x=h-2048`, `(M9)` is exactly

```text
347969733288531969
+ 1213875709956099 x
+ 1452336878565 x^2
+ 795988281 x^3
+ 204896 x^4
+ 20 x^5,
```

which is positive for `h>=2048`.  Hence `(M5)` is strictly smaller than
`(M6)`, contradiction.  Therefore `N<=2h`.

The file `_HalfPredecessorRateEighthNumeric.lean` machine-checks `(M7)`--`(M9)`,
monotonicity, and the final abstract contradiction consumer.  Its theorem
audit contains only `propext`.

## 8. Red-team audit

### The `2 x 2` witness trade does not attack this proof

The known four-witness relation

```text
1_S1 + 1_S2 = 1_S3 + 1_S4
```

refutes raw incidence-vector independence.  No independence or rank claim of
that kind appears here.  The proof uses only exact polynomial-line cores,
off-line root caps, and two applications of Cauchy--Schwarz to honest set
systems.  Affine-plane circuits are allowed.

### The packing extremizer survives

The sharp packing has exactly two lines, each with `h` selected points and
core size `h`.  In the contradiction argument, any core above `(C1)` triggers
the two-line branch and proves only `N<=2h`; equality is not excluded.

### Why the high-line core family really has pair intersection at most `d`

Two distinct exceptional lines contain at least five selected points each.
Choose a selected point on the first line which is not on the second.  Its
agreement contains the first core, and `(G3)` bounds its intersection with
the second core by `d`.  Thus `(G5)` has no hidden general-position premise.

### Full agreements and large cores are harmless

Agreement sets are not truncated to size `h+1`.  Larger agreements only
increase the Jensen lower bound and preserve `(G1)`.  The global collapse
first proves `z<=h-4`, so all later uses of `h+1-z=c+1` occur where the
`max(1,...)` in `(G2)` is exactly `c+1`.

### Constants are intentionally coarse

The cutoff `100`, the exceptional-line cap `15`, and `h>=2048` were chosen
for transparent integer arithmetic, not optimization.  The exact final
numeric margin becomes positive already at the first multiple of four
`h=1476`.  Improving constants is unnecessary for the prize-scale instance
`h=2^29`.

## 9. Prize-branch consequence

For the concrete tight-budget branch with

```text
Q=2^128,       n=2^30,       h=2^29,       k=n/8=2^27,
floor(p/Q)=n,
```

the theorem gives at most `n` bad scalars at radius `1/2-1/n`, hence
`epsMCA<=n/p<=1/Q`.  The overlap packing gives `n+2` bad scalars at radius
`1/2`, hence `epsMCA>1/Q`.  After the standard lattice/threshold bridge, the
operational threshold on this field branch is exactly

```text
mcaDeltaStar(RS,1/Q) = 1/2
```

at rate `1/8`, matching the already established rate-`1/16` branch.

## 10. Canonical simplification: prune the exceptional-line union

After the proof above was completed, the same two Johnson strata yielded a
shorter argument which should be treated as the canonical route.  It avoids
the ultra-core complement code and does not pay any exceptional-line term in
the third moment.

Keep `(C1)`, so every line core satisfies `z<=h-4`.  Section 5 proves that
there are at most fifteen exceptional (`L>=5`) lines.  Introduce the higher
core threshold

```text
z >= 15h/16.                                        (P1)
```

Truncate every core satisfying `(P1)` to a `Z=15h/16` subset.  Truncation
cannot increase intersections, so the pair cap stays `d=h/4-1`.  The sharp
constant-weight Johnson inequality is

```text
m(Z^2-2hd) <= 2h(Z-d).
```

Here

```text
Z^2-2hd = 97h^2/256+2h,
2h(Z-d) = 11h^2/8+2h.
```

For `m=4`, the left side exceeds the right side by
`9h^2/64+6h`.  Thus at most three exceptional lines have core at least
`15h/16`.

For such an ultra line, `(C1)` and the packing law give

```text
5L <= h+4.                                          (P2)
```

Indeed, with `f=h+1-z>=5`, packing is
`(L-1)f<=h-1`, hence `5(L-1)<=h-1`.  For every other exceptional line,
`z<15h/16`; inserting this in `(G2)` shows

```text
L <= 16.                                            (P3)
```

Let `R` be the union of all selected points lying on an exceptional line.
There are at most fifteen exceptional lines total and at most three ultra
lines.  Since `(h+4)/5>=16` at the present scale, the worst sum of their
sizes has three ultra slots and twelve ordinary slots:

```text
|R| <= 3(h+4)/5 + 12*16.
```

Equivalently,

```text
5|R| <= 3h+972.
```

For `h>=1699`, exact integer arithmetic gives

```text
7|R| <= 5h.                                         (P4)
```

Remove `R` from the selected point set.  If the remaining size is `M`, then
from `N>=2h+1` and `(P4)`,

```text
7M >= 7(2h+1)-5h = 9h+7,
9h < 7M.                                            (P5)
```

Every affine line in the remaining configuration has at most four points:
five remaining collinear points would make their original line exceptional,
so all five would have been removed.

Apply the third-moment argument only to these `M` remaining agreement sets.
There is now no exceptional correction.  Six times the upper bound is

```text
(h/4-1)M(M-1)(M-2) + (3h/2-6)M(M-1).               (P6)
```

The same discrete Jensen argument applies because `(P5)` and `h>=1699`
put the average multiplicity well above two.  Subtracting `(P6)` from its
lower bound factors as `M Q_h(M)`, with the same quadratic `(M7)`.  This
quadratic is increasing for `M>=9h/7`, and at the rational endpoint

```text
Q_h(9h/7) = (831h-689)/196 > 0.                     (P7)
```

Thus `(P5)` gives a strict contradiction.

This pruning proof uses only the global core ceiling, two fixed-size Johnson
counts, and the rate-`1/16` style `L<=4` third moment.  The independent
complement-code proof in Sections 4--7 remains useful as a red-team check
and as a stronger statement that every line in a counterexample has at most
100 points.

The structural calculations are axiom-clean in
`Frontier/_HalfPredecessorRateEighthCombinatorics.lean`:

* `sharp_johnson_of_lower_upper_pair`;
* `truncation_preserves_pair_cap`;
* `exceptional_family_card_le_fifteen`;
* `ultra_family_card_le_three`;
* `nonultra_line_card_le_sixteen`;
* `global_core_ceiling_line_budget`.

The numeric endpoint `(P7)` and the pruned-family contradiction are
axiom-clean in `_HalfPredecessorRateEighthNumeric.lean` as
`gapQuadratic_pos_of_nine_mul_lt_seven_mul` and
`nine_mul_le_seven_mul_of_bulk_thirdMoment_bounds`.
The residue-uniform Johnson arithmetic is isolated in
`_HalfPredecessorRateEighthCutoffArithmetic.lean`: the exceptional stratum
needs no large-scale hypothesis, the ultra stratum holds from `h>=416`, and
the integer union budget sets the final intrinsic cutoff `h>=1699`; the
arithmetic envelope still permits a violation at `h=1698`.

## 11. Machine-checked assembly and exact pin

The complete connector is now axiom-clean in
`Frontier/_HalfPredecessorRateEighthFullWiring.lean`.  Its headline theorem

```text
badScalarRichPointFamily_card_le_two_mul
```

constructs the exceptional-line family `E`, the ultra subfamily `Q`, and the
removed union `R`; proves the `15`/`3` Johnson bounds and `7|R|<=5h`; transports
the four-point, noncollinear, and collinear hypotheses to the pruned family;
and invokes the weighted third-moment consumer.  The literal wrappers are

```text
canonical_halfPredecessor_card_le_length
halfPredecessor_badScalar_filter_card_le_length
halfPredecessor_badScalar_filter_card_le_two_pow_thirty.
```

The operational normalization and threshold composition are in
`Frontier/_HalfPredecessorRateEighthPin.lean`:

```text
epsMCA_halfPredecessor_rateEighth_le
evalCode_mcaDeltaStar_eq_half_of_rateEighth.
```

For every `n=2h` with `h>=1699` and `8k<=n`, the first theorem proves

```text
epsMCA(RS[dom,k], halfPredecessorRadius n) <= n / |F|.
```

For a smooth `ZMod p` evaluation domain with `p/Q=n` and the explicit overlap
packing supply, the second theorem combines that good predecessor with the
matching half-radius bad point and proves exactly

```text
mcaDeltaStar(evalCode g n (k-1), Q^-1) = 1/2.
```

The axiom audits for both capstones contain only `propext`,
`Classical.choice`, and `Quot.sound`; there is no named geometric residual or
`sorryAx`.  This is an operational field/budget pin for the rate-at-most-`1/8`
branch, not a claim that the higher-rate or full proximity-gap challenge is
closed.
