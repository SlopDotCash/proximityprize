# R387: Johnson pruning closes the half predecessor at rate at most `1/8`

Date: 2026-07-09
Campaign: #466
Status: abstract combinatorial and moment engine axiom-clean; concrete RS secant
connector remains to instantiate the hypotheses

## 1. Statement

Let `n=2h`, let the agreement threshold be `t=h+1`, and let a selected bad
scalar carry a degree-`<k` Reed--Solomon explainer.  Assume

```text
h >= 2048,       4 | h,       k <= h/4 = n/8.
```

The lifted rich-hyperplane geometry reduces the desired half-predecessor bound
to a finite family `G` of selected affine points with agreement sets
`A_P subset [2h]`, each of size at least `h+1`.  Under the standard secant-core
laws listed below, this note proves

```text
|G| <= 2h = n.
```

The proof is field- and evaluation-domain-independent.  It uses no genericity,
characteristic-zero transfer, higher-order MDS assertion, or incidence-vector
independence.

The axiom-clean abstract implementation is split into:

* `Frontier/_R387RateEighthPruning.lean`: nonuniform Johnson packing, the
  `15/3` line stratification, the exceptional-union bound, and the exact line
  arithmetic;
* `Frontier/_R387RateEighthPrunedMoment.lean`: Jensen under the correct
  post-pruning average hypothesis, the exact rate-`1/8` numeric gap, and the
  abstract final incidence consumer.

These files are an independent cross-check of the contemporaneous
`_HalfPredecessorRateEighth*` lane.

## 2. Geometric inputs

For every selected secant line `ell`, write

```text
D_ell = common agreement core,
z_ell = |D_ell|,
r_ell = number of selected points on ell,
d     = k-1 <= h/4-1.
```

The polynomial-line geometry supplies:

1. Any selected line has `r_ell <= h`.
2. The exact fresh-fibre packing law is

   ```text
   r_ell * max(1,h+1-z_ell) + z_ell <= 2h.          (P)
   ```

3. A selected point off `ell` meets `D_ell` in at most `d` coordinates.
4. A noncollinear selected triple has common agreement at most `d`.
5. Distinct selected points determine a unique secant line.

There is also a derived input needed by Johnson:

```text
|D_ell intersect D_m| <= d                         (C)
```

for distinct selected lines.  To prove `(C)`, choose a selected point `P` on
`ell` but not on `m`.  Such a point exists because otherwise two points of
`ell` would lie on `m`, contradicting secant uniqueness.  Since
`D_ell subset A_P`, the off-line core cap for `m` gives
`|D_ell intersect D_m| <= |A_P intersect D_m| <= d`.

## 3. The global core ceiling comes before pruning

Assume for contradiction that

```text
N = |G| >= 2h+1.                                   (H)
```

Fix any selected line `ell` with core size `z`.  Because every line has at
most `h` points, at least `h+1` selected points lie outside `ell`.  Every such
point `P` has at least

```text
|A_P \ D_ell| >= h+1-d
```

agreements outside the core.  Three outside points therefore have, by the
three-set Bonferroni inequality in the `2h-z` outside coordinates, common
agreement at least

```text
3(h+1-d) - 2(2h-z) = 2z-h+3-3d.                   (B)
```

If `2z > h+4d-3`, `(B)` is greater than `d`, so every outside triple is
collinear.  Fixing two outside points and using secant uniqueness puts every
outside point on one line.  The whole family is then contained in two lines,
each of size at most `h`, contrary to `(H)`.  Hence every selected line,
before any deletion, obeys

```text
2z <= h+4d-3 <= 2h-7,
z <= h-4.                                          (G)
```

This order matters: `(G)` is a global consequence of the original
counterexample and is not inferred from the pruned subfamily.

## 4. Reparameterization and the two line strata

Put

```text
c = h+1-z.
```

By `(G)`, `c>=5`.  Substituting `z=h+1-c` in `(P)` gives

```text
(r-1)c <= h-1.                                     (F)
```

Call a line exceptional if `r>=5`.  Then `(F)` implies

```text
c <= h/4-1,
z >= 3h/4+2.                                       (E)
```

Call it ultra if additionally `c<=h/16`.  Then

```text
z >= 15h/16+1,
5r <= h+4.                                         (U)
```

For a non-ultra exceptional line, `c>h/16`; if `r>=17`, then
`(r-1)c>h`, contradicting `(F)`.  Thus

```text
r <= 16.                                           (N)
```

## 5. Johnson with nonuniform cores

For a family of `q` subsets of an `n`-point universe, suppose every member has
size at least `Z` and distinct members intersect in at most `d`.  The
second-moment/Johnson inequality is

```text
q (Z^2-n d) <= n (Z-d).                            (J)
```

No equal-size assumption is hidden here.  The Lean theorem
`johnson_core_packing` proves `(J)` directly for nonuniform members.  Truncating
each member to an arbitrary `Z`-subset is an equivalent safe proof because
intersections can only decrease.

Apply `(J)` with `n=2h`, `d=h/4-1`.

For all exceptional lines, take `Z=3h/4+2`.  Then

```text
Z^2-2hd = h^2/16+5h+4,
2h(Z-d) = h^2+6h.
```

Sixteen cores would make the left side
`h^2+80h+64`, strictly larger than the right side.  Therefore

```text
# exceptional lines <= 15.                         (J15)
```

For ultra lines, take `Z=15h/16+1`.  Substituting `q=4` in `(J)` gives a
strict excess

```text
9h^2/64 + 23h/2 + 4 > 0.
```

Therefore

```text
# ultra lines <= 3.                                (J3)
```

## 6. Delete every exceptional line

Let `R` be the union of the original selected point sets on all exceptional
lines.  Overlaps only make this union smaller.  If `q` is the number of ultra
lines and `e` the total number of exceptional lines, `(U)`, `(N)`, `(J15)`,
and `(J3)` give

```text
|R| <= q(h+4)/5 + 16(e-q)
     <= 3(h+4)/5 + 12*16.
```

For `h>=1701`, the last expression is at most `5h/7`; in particular,

```text
7|R| <= 5h                                         (R)
```

for the production-safe cutoff `h>=2048`.

Let `M=|G\R|`.  From `(H)` and `(R)`,

```text
7M >= 9h+7.                                        (M)
```

Every original secant line now contains at most four surviving points.  If it
was exceptional, every selected point on it was placed in `R`; otherwise its
original selected-point count was already at most four.  This explicitly
rules out a possible error in which lines are reclassified only after deletion.

## 7. The pruned third moment

For each coordinate `i`, let

```text
m_i = #{P in G\R : i in A_P}.
```

Since each remaining agreement set has size at least `h+1`,

```text
sum_i m_i >= M(h+1).
```

The comparison average is

```text
a = M(h+1)/(2h).
```

Condition `(M)` and `h>=3` imply `a>=2`.  Convexity of the descending
Pochhammer extension of `choose(x,3)` therefore gives

```text
6T := 6 sum_i choose(m_i,3)
   >= 2h * a(a-1)(a-2).                            (L)
```

For the upper bound, noncollinear triples cost at most `d=h/4-1`.  A collinear
triple has common agreement at most the global core ceiling `h-4`, hence excess
at most

```text
(h-4)-d = 3h/4-3.
```

A line has at most four surviving points, so each ordered pair has at most two
collinear choices for its third point.  Consequently

```text
6T <= (h/4-1) M(M-1)(M-2)
      +(3h/2-6) M(M-1).                            (Q)
```

Four times `(L)-(Q)` factors as

```text
M * [
  (7 + 3/h + 1/h^2) M^2
  -(9h + 6/h) M
  +12h-8
].                                                 (D)
```

From `7M>=9h+1` and `h>=7`, one has

```text
9h+6/h < 7M
       <= (7+3/h+1/h^2)M.
```

Both the leading bracket contribution and `12h-8` in `(D)` are positive.
Thus the lower bound is strictly larger than the upper bound, a contradiction.
This proves `|G|<=2h`.

## 8. Lean handoff

The principal reusable declarations are:

```text
R387RateEighthPruning.johnson_core_packing
R387RateEighthPruning.ultra_core_family_card_le_three
R387RateEighthPruning.exceptional_core_family_card_le_fifteen
R387RateEighthPruning.exceptional_biUnion_seven_mul_card_le_five_mul
R387RateEighthPruning.rateEighth_exceptional_union_bound

R387RateEighthPrunedMoment.thirdMoment_jensen_lower_rat_of_average_two
R387RateEighthPrunedMoment.upperSix_lt_lowerSix
R387RateEighthPrunedMoment.card_le_thirtyTwo_mul_of_pruned_geometry
```

The last theorem takes `h=16m`, `m>=128`, a removable subset with
`7|R|<=80m`, the exact secant-line uniqueness/four-point hypotheses, and the
two triple-codegree caps.  It returns `|G|<=32m=2h`.

## 9. Honesty boundary

The abstract pruning and moment theorem is axiom-clean.  This note does not
claim the operational MCA theorem is already connected: the concrete
bad-scalar rich-point family must still instantiate the distinct-core
intersection bound, global core ceiling, exceptional/ultra filters, removal
set, and post-pruning line hypotheses.  All of those are elementary
consequences of the existing polynomial secant geometry, but the final Lean
connector is separate work.
