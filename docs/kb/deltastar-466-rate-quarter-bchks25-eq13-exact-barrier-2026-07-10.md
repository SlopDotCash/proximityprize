# P1 rate-quarter: exact BCHKS25 Equation 13 optimization barrier

## Result

At the P1 predecessor parameters

```text
n = 2^30 = 1073741824
k = 2^28 = 268435456
gamma = 480946858 / n
rho = k/n = 1/4
eta = 1 - sqrt(rho) - gamma = 27962027 / 536870912,
```

the multiplicity in [BCHKS25, Theorem 1.5] is exactly `m=5`, because

```text
sqrt(rho)/(2 eta) = 134217728 / 27962027
4 < 134217728 / 27962027 < 5.
```

The theorem's printed, deliberately unoptimized degree choice gives

```text
DX = 2952790016,  DY = 11,  DZ = 121/3,
Eq13 RHS = 86479468494859/3 = 28826489498286 + 1/3.
```

Thus its smallest integer firing count is `28826489498287`.

Counting the integer interpolation variables and equations before the
relaxations in Equations (11)--(12), and allowing a restricted `Y`-degree
subspace, improves the best strict-integer threshold to

```text
smallest |S| that fires Eq13 = 11510231640868,
non-joint exceptional cap     = 11510231640867.
```

This is a genuine factor-`2.5044` improvement over the printed Theorem 1.5
constant.  It still misses the required cap `n=1073741824` by more than four
orders of magnitude:

```text
10719*n < 11510231640867 < 10720*n.
```

In particular, the P1 predecessor hypothesis supplies only `n+1` bad
scalars, far below the `11510231640868` needed to trigger this optimized
Guruswami--Sudan/Hensel route.  This is a barrier for this proof architecture,
not a counterexample to the exact predecessor bound or to the proximity-prize
conjecture.

The deterministic reproducer is

```text
python3 scripts/probes/probe_rate_quarter_p1_bchks25_eq13_exact.py
```

and uses only Python's exact `Fraction` arithmetic.

## Exact interpolation cell

Equations (10)--(12) in [BCHKS25] count a homogeneous linear system.  For
real caps `DX,DY,DZ`, write

```text
X = ceil(DX),  Y = ceil(DY),  Z = ceil(DZ).
```

Restrict the interpolation ansatz to monomials

```text
i + k*j < DX,       j < DY,       j + h < DZ.
```

This restriction is legitimate: it only replaces the paper's interpolation
space by a smaller explicitly counted subspace.  In one ceiling cell the
exact number of variables is

```text
V(X,Y,Z) = sum_{0 <= j < Y} (X-k*j)(Z-j),
```

while the number of coefficient equations from (10) is at most

```text
E(m,Z) = n * sum_{0 <= s < m} (m-s) max(Z-s,0).
```

The optimum cell is

```text
m=5, X=2959337223, Y=10, Z=25,
V=381178347675,
E=381178347520,
V-E=155 > 0.
```

The strict margin `155` is important: rank-nullity gives a nonzero
interpolant over every field, with no numerical-rank assumption.

Take the explicit rational caps

```text
epsilon = 10^-18,
DX = 2959337222 + epsilon,
DY = 9 + epsilon,
DZ = 24 + epsilon.
```

They satisfy all cap conditions used in the paper's interpolation argument:

```text
DY >= m-1,  DX >= k*DY,  DZ >= DY,
DX <= m*(1-gamma)*n = 2963974830.
```

Their ceilings are the optimum `(X,Y,Z)` above.  Exact rational evaluation
then gives

```text
11510231640867 <
  2*DX*DY^2*DZ + (gamma*n+1)*DY
< 11510231640868.
```

Because Equation (13) is strict, `11510231640868` is the first integer
cardinality that fires, and contraposition gives the exceptional cap
`11510231640867`.

## Why the optimization is exhaustive

The probe enumerates ceiling cells, not floating-point degree triples.  In a
cell `(X,Y,Z)`, the infimum of the Equation (13) right-hand side is

```text
B0 = 2*(X-1)*(Y-1)^2*(Z-1) + (gamma*n+1)*(Y-1).
```

Every feasible real cap in that cell has RHS strictly above `B0`.  The exact
dimension inequality is linear in `X`, so the least possible `X` is obtained
by integer division.  The constraints `DX >= k*DY`, `DZ >= DY`, and
`DX <= m*(1-gamma)*n` give finite ranges for `Y` and `Z`.

Multiplicities outside the enumerated range are excluded without a heuristic
cutoff.  Since `DY >= m-1`, `DX >= k*DY`, and `DZ >= DY`, every feasible RHS
is at least

```text
2*k*(m-1)^4 + (gamma*n+1)*(m-1).
```

This already exceeds the incumbent for every `m>=14`.  The probe exhausts
all potentially competitive cells for `5<=m<=13`; its monotone `Z` lower
bound stops a row only after every later cell is provably too large.  The
reported global cell is also explicitly feasible, so the open-cell infimum
and the smallest strict integer threshold are both certified.

The word "minimal" here is deliberately scoped to the universal
rank-nullity proof behind Equations (10)--(13).  An input-dependent rank defect
could produce an interpolant with fewer variables than equations, but the
paper gives no uniform theorem of that kind, and it cannot be assumed in a
worst-case predecessor proof.

## Relation to existing in-tree barriers

This calculation does not duplicate
`_FSME_BivariateJohnsonErrorFloor.lean`.  FSME evaluates the older in-tree
`BCIKS20.errorBound` at P1 and obtains the much larger scalar budget

```text
2^63 * 10^7 = 92233720368547758080000000.
```

The present note audits the improved 2025 interpolation count in
[BCHKS25, Equations (10)--(13)] and lowers that architecture to
`11510231640867` exceptions.

It also does not supersede the separate Hab25 cell architecture.
`Hab25CellWiring.lean` records a sharper conditional per-stack count `L*n`
once the deep factor-capture input is supplied.  At a nearby strict P1
Johnson slack with `m=5`, its list-shape constraint gives integer `L<=10`, so
that route is already at most `10*n`.  It still does not reach the exact
`1*n` budget.  The result here is therefore the exact optimum of BCHKS25
Equation (13), while Hab25 remains a distinct and quantitatively sharper
conditional decomposition.

## Source and honesty boundary

Primary source: Eli Ben-Sasson, Dan Carmon, Ulrich Habock, Swastik Kopparty,
and Shubhangi Saraf, *On Proximity Gaps for Reed--Solomon Codes*, ECCC
[TR25-169](https://eccc.weizmann.ac.il/report/2025/169/) (2025), also
[ePrint 2025/2055](https://eprint.iacr.org/2025/2055).
The inputs used above are Theorem 1.5, Lemma 3.1, Equations (10)--(13), and
the paper's explicit observation that its degree parameters are not fully
optimized.

No claim is made past the Johnson radius, no exact delta-star pin is claimed,
and no polynomial realization or non-realization is inferred from this
numeric barrier alone.
