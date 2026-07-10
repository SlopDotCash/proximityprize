# #466 rate-quarter cross-prime clique and five-line ownership barrier (2026-07-10)

## Scope and verdict

This note tests whether extending the saturated universal three-line
split-cubic construction on `mu_16` to a larger mutually split-cubic clique can
improve its asymptotic minimum core `53m/6`.

It does not.  The exact ownership LP finds no improvement, and a
clique-independent counting argument rules out **every five-line** instance of
this architecture:

```text
20 z <= 171 m,
6 z < 53 m                 (m > 0).
```

This is an architecture-local upper bound.  It is not a global rate-quarter
list-decoding lower or upper bound, and it does not close the proximity prize.

## Cross-prime compatibility census

The probe
[`scripts/probes/probe_rate_quarter_mu16_universal_clique_lp.py`](../../scripts/probes/probe_rate_quarter_mu16_universal_clique_lp.py)
starts from the fixed triangle

```text
0, (1-lambda) L_A, L_C
```

and the 29 fourth-line records that survive the four primes
`97, 193, 257, 353`.  Two extension vertices are adjacent only when their
difference is a split cubic with the same exponent-root triple at every test
prime.  The resulting graph has:

```text
29 vertices
93 edges
45 maximal extension cliques
maximal sizes: 2:15, 3:20, 4:9, 5:1
all clique sizes: 1:29, 2:93, 3:60, 4:14, 5:1
largest extension clique: (0,14,15,21,22)
largest total line count: 3 + 5 = 8
```

This is a four-prime survivor census, not a proof that the displayed lines or
edges are universal over every characteristic.  Requiring the same exponent
roots at all four primes is deliberately stronger evidence than merely seeing
a split difference separately in each field.

The graph-only reproduction is lightweight:

```bash
python3 scripts/probes/probe_rate_quarter_mu16_universal_clique_lp.py \
  --start 0 --stop 0
```

## Corrected ownership LP

At a quotient fibre, let the line values split into value-components.  The LP
allows the received row to:

1. own one component, consuming one safe scalar label unless that component
   already contains every line;
2. make a hole, consuming one label for **each distinct value-component**;
3. spend common-locator mass, joining all lines at a dead common root.

The second cost is important: a hole is worth the number of distinct values at
that fibre, not blindly the total line count.  The probe solves the exact
rational dual with SymPy simplex in fresh worker processes to avoid retained
expression caches.

All 15 maximal cliques whose total line count is five were solved exactly.
Their largest optimum was

```text
z/m = 127/16 = 7.9375 < 53/6.
```

The first five total-six-line maximal cliques have best optimum `184/25`, also
below the target.  The unique total-eight-line maximal clique has exact optimum
`237/35`.  These LP computations are diagnostic evidence; the five-line
barrier below does not depend on their enumeration.

## Clique-independent five-line proof

Let `s_e` be the size of the largest equality component among five line values
at quotient coordinate `e`, and let `p_e` be the total number of equal line
pairs at that coordinate.  For `1 <= s_e <= 5`, direct integer arithmetic gives

```text
2 s_e <= choose(s_e,2) + 3 <= p_e + 3.
```

There are ten line pairs.  Every pair difference is a nonzero split cubic, so
it has at most three quotient roots.  Hence

```text
sum_e p_e <= 3 * choose(5,2) = 30.
```

Summing over the sixteen quotient coordinates gives

```text
2 sum_e s_e <= 30 + 16*3 = 78,
sum_e s_e <= 39.
```

After the scale lift, the total baseline maximum-component mass therefore
satisfies `M <= 39m`.

Now let `H` be hole mass and `G` new all-line common-root mass.  Scalar-label
capacity and total core incidence give

```text
G <= 4H,
5z + H <= M + 4G,
G <= m.
```

Multiplying the core inequality by four and using `G <= 4H` yields

```text
20z + G <= 4M + 16G,
20z <= 4M + 15G
     <= 4(39m) + 15m
      = 171m.
```

For positive integer `m`, this implies `6z < 53m`, strictly below the
three-line saturated threshold.

The kernel-cheap arithmetic endpoints are axiom-clean in
[`_RateQuarterManyLineOwnershipBarrier.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_RateQuarterManyLineOwnershipBarrier.lean):

- `maxComponentMass_le_thirtyNine_of_aggregate`;
- `fiveLine_twenty_mul_core_le_171_mul`;
- `fiveLine_core_lt_threeLine_saturated`.

They deliberately consume the already-summed incidence inequality instead of
elaborating a generic symbolic-`L` ledger or a sixteen-term finite sum.

## Frontier consequence

Within this common-factor/ownership amplifier route:

- total line count five is now excluded uniformly;
- larger cliques are numerically much worse here and are structurally covered
  by the separate saturated-six-core obstruction;
- total line count four remains the only larger-clique case not eliminated by
  this five-line certificate, but its best exact LP value found so far is
  `77m/9 < 53m/6`.

Thus searching for still larger universal split-cubic cliques is not a route
to improving the three-line construction under the present ownership rules.
