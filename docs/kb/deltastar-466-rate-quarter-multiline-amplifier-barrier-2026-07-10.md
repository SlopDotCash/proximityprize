# Delta-star rate quarter: multi-line amplifier barrier (2026-07-10)

## Result

Adding universal split-cubic lines does not improve the known three-line
common-factor amplifier in the fractional ownership model.

There are two different levels of evidence:

1. **Kernel checked:** the general ownership exchange rate and the cutoff for
   six or more lines.
2. **Exact rational computation:** exhaustive LP certificates for the fixed
   universal triangle, followed by a four-prime census of every normalized
   non-collinear universal candidate with four or five lines.

The fixed triangle has 29 fourth-line extensions surviving the split primes

```text
97, 193, 257, 353.
```

Their compatibility graph has 93 edges and clique counts

```text
extension vertices       0   1   2   3   4   5
number of cliques         1  29  93  60  14   1
total decoded lines       3   4   5   6   7   8.
```

Exact primal and dual rational certificates give:

| Lines | best core / `m` | radius |
|---:|---:|---:|
| 3 | `53/6` | `43/96` |
| 4 | `77/9` | `67/144` |
| 5 | `127/16` | `129/256` |
| 6 | `149/20` | `171/320` |
| 7 | `43/6` | `53/96` |
| 8 | `237/35` | `323/560` |

Thus every extension of the fixed triangle is strictly worse than the
three-line amplifier.

## 1. General ownership identity

For `ell + 1` decoded-line cores, write

```text
H = number of holes,
A = number of coordinates in every core,
B = one-fresh ownership capacity.
```

The kernel theorem

```text
freshOwnershipBudget_add_allCore_card
```

proves the exact identity

```text
B + A = |U| + ell * H.
```

Consequently an excess of `e` charged labels requires

```text
A + e <= ell * H.
```

This is the general common-factor/hole exchange rate.  At the primitive
direction degree endpoint `A = m-2` and the construction's excess `e=2`, it
becomes

```text
m <= ell * H.
```

The same Lean module proves that the polynomial degree condition

```text
3m + g + 1 < 4m
```

forces `g <= m-2`.

## 2. Six or more lines are impossible

A split-cubic pair difference has three root fibres.  Adding a common factor
of degree below one fibre gives pair-core size at most `4m`.  The exact
constant-weight Johnson/Plotkin calculation for six cores in a `16m`-point
universe gives

```text
6z <= 53m.
```

This is the axiom-clean theorem

```text
six_core_le_three_line_amplifier
```

and its arbitrary-family consumer

```text
multi_core_le_three_line_amplifier.
```

Therefore no architecture with at least six lines, pair cores at most `4m`,
and common target core `z` can strictly beat `53m/6`.  The only LP cases that
needed a census were four and five lines.

## 3. Non-fixed universal census

Translate one line to zero and scale a second line to a monic locator.  The
affine/Galois action on three-subsets of `Z/16` has nine orbits, represented
by

```text
(0,1,2), (0,1,3), (0,1,4), (0,1,7), (0,1,8),
(0,2,4), (0,2,6), (0,2,8), (0,4,8).
```

Intersecting root records over the four split primes gives:

| Lines | survivor records checked | equality signatures | largest exact dual upper |
|---:|---:|---:|---:|
| 3 | 5,520 | 3 | `53/6` |
| 4 | 304,576 | at most 24 per orbit | `77/9` |
| 5 | 2,088,630 compatible extension pairs | at most 143 per orbit | `163/20` |

The five-line result is slightly stronger than the fixed-triangle audit in
one direction: non-fixed cliques can reach `163/20`, above the fixed
triangle's `127/16`, but still far below `53/6`.

Purely proportional pencils are excluded from the non-collinear
normalization and checked separately.  Their exact optima for line counts
three through eight are

```text
22/3, 20/3, 31/5, 88/15, 118/21, 38/7,
```

so they also cannot improve the three-line amplifier.  A mixed clique with
at least one nonproportional difference is represented by a nonproportional
base triangle and is included in the extension census.

## 4. Reproduction

The standalone probe is

```text
scripts/probes/probe_rate_quarter_mu16_multiline_barrier.py
```

It uses SciPy only to locate a floating-point LP vertex.  Before accepting a
result, it rationalizes every nonzero entry and checks all primal or dual
equalities and inequalities with Python `Fraction`.  The fixed-triangle mode
requires matching exact primal and dual objectives.

Run the fixed audit and global triangle audit with

```bash
python3 scripts/probes/probe_rate_quarter_mu16_multiline_barrier.py
python3 scripts/probes/probe_rate_quarter_mu16_multiline_barrier.py --global-triangles
```

Run the four- and five-line orbit census with

```bash
for i in 0 1 2 3 4 5 6 7 8; do
  python3 scripts/probes/probe_rate_quarter_mu16_multiline_barrier.py \
    --global-four-orbit "$i"
  python3 scripts/probes/probe_rate_quarter_mu16_multiline_barrier.py \
    --global-five-orbit "$i"
done
```

The Lean barrier is

```text
Frontier/_RateQuarterMultiLineOwnershipBarrier.lean.
```

## 5. Exact remaining gap

This closes the **fixed-triangle LP question** exactly and rules out six or
more lines under the pair-cap hypothesis in the kernel.  It does not prove a
global lower bound for delta star.

The non-fixed four/five-line statement remains computational for two precise
reasons:

1. A four-prime survivor intersection is not a symbolic classification over
   `Q(zeta_16)`.  A final theorem would enumerate the cyclotomic identities
   directly or prove that reduction at the selected primes is complete.
2. The rational LP dual certificates are checked exactly by the probe but
   are not yet imported as finite Lean certificates.

The census also concerns universal `mu_16` identities.  Characteristic-
specific cliques existing only at the prize prime, higher-degree pair
locators, or an architecture violating the `4m` pair-core cap are separate
search spaces.  Those are the only ways a multi-line common-factor route can
still evade this barrier.
