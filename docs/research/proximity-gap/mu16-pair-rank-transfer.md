# Sixteen-site half-rate lists over smaller residue fields

Let $K$ contain a primitive sixteenth root $z$, let $p$ be its characteristic
and put $Q=|\mathbb F_p(z)|=p^{\operatorname{ord}_{16}(p)}$. If
$Q>3\,060\,803\,059\,969$, every five-error ball on the sixteen sites has
at most three degree-seven words, at every positive interleaving width.
Three occur, and a six-error ball contains four. For a budget-three field
this gives first failing list counts **6, 8, 11, 12** in decreasing rate
order and MCA counts **3, 3, 3, 3**. In particular the table holds whenever
$[K:\mathbb F_p(z)]\le3$, since $|K|\ge3\cdot2^{128}$ exceeds the cube
of the bound. The previous uniform condition was $Q>2^{109}$.
[All four rates, lower witnesses and coset transport](sixteen-all-rate-thresholds.md)

Examples newly covered are the quadratic field of characteristic
$31\cdot2^{60}+1$ and the cubic field of characteristic $305\cdot2^{35}+1$.
Each prime is 1 modulo 16. For both Proth numbers, 3 raised to half the
predecessor is $-1$, certifying primality. Their field sizes lie in
$[3\cdot2^{128},4\cdot2^{128})$.

## Which ranks must survive reduction?

Use the existing [five-pivot support and compatibility theorem](mu16-septic-list-large-characteristic.md).
Two full words choose six roots each among the eleven outside sites and
agree on all five pivots. Their root sets meet in one or two places:
the eleven-site union forces at least one and distinct degree-seven
words have at most seven common values. After cancellation the disjoint
locator degrees are $(5,5)$ or $(4,4)$. A full and partial word choose
six and seven roots and agree on four pivots, giving degrees $(4,5)$
or $(3,4)$. Two partial words choose seven roots each and share at
least three pivots, giving $(4,4)$ or $(3,3)$.

Write $F,G$ for the two reduced locators and $y$ for a pivot. A full
word contributes columns $F(y),yF(y)$; a partial one contributes just
its locator. Signs on entire columns do not affect absolute norms.
For the extra nonvanishing test on a full/partial pair, the partial
column can be zero on one extra row. Locators, sites and differences
of distinct sixteenth roots have odd absolute norm one. This covers
one-column minors, two columns from the same word, and a two-by-two
minor with an erased entry. For two distinct words' single columns,
remove a common unit from each row to leave the relative exponent
$-1$, $0$ or $1$. For three columns take a repeated full locator and
one singleton. The latter can carry $y$ for full/full pairs; the
full/partial test includes each possible erased singleton entry.

For two full words with distinct pairwise locator ratios the previous
proof checks existence of a projectivity on **all five** pivots. The
matrix with rows $(F,yF,G,yG)$ has five rows and four columns. A
rank-four matrix can drop rank only if every one of its five maximal
minors vanishes under the same reduction. For a nonzero algebraic integer
that vanishes in $\mathbb F_p(z)$, its absolute norm is divisible by $Q$.
As $p$ is odd, $Q$ divides its odd part. Thus the common gcd of the five
odd norms bounds $Q$ whenever a rank drop occurs. Take gcd with zero in
the usual way; an identically zero set of maximal minors stays zero.

In rank at most three the smaller minors below preserve the rank. Whether
two ratios coincide is also preserved by the smaller minors. In the
nonconstant case any three distinct pivot/ratio pairs determine a unique
projectivity, whose nonsingular reduction follows from their preserved
distinctness. The existing compatibility proof for triples therefore uses
the same constant/projective tests and the same good reduction of the
three projectivities. It does not require every individual four-row minor
of an incompatible five-row pair to stay nonzero. The unaltered support
and interleaving arguments transfer the known characteristic-zero list
decision.

## Integer certificate

| Test | Greatest odd norm or common gcd |
| --- | ---: |
| Two rows, distinct locators | 36,740,277,089 |
| Three rows, including mixed-pair nonvanishing | 3,060,803,059,969 |
| An individual four-row full/full minor | 33,844,696,351,656,961 |
| Five rows, gcd of maximal minors, degrees 4 and 4 | 13,786,369 |
| Five rows, gcd of maximal minors, degrees 5 and 5 | 43,046,721 |

The probe ranges over all disjoint reduced root sets of the specified
degrees outside the chosen pivots. This is a superset of the feasible
supports. Translation of exponents multiplies columns by units, and
an odd dilation applies a cyclotomic automorphism. Both preserve all
odd norms, including for the erased-row tests. The probe takes one
representative of each pivot-set orbit and enumerates every ordered pair
of disjoint locators there. For four or five rows the two word blocks are
interchangeable, so it takes one order. It checks 19,704,069 individual
minors and 336,567 five-row matrices.

The census computes in $\mathbb Z[z]/(z^8+1)$. Expanding a repeated
column pair gives $F(x)F(y)(y-x)$. The coefficient 1-norm of a
degree-at-most-five locator evaluated at a root is at most 32, so that
of any four-row determinant here is at most $6\cdot(2\cdot32^2)^2$.
Signed 64-bit arithmetic suffices before the field norm. Successive
quadratic norms take $E(z^2)+zO(z^2)$ to $E(z^2)^2-z^2O(z^2)^2$;
the implementation drops only rational powers of two and checks the
wide integer multiplications and additions for overflow. The independent
Python check uses the ordinary determinant expansion and fraction-free
elimination on the eight-dimensional multiplication matrix for each
reported maximizing example. It also verifies orbit counts, the two
field examples and the strict bound for degree three.

Run from the repository root:

```sh
python3 scripts/probes/probe_mu16_pair_minor_norms.py
```

[Enumeration](../../../scripts/probes/probe_mu16_pair_minor_norms.cpp) · [Independent witness and coverage checks](../../../scripts/probes/probe_mu16_pair_minor_norms.py)
