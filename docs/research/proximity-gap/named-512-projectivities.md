# Six projective matches on the two named order-512 subgroups

At either designated prime, let $H$ be the 512th roots of unity. A projectivity
sending seven distinct points of $aH$ into $bH$, for any nonzero $a,b$, is
a scaling or a reciprocal scaling. Six matches are attainable by a
projectivity of neither form. The result applies to all dyadic subgroups
of order at most 512, with the same sharp maximum at orders at least eight.

In fact **every equality between two ordered four-point cross ratios on
$H$ lifts to the complex 512th roots with the same exponents**. The
[general seven-site determinant estimate](dyadic-joint-minor-transfer.md#seven-matches-for-an-arbitrary-projectivity)
gave a sufficient characteristic of $2^{222}$ already at order 256.
Neither designated prime meets that sufficient condition. The proof below
uses the two actual field reductions. It makes no transfer claim for the
full $2^{30}$-site domains.

## Certifying every ordered comparison

Fix a primitive root $g$ of order $N$, with $N=256$ or 512, and use
$$[x,y;u,v]=\frac{(x-u)(y-v)}{(x-v)(y-u)}.$$
Translate the exponents of an unordered four-set to put one point at 0.
The four positive cyclic gaps sum to $N$. Changing the initial point rotates
the gap tuple, and inverting all points reverses it up to rotation. Both
multiplication by a root and inversion preserve ordered cross ratios.
Enumerate the lexicographically least gap tuple in each dihedral orbit.
On its four points it suffices to fix the first entry and permute the other
three: the Klein four permutations preserving a cross ratio act transitively
on the distinguished entry. Thus six ratios per orbit include every ordered
value. The verifier checks the sum of all gap orbit sizes against
$\binom{N-1}{3}$ and separately checks the four-set orbit count by Burnside.

For each finite-field residue remember one ordered tuple. On every repeated
residue, compare the two formal cross ratios by clearing denominators.
The numerator difference is a difference of products of four binomials,
so its integer coefficient one-norm is at most 32, also after reduction
modulo $X^{N/2}+1$. For this exact comparison evaluate the roots as
$64^j$ in $\mathbb Z/(64^{N/2}+1)$. The reduced numerator has absolute
integer value at 64 strictly below $64^{N/2}+1$; if nonzero, its highest
nonzero digit dominates the lower digits since the coefficient one-norm
is at most 32. Hence zero in this finite ring is **equivalent** to zero
at the complex primitive root. No division or probabilistic fingerprint
is used for the formal equality. The lookup table resolves machine-hash
collisions by recomputing the full prime-field ratio.

| Order | Unordered gap orbits | Ordered comparisons to register | Distinct field values | Repeat comparisons |
|---:|---:|---:|---:|---:|
| 256 | 345,472 | 2,072,832 | 2,001,387 | 71,445 |
| 512 | 2,779,904 | 16,679,424 | 16,389,099 | 290,325 |

The counts are per designated prime. In each case every repeat lifts.
For a negative control the same routine on the 16th roots of $\mathbb F_{17}$
at primitive root 3 finds cross ratio 12 at exponent tuples $(0,4,1,2)$
and $(0,1,2,5)$. The cleared complex comparison is nonzero.

## Reconstructing the projectivity

Divide input and output by $a$ and $b$ respectively. Three matched pairs
determine a unique complex projectivity on the corresponding dyadic roots.
For each fourth matched pair, equality of the two ordered cross ratios lifts
by the certificate; injectivity of the cross-ratio coordinate then forces
the same complex projectivity to match that pair. With seven matches the
[complex seven-site theorem](six-dyadic-projective-matches.md) makes that
map $x\mapsto tx$ or $x\mapsto t/x$. Its multiplier is itself a dyadic
root, as one matched pair determines it. The resulting exponent differences
or sums give the same scaling or reciprocal scaling at the designated prime,
where uniqueness on three points identifies the original map. Containment
gives the conclusion for smaller dyadic subgroups.

For sharpness take $u=g^{N/8}$. The projectivity taking $1,u,u^2$ to
$1,u,u^3$ is neither a scaling nor a reciprocal scaling: a scaling fixing
1 is the identity and inversion does not fix $u$. The program scans its
actual graph on all $N$ sites. Its six matches, in exponents of $u$, are
$(0,0),(1,1),(2,3),(3,5),(4,6),(6,7)$.

In particular a non-dihedral involution on this subgroup has at most three
disjoint transpositions. At three transpositions the lift is itself an
involution, since its square fixes the six sites. The complex
[three-pair shape classification](dyadic-three-pair-shapes.md) consequently
applies to these six exponents in each designated field. This supplies the
pair geometry on the 512-site quotient without assuming its much larger
general characteristic bound.

Run `python3 scripts/probes/probe_named_projective_cross_ratios.py` to check
both named order-512 grids and the negative control; use `--order 256` for
the shorter run. Both use the Python standard library.
