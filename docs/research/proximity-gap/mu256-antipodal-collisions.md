# At most eleven antipodal collisions for an asymmetric order-256 locator

Let $F$ be either named prime field and fix a primitive 256th root $z$.
Let $P,Q$ be disjoint subsets of $H=\mu_{256}(F)$ and
$R(T)=\prod_{a\in P}(T-a)/\prod_{b\in Q}(T-b)$. Call $\{x,-x\}\subset H$
a collision when both sites lie outside $P\cup Q$ and $R(x)=R(-x)$.
The values at different collision pairs can differ.

**Twelve collisions imply $P=-P$ and $Q=-Q$.** In fact, four collision
pairs already suffice when their exponent classes modulo 128 form a
parallelogram with four distinct vertices. A three-term progression of
collision pairs imposes an antisymmetry on the support differences.
No degree condition is required. The result concerns each designated
field individually and every choice of primitive root of its subgroup.

## The antipodal observation

Put $w_j=1_P(z^j)-1_Q(z^j)$ and $a_j=w_j-w_{j+128}$, extended by
$a_{j+128}=-a_j$. Write $C\subset\mathbb Z/128$ for the collision classes.
At a collision $x$, both weights vanish, so $a_x=0$. Set
$M=(p-1)/256$ and $d(j)=\log_g(1-z^j)\bmod M$ for $j\ne0$,
with $d(0)=0$. Here $g=3$ or $37$ is the designated field generator and
initially $z=g^M$. Factoring $z^x$ out of each evaluation factor gives
\[
 \sum_{j=0}^{127} a_j b_x(j)=0\pmod M,\qquad
 b_x(j)=d(j-x)-d(j+128-x),\quad x\in C.
\]
The zero placeholder is multiplied only by a zero source weight. The kernel
$b_x(j)$ is antiperiodic in each subscript. Since
$1-z^{-k}=-z^{-k}(1-z^k)$, it also satisfies
$b_{h-x}(h-j)=b_x(j)$. A simultaneous translation of the sites and source
preserves these identities.

## Four-site and three-site certificates

Suppose a reflection $j\mapsto h-j$ exchanges two distinct pairs in $C$.
Write $S_h a(j)=a_{h-j}$ on the 256-periodic extension. Both $a+S_ha$ and
$a-S_ha$ obey the observation equations at one representative of each
reflected pair. Let $E=\sum_{j=0}^{127}a_j^2$. The four protected sites
give $E\le124\cdot4=496$.

For odd $h$, translate the quartet to $\{0,r,s,r+s\}$, with $r$ odd and
$s\ne0$ even. One obtains this form by translating an even vertex to zero,
taking the other even vertex as $s$, and taking its reflected partner as
$r$. Translating by a side changes its sign independently of the other
side, so it suffices to take $r=1,3,\ldots,63$ and $s=2,4,\ldots,64$.
There are 62 free source pairs and zero fixed source classes.
For even $h$, translate the reflection to $j\mapsto-j$. The quartet is
$\{\pm r,\pm s\}$, where $1\le r<s\le63$. There are 61 free source pairs
and two fixed classes modulo 128. At 0 reflection acts on $a$ by $+1$,
and at 64 it acts by $-1$. Exactly one fixed coordinate survives in
each sector, with coefficient $1/2$ in its squared norm.

In both cases the compressed sector energies add to $2E$. On a free
orbit this is $(u+v)^2+(u-v)^2=2(u^2+v^2)$, also valid for a twisted
reflection $v\mapsto-v$. A fixed class contributes $(2u)^2/2$. At least
one sector therefore has energy at most 496. Each corresponding lattice
has only zero up to that bound. Thus $a$ has pure symmetry in the
other sector. The original $a$ then satisfies that sector's two equations
and has compressed energy $E/2$. The second lattice certificate gives
$a=0$. This last step uses $a$ directly and works with an even modulus.

For the progressions $c-r,c,c+r$ of distinct classes, translate $c$ to 0
and take $1\le r\le63$. The symmetric sector has 62 free source pairs.
The fixed class 0 is protected, and the fixed class 64 is antisymmetric.
Each free sum has absolute value at most four, so its squared norm is
at most $62\cdot16=992$. The two observations at 0 and $r$ have no
nonzero lattice point in that ball. We obtain $a_{2c-j}=-a_j$ for every
$j$. Two distinct midpoints modulo 128 give distinct axes modulo 256.
Composition of their antireflections yields a nonzero period, whose
generated subgroup contains the antipode. The antiperiodic integer
signal must therefore vanish. [Dyadic antireflections](../../../ArkLib/Research/ProximityGap/Frontier/DyadicAntiperiodicReflection.lean)

## Counting pairs of sites

Assume $a\ne0$. There is no four-vertex parallelogram in $C$, so unordered
pairs of distinct vertices in $C$ have distinct sums. Moreover all proper
three-term progressions in $C$ have the same midpoint. Two distinct
endpoint pairs about that midpoint would themselves form a forbidden
parallelogram. Hence there is at most one proper progression, up to reversal.

Color every unordered pair of distinct vertices of $C$ by its undirected
distance in $\{1,\ldots,64\}$. Two disjoint pairs of the same distance
give a parallelogram. Two pairs of that distance meeting at one vertex
give a three-term progression about their common vertex. Thus only one
distance can be repeated and it can occur only twice. If $k=|C|$ this
gives $\binom{k}{2}\le65$, hence $k\le11$. The Lean proof counts oriented
differences, assigning the two orientations of the self-inverse distance
separate tags. The proof and the identity for both fixed source classes
were independently replayed by con-leche with 5,978 accepted declarations.
[Kernel-checked counting and metric](../../../ArkLib/Research/ProximityGap/Frontier/DyadicPairedCenterDensity.lean)

The bound of eleven is attained for the two combinatorial restrictions. In $\mathbb Z/128$ take $\{0,2,22,48,52,58,66,67,79,90,95\}$. Its 55 unordered pairs have 54 distinct undirected distances. Only distance 38 occurs twice, on $\{0,90\}$ and $\{52,90\}$. Any improvement of the collision bound must therefore use additional information about locator evaluations. Realization of these eleven classes by an asymmetric locator is open.

Because $w$ is ternary with disjoint supports, $a=0$ says that $P$ and $Q$
are each unions of antipodal pairs. Consequently $R(T)=R_0(T^2)$ for a monic
order-128 locator quotient. A change of primitive root permutes the classes
by a unit modulo 128, preserving all parallelograms and all progressions.
The four-site, three-site and cardinality conclusions thus apply for any
primitive root.

## Consequences for constant fibers

* Take five sites in an odd-step exponent progression and add the antipodes
  of its first four sites. Constancy on these nine sites first forces
  $a=0$ by the four-site theorem. The five squared sites are an odd-step
  progression on $\mu_{128}$. Each comparison for the descended quotient
  transfers to characteristic zero, where five such sites force both
  reduced supports empty. [Order-128 transfer](mu128-unit-ellipsoid-transfer.md) · [Five-site theorem](five-dyadic-centres.md)
* If a degree-63 pencil had three disjoint full fibers of size 63 on
  $\mu_{256}$, each fiber could contain at most eleven complete antipodal
  pairs. Indeed the other two monic fiber locators have constant ratio
  on it, and their odd degrees exclude antipodal supports. The three
  fibers together occupy 189 sites, so at least $189-128=61$ antipodal
  pairs are filled twice. At most 33 of these are monochromatic. At least
  **28** have different fiber labels at their two ends. The existence of
  such a pencil remains open.

## Finite reproduction

Run `python3 -O scripts/probes/probe_mu256_paired_centers.py --jobs 2` with
`python-flint` and a C++17 compiler. The verifier first certifies the named
primes, generators, primitive roots and the full logarithm table by exact
modular powers. It then constructs the complete congruence lattice at
each shape, using an invertible minor when possible and otherwise taking
successive exact single-row kernels. Integer basis reduction is checked
by its unimodular transform. The integer search exhausts an outward
approximation of the exact rational Gram–Schmidt ball. Its exclusion of
nonzero candidates certifies the closed ball in the original metric.
[Verifier](../../../scripts/probes/probe_mu256_paired_centers.py) · [Integer search](../../../scripts/probes/probe_mu256_joint_transfer.cpp) · [Unit logarithms](../../../scripts/probes/mu256_unit_logs.json)

| Axis and marked shape | Shapes per field | Sectors per shape | Squared radius |
| --- | ---: | ---: | ---: |
| Odd axis, four protected pairs | 1,024 | 2 | 496 |
| Even axis, four protected pairs | 1,953 | 2 | 496 |
| Midpoint and its two neighbors | 63 | 1 | 992 |

This gives 12,034 exact lattice checks across the two fields.
