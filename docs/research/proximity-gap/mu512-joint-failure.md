# The first dyadic failure of joint locator transfer is at 512 roots

For either named prime separately, order 256 is the first dyadic order with a nonlifting two-site locator comparison. For the two primes together, with matching exponent labels at their designated roots, the first such order is **512**. At that order the negative conclusion holds for every independent choice of primitive finite-field roots. The two locators have disjoint supports and equal degree. [Single-prime examples](mu256-actual-locator-counterexamples.md) · [Joint positive theorem at 256](mu256-joint-transfer.md)

Write $L_S(X)=\prod_{j\in S}(X-z^j)$ and $R=L_P/L_Q$. The following bounds each apply to some common choice of $P,Q$ for the two primes. The value of $R$ is constant across the two sites in each finite field. Its two complex absolute values differ. Rotation and multiplication of exponent labels by any odd unit allow every displacement of the indicated order.

| Order of the quotient of the two sites | Example exponent displacement | Degree of each reduced locator, at most | Degree after pullback to length $2^{30}$ |
|---|---:|---:|---:|
| 4 | 128 | 121 | 253,755,392 |
| 8 | 64 | 116 | 243,269,632 |

In each row $R(X^{2^{21}})$ is constant on two full production fibers, totaling **4,194,304** sites, in both fields. The fibers have different complex magnitudes. The proof gives existence by counting. The production decision requires three disjoint full split fibers.

## Counting different complex magnitudes

Fix the sites $1,z^h$. A single support index $j$ contributes $c_j=(1-z^j)/(z^h-z^j)$ to the normalized value. Its complex magnitude is a product of $|1-z^r|$ for the 128 odd representatives $1\le r<256$. For $d=2^a b$ with $b$ odd, factor $1-z^d$ as the product of $1-z^{b+t\,512/2^a}$ for $0\le t<2^a$, then fold the exponents modulo sign. Subtracting the exponent column for $j-h$ from the one for $j$ gives an integer vector $A_j$. Different integer signatures give different positive real magnitudes by the multiplicative independence of the primitive dyadic chord lengths. [Chord independence](quarter-dyadic-parity.md)

Among the 510 unmarked indices the reflection $j\mapsto h-j$ has two fixed sites and 254 pairs. The fixed sites have magnitude one, and $A_{h-j}=-A_j$. On each pair, choosing neither, one member, or the other realizes digits $0,1,-1$ in its signature. Every ternary signature has a support of **exactly 254** indices. A representation that uses $b$ singletons can add both members of $\lfloor(254-b)/2\rfloor$ unused pairs and one fixed site if $254-b$ is odd.

For any list of integer vectors $A$, the number of distinct ternary sums is at least
$$
  \sum_{J\text{ linearly independent over }\mathbb Q}2^{|J|}.
$$
Induct on the number of vectors. A zero column changes neither side. For a nonzero column $v$, project the previous sums along $\mathbb Qv$. On every occupied line, translating its two extreme points by $-v$ and $v$ adds two points outside the previous set. The number of previous occupied lines is the ternary sum count for the projected family. Independent sets containing $v$ correspond to independent sets after deleting $v$ and projecting. This proves the inequality. Every independent set modulo 3 is independent over $\mathbb Q$, as witnessed by a minor nonzero modulo 3. [Lean proof of the two-extremes bound](../../../ArkLib/Research/ProximityGap/Frontier/TernaryProjectionCount.lean)

## The finite count

Use one column from every reflected pair. Split the 128 row coordinates recursively by their odd label modulo sign, using moduli $4,8,16,32,64,128$. At a node with coordinates $I$, assign every column supported in $I$ that belongs to neither child. Its boundary space $B_I$ is the span over $\mathbb F_3$ of the restrictions to $I$ of all exterior columns. For an independent choice of interior columns, only the intersection of its span with $B_I$ is needed above that node.

The two children have disjoint coordinates. Combine their states by direct sum and multiply their counts. Each newly assigned column can be omitted with weight one or included with weight two if it increases rank. Its restriction in each child lies in that child's boundary. This also holds for every parent boundary vector. Consequently all of the tests use only the two stored intersections. After adding the node's columns, intersect with $B_I$ for the outgoing state. At the root the exterior is empty. The verifier enumerates all vectors in each boundary when computing that intersection. The maximum boundary dimension is four. [Exact standard-library Python verifier](../../../scripts/probes/probe_mu512_joint_failure.py)

| $h$ | Weighted independent subsets modulo 3 (lower bound on complex signatures) | Distinct signatures in one joint finite fiber, at least |
|---:|---:|---:|
| 128 | 162556511019802226186357332579493573469778017126698240931258039194500582915358827449381351470947265625 | 608,830 |
| 64 | 38023273840781151259760254827747883671613127455648285081482627480810178111853759865585931436920166015625 | 142,410,130 |

For each distinct magnitude select one support of weight 254. The joint finite value of $L_S(1)/L_S(z^h)$ has at most $(p_1-1)(p_2-1)$ possibilities. Pigeonholing gives the last column, for any primitive roots in the two fields. Two supports in the same fiber, after canceling their intersection, give locators of degree exactly half their Hamming distance. Their complex magnitudes still differ.

## Two distance certificates

For $h=128$ encode the supports by sign vectors of length 510, with pairwise inner products $t=510-2d$ at Hamming distance $d$. If every distinct pair has $d\ge244$, then $t\le22$ and $f(t)=(t-22)(t+23)^2\le0$. For a code of size $M$, summing $f$ over all ordered pairs gives at least $602M^2$. Indeed $t$, $t^2-510$, and $t(t^2-510)$ are Gram kernels, the latter two from off-diagonal quadratic features and their products with linear features. In the expansion $f(t)=t(t^2-510)+27t+24(t^2-510)+602$, each kernel has nonnegative total sum. Only diagonal terms can contribute positively, and $f(510)=138635432$. Thus $M\le230291$. The fiber has 608,830 members and every distance is even, so some pair has $d\le242$. [Lean cubic bound](../../../ArkLib/Research/ProximityGap/Frontier/LocatorBinaryCubic.lean)

For $h=64$ use the distance polynomial $F(d)=\prod_{r\in T}(r-d)$ for $T=\{234,252,254,272,274,316,318\}$. It is nonpositive at every even distance in $[234,510]$. Its expansion $F=\sum_{j=0}^7 a_j K_j$ in binary Krawtchouk polynomials has all $a_j\ge0$ and $a_0>0$. The verifier reconstructs the rational coefficients exactly and checks the identity at every integer from 0 to 510. For sign vectors at distance $d$, $K_j(d)$ is the inner product of the squarefree degree-$j$ sign features, by grouping the $j$-subsets according to their overlap with the differing coordinates. Thus $M^2a_0\le M F(0)$ if all distances are at least 234. The exact floor is **123,094,846**. The fiber exceeds this, giving distance at most 232. [Delsarte’s original monograph](https://users.wpi.edu/~martin/RESEARCH/philips.pdf) · [Polynomial and integer checks](../../../scripts/probes/probe_mu512_joint_failure.py)

Orders dividing 256 inherit the joint positive theorem by restricting its roots. This proves the asserted first failure. Lean checks the two-extremes lemma and the cubic distance certificate. The degree-seven distance certificate and the finite-state count have exact executable verifiers. The written proof combines these with primitive chord independence.
