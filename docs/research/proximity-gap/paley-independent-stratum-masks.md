# Independent selections across different product strata

Let $q$ be the generator of the order-$n=2^{30}$ subgroup $H$ at the second
prize prime. Its quadratic character is $-1$. Write
$A_s=\{x+s/x:x\in H\}\setminus\{0\}$. For $1\le K\le n/2$, the sets
$q^jA_s=A_{q^{2j}s}$ for $0\le j<K$ are disjoint, since a nonzero sum
of two subgroup elements determines its product. Each has $n/2$ points.
Taking initial $s,t$ of opposite exponent parity makes the entire two runs
disjoint: every source product differs from every target product. Write
$S(A,B)=\sum_{x\in A,y\in B}\chi(x-y)$.
[Named generator](../../../ArkLib/Research/ProximityGap/Frontier/PaleyCosetCancellation.lean) ·
[Product uniqueness and its computational premise](paley-product-traces.md#a-single-stratum-against-two-reciprocal-products)

## Arbitrary subsets of two runs

Take any nonempty seeds $X\subseteq A_s$, $Y\subseteq A_t$, and form
$U=\bigcup_{i<K}q^iX$, $V=\bigcup_{j<K}q^jY$. Independently choose any
$A\subseteq U$, $B\subseteq V$ of positive relative densities
$\alpha,\beta$. With $[x]_+=\max(x,0)$,
$$
\frac{|S(A,B)|}{|A||B|}
\le 1-
 \left[2-\frac{1+1/K}{\alpha}\right]_+
 \left[2-\frac{1+1/K}{\beta}\right]_+ .
$$
At $K=2^{20}$, densities at least $3/4$ give a bound below **0.556**.
Indeed simultaneous dilation changes the sign of the character sum. In
the difference of the sums on $A\times B$ and $qA\times qB$, the shared
entries cancel. The two remaining pieces have equal size. This gives
$|S(A,B)|\le |A||B|-|A\cap qA||B\cap qB|$. Finally,
$|A\cap qA|\ge2|A|-(K+1)|X|$, since $A\cup qA\subseteq U\cup qU$.
The same argument applies to $B$. At density exactly $1/2$ and even $K$,
the union of the even-indexed layers has empty intersection with its
$q$-dilate, since the product orbit has even period $n/2$. Thus the overlap
bound alone supplies no saving there.

There is also a monochromatic control on the actual second prime. Use
$K=16$, the singleton seeds $X=\{2\}\subset A_1$ and
$Y=\{q^{44718}+q^{1-44718}\}\subset A_q$, and select the even
layers in each run. All 64 differences on this $8\times8$ rectangle are
nonsquares, so its relative discrepancy is one. The kernel calculation
reduces the 64 signs to 15 modular powers, since each row dilation is a
square. This small control precludes a general strict half-density bound
uniform in $K$; it makes no claim about half-density at $K=2^{20}$.

## A power saving with sparse, irregular selections

Put $K=2^r$. For each $x\in X$, independently choose any subcollection
of the pairs $(q^{2i}x,q^{2i+1}x)$ for $0\le i<K/2$. Their union is $A$.
Let $a_x$ be the number of retained sites on this fiber, and write
$\bar a=|A|/|X|$. For each $y\in Y$ independently choose one of the two
Rudin–Shapiro sign sequences of length $K$, or the negative of either.
Keep $q^jy$ exactly where this sequence has sign $+1$, giving $B$.
Set $\beta=|B|/(K|Y|)$. Then
$$
\frac{|S(A,B)|}{|A||B|} \le
 \frac1{2\beta K}+\frac1{\beta\sqrt{\bar a}},
 \qquad |A||B|>0.
$$
The source decisions can differ at every pair and for every initial site.
The bound is uniform over all these choices, including a source selected
after seeing the target. It saves a power when $\bar a$ grows as a power
and $\beta$ is bounded below. No lower bound on each separate $a_x$ is
needed. The seeds and all decisions at distinct sites can be independent.

At $K=2^{20}$ each of the two positive sign sequences has coefficient sum
$1024$. Thus $\beta\ge (K-1024)/(2K)$. If $|A|\ge K|X|/2$, then
**$|S(A,B)|<0.0028|A||B|$**. When both seeds are full nonzero strata,
the two carriers each have $2^{49}$ sites. Choosing opposite product
parities makes every contributing rectangle a mixed one. For an isolated
pair of prescribed products the construction has no long run, so this
estimate leaves the individual mixed sums open.

For the proof, fix $x,y$ and put $h(d)=\chi(x-q^d y)$ for
$1-K\le d\le K-1$. At $(q^ix,q^jy)$ the character is $(-1)^i h(j-i)$.
Write $a_i\in\{0,1\}$ for the source choice and $b_j=(1+w_j)/2$ for
the target choice. The doubled local sum splits into $C+R$, corresponding
to the constant $1$ and the sign $w_j$. For a retained pair starting
at $i=2l$, its contribution to $C$ telescopes to
$h(K-i-1)-h(-i-1)$. Hence $|C|\le a_x$.

The two sign sequences start at $P_0=Q_0=(1)$ and are obtained by
concatenation, $P_{r+1}=(P_r,Q_r)$ and $Q_{r+1}=(P_r,-Q_r)$. On the
cyclic group of order $2K$ let
$L_w v(d)=\sum_{0\le j<K}w_j v(d+j)$. For any input,
$$
 \sum_d (L_{P_r}v(d))^2+\sum_d (L_{Q_r}v(d))^2
       =2K\sum_d v(d)^2.
$$
In each recursion step, the two new operators add or subtract the same
translate of $L_{Q_r}v$ from $L_{P_r}v$. The parallelogram identity doubles
the energy, since translation preserves its sum. This argument also gives
the usual Fourier bound $\sqrt{2K}$ for each sign sequence.
[Rudin–Shapiro recurrence](https://arxiv.org/abs/1909.08777)

Extend $h$ by zero at the unused lag $K$ modulo $2K$.
Put $v(i)=(-1)^i a_i$ on the index interval and zero elsewhere.
Then $R=\sum_d h(-d)L_w v(d)$. All actual differences remain distinct
as lags modulo $2K$. Cauchy–Schwarz gives $R^2\le4K^2a_x$, also for the
negative of either sequence. Summing over seeds, the total constant term
has size at most $|A||Y|$. A further Cauchy–Schwarz gives
$R_{\rm total}^2\le4K^2|Y|^2|X||A|$. This proves the displayed bound.
For the named numerical inequality, $724^2\le 524288$ and
$10000(724+2K)<28\cdot1448\cdot523776$.

## Full orbits and independently chosen ordinary subsets

The full nonzero sumset splits into the cosets $(1+q^j)H$,
$0\le j<n/2$. The product parity equals $j$ modulo two, and each stratum
of that parity contributes an antipodal pair to the coset. Thus each parity
has $n/4$ disjoint cosets. Choose any nonempty collections of these cosets
on the two opposite parities, and choose representatives $X,Y$. The source
can use an arbitrary indicator $a_x(i)$ for each full orbit
$q^ix$, $i\in\mathbb Z/n$. Write
$\Delta=\sum_{x\in X}|\sum_i(-1)^ia_x(i)|$. Independently choose a positive
Rudin–Shapiro mask of length $n$ on each target coset, allowing the same
four choices as above. With $\beta=|B|/(n|Y|)$ and $\bar a=|A|/|X|$,
$$
 \frac{|S(A,B)|}{|A||B|}
 \le \frac{\Delta}{2\beta |A|}+\frac1{\beta\sqrt{2\bar a}}.
$$
Indeed the constant term for each coset pair factors as
$(\sum_i(-1)^ia_x(i))(\sum_d h(d))$. The lag function now lives on just
$n$ sites, so the complementary energy gives $R_{xy}^2\le2n^2a_x$.
Summation and Cauchy–Schwarz give the inequality. At the second prime
$\sqrt n=32768$. Each target mask has size at least $(n-32768)/2$, by the
two-step recurrence for the coefficient sums. If each source coset retains
equal numbers of even and odd exponents and the global source density is
at least $1/2$, the relative discrepancy is at most $2/(32768-1)<0.000062$.
The locations selected within each parity can be arbitrary.
[Coset partition](paley-product-traces.md#between-two-different-products)

There are also independently selected families with **exactly zero**
discrepancy and arbitrary target residues. Fix an even divisor $d$ of $n$.
On each source coset select the same number $c_x$ of exponents from every
residue class modulo $d$, with arbitrary positions in each class. On each
target coset choose an arbitrary union of residue classes modulo $d$,
requiring equal numbers of even and odd selected residues. Let its indicator
be $b_y$. For each lag $\ell$ the coefficient of $h(\ell)$ is
$$
 \sum_i(-1)^i a_x(i)b_y(i+\ell)
 =c_x\sum_{r\bmod d}(-1)^r b_y(r+\ell)=0 .
$$
Hence the result holds even for different choices on every coset and every
source fiber. It needs no estimate on any mixed character row.

In particular take $d=n/2$ and pick one point from each antipodal pair on
each source coset. On the target side one may prescribe just the two strata
$A_t,A_{q^2t}$. In each target coset they contribute two antipodal pairs
whose exponent residues differ by one. Independently choose both pairs
or neither. The discrepancy is exactly zero. With all cosets of the
opposite parity in the source and all target pairs, the two sizes are
$n^2/8=2^{57}$ and $n=2^{30}$. A single product stratum contributes just
one residue modulo $n/2$ to each of its cosets, so a nonempty target
supported on only that stratum fails this balance condition.

Lean checks the character phase, telescoping, the complementary energy for
every finite abelian group, the residual and aggregate inequalities, the
named run margin, the independent-rectangle overlap estimate, and exact
periodic cancellation for a homomorphism between finite abelian groups.
The set-to-mask identifications and their combination are given above.
The control probe compares all terms with literal field-character rectangles
for 24 independently selected pairs in $\mathbb F_{100129}$, checks the
full-orbit masks and exact residue constructions at four periods, tests
energy on additional integer inputs, and constructs the length-$2^{20}$
coefficients. The first named subgroup consists of squares, so dilating by
its generator leaves the constant target term with the same sign.
[Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/PaleyMaskedStrata.lean) ·
[Exact controls](../../../scripts/probes/probe_paley_masked_strata.py)

## Which masks cancel every possible mixed lag row?

Let $n=2^r$, $r\ge1$, and let $A,B$ be nonempty exponent subsets of
$\mathbb Z/n$. For $1\le j\le r$ say that $A$ is **balanced at level $j$**
when its counts in residues $u$ and $u+2^{j-1}$ modulo $2^j$ agree for
every $0\le u<2^{j-1}$. Level one just compares the even and odd totals.
The following three conditions are equivalent.

1. For every lag function $h$, the sum
   $\sum_{i\in A,j\in B}(-1)^i h(j-i)$ is zero.
2. Both sets are balanced at level one. At each higher level, at least one
   of the two sets is balanced at that level.
3. Both sets are balanced at level one, and the ordinary difference count
   $N_d=|\{(i,j)\in A\times B:j-i=d\}|$ is constant for all $d$.

To see this, put $P(X)=\sum_{i\in A}X^{-i\bmod n}$ and
$Q(X)=\sum_{j\in B}X^j$. The coefficient of $X^d$ in $P(-X)Q(X)$ modulo
$X^n-1$ is the signed number of representations at lag $d$. Testing the
indicator of each single lag proves the first equivalence with divisibility
by $X^n-1$. Its linear factors $X-1,X+1$ force both parity balances because
$P(1),Q(1)>0$. The higher factors $X^{2^{j-1}}+1$ are irreducible over the
rationals and are unchanged by $X\mapsto-X$. Each must divide $P$ or $Q$.
Reducing a mask polynomial modulo that factor gives exactly the differences
of its counts in the corresponding opposite residues. Reversing exponents
permutes those pairs and preserves whether the two counts agree. Finally
$N_d$ is constant precisely when $(X-1)P(X)Q(X)$ vanishes modulo $X^n-1$,
since multiplication by $X-1$ takes adjacent differences. Under the two
parity balances this last test has exactly the same remaining factors.
[Formal finite-mask equivalences](../../../ArkLib/Research/ProximityGap/Frontier/PaleyDyadicMasks.lean)

For ordinary masks, constant $N_d$ equals $|A||B|/n$. Exactly half of its
representations have even source exponent and half have odd source exponent.
In particular **$2n$ divides $|A||B|$**. This divisibility is sharp even
with independent choices on both sides. Give the two sides a common free
least-significant bit, and partition the remaining bit positions between
them. To construct each mask, proceed from low to high bits. At every free
bit extend each current prefix in both ways. At all other bits choose one
extension independently for each current prefix. Each free bit balances its
corresponding level, since every surviving prefix subsequently acquires the
same number of descendants. The two cardinalities multiply to $2n$.
Each lag therefore has exactly one representation of each sign. Different
coset representatives may use independent trees with the same allocation of
free bits. More generally level two and above may be allocated arbitrarily
provided one entire side balances the assigned level across its cosets.
For classical mask-polynomial tools in translational tilings see
[Coven and Meyerowitz](https://arxiv.org/abs/math/9802122) and
[Kiss, Łaba, Marshall and Somlai](https://arxiv.org/abs/2507.11672).

At the second prime take the 15 even bit positions $0,2,\ldots,28$ free on
the source, and the 16 positions $0,1,3,\ldots,29$ free on the target.
The resulting arbitrary tree choices select $32768$ ordinary source sites
and $65536$ ordinary target sites per opposite-parity coset pair. For example
one can use seeds $2$ and $1+q$. Their actual field-character discrepancy
is exactly zero, by the sign identity $\chi(q^ix-q^jy)=(-1)^i h(j-i)$.
The criterion classifies cancellation uniform over *all* choices of $h$.
The arithmetic character row may permit additional cancellations. At the first
prime the generator has positive character. The constant test $h=1$ then
gives $|A||B|$ for every nonempty pair, so a row-uniform argument there
requires additional arithmetic information on the actual lag function.
The control exhausts every nonempty pair of masks at lengths 2, 4 and 8.
It also constructs the full-size independent masks and checks 52 individual
lags directly. The equivalence supplies all lags, including those outside
that finite control. [Reproduction](../../../scripts/probes/probe_paley_masked_strata.py)

## Why the single-stratum fourth-moment factorization stops

For distinct nonzero products $s,t$, the phase numerator in ratio and
product coordinates is $F(U,V)=UV-V-tU+s$. Its translates under nonzero
multipliers are
$$
 F(aU,bV)=b(aU-1)V-(taU-s).
$$
They are absolutely irreducible. The two coefficients as a polynomial in
$V$ have coprime linear factors in $U$, because $s\ne t$. The polynomial
is primitive and has degree one over the rational function field. The
different translates have distinct roots as rational functions of $U$:
the pole $1/a$ recovers $a$ and the value at zero recovers $b$ because
$s\ne0$. Equivalently their constant and linear coefficients distinguish
them up to scalar. Consequently a product of distinct translates cannot
equal $f(U)g(V)$ times a rational square: at each such mixed irreducible
its valuation is odd, while the proposed right side has even valuation.

For a lifted four-corner rectangle with source and target multiplicative
steps $L,M$, the four pairs of translation factors are
$(1,1),(L,L),(M^{-1},M),(L/M,LM)$. A repeated pair requires $L=1$,
$M=1$, or $L=M=-1$ in odd characteristic. In these degenerate cases all
factors occur with even multiplicity. This rules out the one-dimensional
fourth-moment separation by multiplicative shifts in these coordinates.
It is an identity in the rational function field and does not determine
quadratic-character sums on any particular finite subgroup.
