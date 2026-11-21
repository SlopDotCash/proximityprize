# Recovering Paley character sums from an interpolation determinant

Fix an odd prime $p$, put $d=(p-1)/2$, and let $\chi$ be the quadratic character of $\mathbb F_p$, with $\chi(0)=0$. Fix a coordinate set $A\subseteq\mathbb F_p$ of size $2\le a\le d+1$. For each shift $b$ write
$$
 W_A(b)=\sum_{u\in A}\chi(b+u),\qquad z_b=\mathbf 1_{-b\in A}.
$$
The multiplicity at $b$ of an explicit polynomial built from the Reed–Solomon interpolation weights of $A$ is exactly $\lfloor W_A(b)^2/4\rfloor$. A matrix rank gives the exact minority-sign count at the same shift. These identities retain the prescribed coordinates. The exponent in the polynomial construction uses the quadratic character through Euler's criterion.

## Construction and factorization

Write $x=\lfloor a/2\rfloor$, $h=x-1$, and $D=d+a-2$. The leading-coefficient functional in Lagrange interpolation at $A$ has weights
$$
 c_u=\left(\prod_{v\in A\setminus\{u\}}(u-v)\right)^{-1} .
$$
Thus $\sum_u c_u u^k$ vanishes for $0\le k<a-1$ and equals one at $k=a-1$. Form
$$
 F(X)=\sum_u c_u(X+u)^D,\qquad J_{ij}(X)=\frac{F^{(i+j)}(X)}{[D]_{i+j}},\qquad
 P_A(X)=\det (J_{ij}(X))_{0\le i,j<x},
$$
where $[D]_j=D(D-1)\cdots(D-j+1)$ and $[D]_0=1$. Every denominator is a unit because $2h\le D<p$.

**Theorem.** In $\mathbb F_p[X]$,
$$
 P_A(X)=\operatorname{lc}(P_A)\prod_{b\in\mathbb F_p}(X-b)^{\lfloor W_A(b)^2/4\rfloor},
 \qquad \deg P_A=x(d-x).
$$

**Degree.** The first surviving coefficient in $F$ is $\binom D{a-1}$ at degree $t=D-(a-1)=d-1$. The coefficient in $P_A$ at the maximal possible degree $x(t-h)$ is the leading coefficient of $F$ to the power $x$, times $\det([t]_{i+j}/[D]_{i+j})$. This determinant is nonzero by the polynomial-basis calculation for normalized derivatives. Explicitly, take $m=D-t=a-1$ in that calculation. Its needed inequalities $h\le m$, $2h\le t$ and $D<p$ follow from $a\le d+1$ and $2h\le a-2$. Hence the maximal degree occurs. [Leading-coefficient proof](paley-defective-rectangle.md#a-determinant-with-certified-leading-coefficient)

**Local contact.** At a fixed $b$, choose $\sigma\in\{1,-1\}$ to be a most frequent nonzero sign and let $E=\{u:\chi(b+u)=-\sigma\}$. Its size is $e=(a-z_b-|W_A(b)|)/2$. Put $G_b=2\sum_{u\in E} c_u(X+u)^D$ and $\nu=a-1-z_b$. For $0\le j<\nu$, the normalized $j$th derivative of $F-G_b$ at $b$ equals
$$
 \sigma\sum_{u\in A}c_u(b+u)^{a-2-j}=0.
$$
At a nonzero $b+u$, this follows by multiplying the sign of the coefficient in $F-G_b$ by $(b+u)^d=\chi(b+u)$. If $-b\in A$, the exponent $a-2-j$ is positive. In both cases the last sum vanishes by interpolation. As all relevant $j!$ are units, $(X-b)^\nu$ divides $F-G_b$. Lean proves this contact directly from the actual sign filter and Lagrange weights. [Polynomial contact theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleyInterpolationContact.lean)

**Multiplicity.** The normalized derivative matrix of a single shifted power has rank at most one over $\mathbb F_p(X)$. The matrix of $G_b$ therefore has rank at most $e$. Entries of the remaining matrix are divisible by $(X-b)^{\nu-i-j}$, where $\nu\ge2h$. Expanding by complementary minors gives order at least $r(\nu-2h+r-1)$ for $r=x-e\ge0$. Indeed, a nonzero summand must use at least $r$ rows of the remaining matrix. A size-$k$ minor uses distinct row and column indices, giving order at least $k(\nu-2h+k-1)$, which increases weakly for $k\ge0$. The four parity cases give the following values. [Lean proof of the weighted divisibility lemma](../../../ArkLib/Research/ProximityGap/Frontier/PaleyDefectMinor.lean)

| $a$ | $z_b$ | $\lvert W_A(b)\rvert$ | Lower bound on the order |
|---|---:|---:|---:|
| even | 0 | $2r$ | $r^2$ |
| even | 1 | $2r-1$ | $r(r-1)$ |
| odd | 0 | $2r+1$ | $r(r+1)$ |
| odd | 1 | $2r$ | $r^2$ |

Each lower bound is $\lfloor W_A(b)^2/4\rfloor$. To see that every one is attained, sum over $b$. The character translates have inner product $p-1$ for equal sites and $-1$ otherwise. For distinct $u,v$ the change of variable $(b+u)/(b+v)$ bijects $\mathbb F_p\setminus\{-v\}$ with $\mathbb F_p\setminus\{1\}$, and $\chi((b+u)(b+v))$ equals the character of the ratio off the pole. Thus $\sum_b W_A(b)^2=a(p-a)$. Exactly $a$ shifts have odd $W_A(b)$ when $a$ is even, and exactly $p-a$ do when $a$ is odd. Subtracting the odd count and dividing by four gives $x(d-x)$ in either case. This accounts for the entire degree and proves the factorization.

## The exact rank at one shift

Take $y=\lfloor(a-z_b)/2\rfloor$. The $y\times y$ northwest submatrix of $J(b)$ has rank exactly $e$, including rank zero for an empty submatrix. To see this for $y>0$, its derivative orders satisfy $i+j\le2y-2<\nu$. It equals
$$
 V\operatorname{diag}\big(2c_u(b+u)^D\big)_{u\in E}V^{\mathsf T},\qquad
 V_{iu}=(b+u)^{-i}.
$$
The $e$ nodes are distinct nonzero field elements and $e\le y$. The first $e$ rows give an invertible Vandermonde matrix. Thus $V^{\mathsf T}$ is surjective, the middle map is invertible, and $V$ is injective. In particular $|W_A(b)|=a-z_b-2\operatorname{rank}J_{<y,<y}(b)$. The rank and the multiplicity both recover the magnitude. The exact rank identity has a Lean proof. [Rank theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleyShiftRank.lean)

## Two determinants recover the sign

Set $y=\lceil a/2\rceil$ and $D_1=d+a-1$. For $\sigma\in\{1,-1\}$ let $P_\sigma$ be the size-$y$ normalized derivative determinant of $\sum_u c_u(X+u)^{D_1}-\sigma$, with normalizers $[D_1]_{i+j}$. Then
$$
 \operatorname{ord}_b P_\sigma=\left\lfloor\frac{(W_A(b)+\sigma)^2}{4}\right\rfloor,
 \qquad W_A(b)=\operatorname{ord}_bP_+-\operatorname{ord}_bP_- .
$$
Consequently the signed discrepancy of a prescribed rectangle is the difference between the total root orders of two explicit interpolation polynomials on its second set. The following calculation gives a polynomial identity before any evaluation at $b$.

Write $t_u=X+u$, $g_u=t_u^d$, $H=X^p-X$ and $\eta=a\bmod 2$. In $\mathbb F_p[X]$,
$$
 P_\sigma\prod_{u\in A}(g_u+\sigma)\left(\prod_{u\in A}t_u\right)^\eta
   =(-1)^{xy+\binom x2+\binom y2} H^y P_A. \tag{*}
$$
To prove this, let $\Delta_I$ be the Vandermonde product on a subset $I$ in any order, and set $w_I=\Delta_I^2\prod_{u\in I}c_u$. The Lagrange moments give $\sum_u c_u t_u^{a-1-i-j}=1$ at $i=j=0$ and zero at all other derivative positions. This holds even at the largest index since $2y-2\le a-1$. Hence the entries of the signed determinant are $\sum_u c_u(g_u-\sigma)t_u^{a-1-i-j}$. Write the two sides of its matrix product using the powers $t_u^{y-1-i}$ and $t_u^{y-1-j}$. Expansion by Cauchy–Binet gives
$$
 P_\sigma=\sum_{|I|=y}w_I\prod_{u\in I}(g_u-\sigma)t_u^{1-\eta}.
$$
The same expansion for $P_A$ gives $\sum_{|J|=x} w_J\prod_{u\in J}(g_u+\sigma)t_u^\eta$. Here adding $\sigma$ to each $g_u$ leaves the matrix entries fixed because the extra terms are Lagrange moments of degrees from zero to $a-2$.

For complementary $I,J$, cancellation of the internal Vandermonde factors gives
$$
 w_I=\frac{(-1)^{\binom y2}}{\prod_{u\in I,v\in J}(u-v)}
     =(-1)^{xy+\binom x2+\binom y2}w_J .
$$
Multiply each summand in $P_\sigma$ by the two products on the left of (*). Each $u\in I$ contributes $t_u(g_u-\sigma)(g_u+\sigma)=t_u^p-t_u=H$. The remaining factors are precisely the summand for $J$ in $P_A$. This proves (*). In particular,
$$
 \frac{P_+}{P_-}=\prod_{u\in A}\frac{(X+u)^d-1}{(X+u)^d+1}
 \quad\text{in }\mathbb F_p(X).
$$
At $b$ the factor $H$ has a simple zero. The product of $g_u+\sigma$ has order $(a-z_b-\sigma W_A(b))/2$ because each nonzero solution of $t^d=-\sigma$ is simple. The product of the $t_u$ has order $z_b$. Inserting the central multiplicity into (*) gives the two signed root orders above, including at the poles. The full polynomial identity (*) also passes direct coefficient-by-coefficient checks for each sign. [Verifier](../../../scripts/probes/probe_paley_shift_multiplicities.py)

Lean independently proves the signed factorization and the difference-of-orders identity by adjoining one formal sign to the local minority count. When that sign is in the minority, its constant term contributes one rank-one matrix supported at the northwest entry. Summing the resulting local lower bounds accounts for the whole degree of each signed determinant. [Signed factorization and discrepancy](../../../ArkLib/Research/ProximityGap/Frontier/PaleySignedFactorization.lean) · [Constant-term rank contribution](../../../ArkLib/Research/ProximityGap/Frontier/PaleyVirtualSign.lean)

## Which root estimate would settle arbitrary placements?

For an integer $2\le m\le(p+1)/2$, let $H_m$ be the maximum of $|\sum_{b\in B}W_A(b)|$ over $|A|=|B|=m$. For each such $A$, define $T_m(A)$ to be the sum of the $m$ largest numbers in
$$
 \left\{\sqrt{4\operatorname{ord}_b P_A+((m-z_b)\bmod 2)}:\ b\in\mathbb F_p\right\}
$$
with one entry per field element. Then
$$
 H_m\ \le\ \max_{|A|=m}T_m(A)\ \le\ \frac{2p-m}{p-m}H_m.
$$
The first inequality is the triangle inequality and the factorization. For the second, divide the $m$ selected shifts into positive and nonpositive values of $W_A$. For either part $U$ of size $j$, its uniformly random $m$-element superset has expected signed sum $(p-m)/(p-j)$ times $\sum_{b\in U}W_A(b)$, since the sum over the whole field is zero. Every such superset has sum of magnitude at most $H_m$. For the two parts the sizes sum to $m$, giving the factor $(2p-m)/(p-m)$ on adding their two bounds. Lean proves both directions of the criterion with the actual determinant root orders. [Root-weight criterion](../../../ArkLib/Research/ProximityGap/Frontier/PaleyAbsoluteSlice.lean)

For any larger $A,B$, independent uniform $m$-subsets sample each pair with probability $m^2/(|A||B|)$. Hence their relative discrepancy is at most $H_m/m^2$. Reflection of $B$ exchanges sums and differences. Consequently, for $m=\lfloor p^\epsilon\rfloor+1$ and fixed $0<\epsilon\le1/2$, a power saving in $\max_A T_m(A)/m^2$ is equivalent, up to absolute factors, to the quadratic Paley conjecture at that scale. The total root multiplicity has the exact value computed above. Bounding how much of its square root can concentrate on the largest $m$ shifts is the outstanding estimate. [Conjecture 2.12](https://arxiv.org/html/2309.09124v3#S2.SS4) · [Related single-set criterion](paley-single-size-test.md)

## Reproduction

Run `python3 -O scripts/probes/probe_paley_shift_multiplicities.py`. The program computes the determinant by polynomial arithmetic modulo $p$ and independently computes the proposed product from Euler's criterion. It also compares the minority counts with Gaussian elimination at every shift. The fixtures cover 1,765 central factorizations, 3,530 signed factorizations and 21,889 shifts at primes from 5 through 97. Lean verifies the complete factorization and the exact root order at every field element for all admissible sets, including the degree-zero case. [End-to-end Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/PaleyShiftFactorization.lean) [Exact verifier](../../../scripts/probes/probe_paley_shift_multiplicities.py)
