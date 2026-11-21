# A constant saving for prescribed quadratic rectangles at the square-root scale

Let $p$ tend to infinity through odd primes, let $\chi$ be its quadratic character with $\chi(0)=0$, and let $A,B\subseteq\mathbb F_p$ be arbitrary sets with $|A|,|B|=(1+o(1))\sqrt p$. At their **prescribed placement**,
$$
 \left|\sum_{u\in A,\,v\in B}\chi(u+v)\right|
 \le \left(\frac{\sqrt3}{2}+o(1)\right)|A||B|.
$$
The same bound for differences follows by replacing $B$ with $-B$. The proof gives an explicit inequality for finite parameters, including unequal sizes. At the square-root scale $\sqrt3/2$ is a fixed relative saving. The Paley conjecture asks for a relative factor $p^{-\delta}$ and extends to sets of size $p^\epsilon$ for every fixed $\epsilon>0$. [Paley graph conjecture, Conjecture 2.12](https://arxiv.org/html/2309.09124v3#S2.SS4)

Hanson and Petridis constructed a degree-$(p-1)/2$ auxiliary polynomial with high-multiplicity zeros at shifts giving perfect square agreement. We use that same polynomial. At a shift with some nonsquare symbols, its initial Taylor coefficients agree with those of a sum of as many powers of linear polynomials as there are nonsquares. A determinant of normalized derivatives converts this rank bound into vanishing with multiplicity. [Hanson and Petridis, proof of Theorem 1.2](https://arxiv.org/pdf/1905.09134)

## Finite bound

Write $a=|A|$, $b=|B|$, $d=(p-1)/2$, $S=\sum_{u,v}\chi(u+v)$ and $z=|\{(u,v)\in A\times B:u+v=0\}|$. Suppose $2\le a\le d+1$ and $b\ge1$. For every integer $x$ with $1\le x\le a/2$,
$$
 \boxed{\quad (|S|+z)^2
 \ \le\ b^2(a-2x)^2+4bx(d+1-x).\quad}                         \tag{1}
$$
The same statement holds with $A$ and $B$ exchanged whenever their sizes meet the corresponding hypotheses.

Write $e_v=|\{u\in A:\chi(u+v)=-1\}|$ and $(s)_+=\max(s,0)$. The stronger estimate underlying (1) is
$$
 \sum_{v\in B}(x-e_v)_+(a-x-e_v)_+\ \le\ x(d+1-x).             \tag{2}
$$
It controls the number of shifts with few errors directly. For example, for an integer $0\le j<x$, the number of $v\in B$ with $e_v\le j$ is at most $x(d+1-x)/((x-j)(a-x-j))$. Including a zero symbol as an error is unnecessary.

### The polynomial at a shift with errors

Set $m=a-1$ and $D=d+m\le p-1$. Solve the invertible Vandermonde system over $\mathbb F_p$ for weights $c_u$ such that $\sum_u c_u u^i=0$ for $0\le i<m$ and $\sum_u c_u u^m=1$. The binomial theorem gives $\sum_u c_u(X+u)^m=1$. Define
$$
 F(X)=\sum_{u\in A}c_u(X+u)^D-1 .
$$
The first $m$ leading coefficients cancel and that of $X^{D-m}$ is $\binom Dm\ne0$ in $\mathbb F_p$, since $m\le D<p$. Hence $\deg F=d$.

For each $v$, set $G_v(X)=2\sum_{\chi(u+v)=-1}c_u(X+u)^D$. We claim
$$
                        (X-v)^m\mid F-G_v.                      \tag{3}
$$
Let $[t]_j=t(t-1)\cdots(t-j+1)$ denote a falling factorial, with $[t]_0=1$. For $0\le j<m$ the $j$-th derivative of $F-G_v$ at $v$ equals
$$
 [D]_j\sum_{u\in A}c_u(v+u)^{m-j}-\mathbf 1_{j=0}.
$$
Indeed, when $v+u\ne0$, the coefficient of $c_u$ before differentiation has sign $+1$ or $-1$ according to $\chi(v+u)$. Multiplication by $(v+u)^d=\chi(v+u)$ cancels that sign. If $v+u=0$, both powers have positive exponents and vanish. The displayed derivative is zero for $j=0$ by the degree-$m$ identity. For $1\le j<m$, differentiate that identity and divide by $[m]_j\ne0$. Since $j!$ is nonzero for every $j<m<p$, the derivative equalities give (3).

### A determinant with certified leading coefficient

Let $h=x-1$ and set
$$
 M(P)_{ij}=\frac{P^{(i+j)}(X)}{[D]_{i+j}},\qquad
 W(X)=\det M(F),\qquad 0\le i,j\le h .
$$
All divisors are nonzero since $2h\le a-2=m-1$ and $D<p$. Moreover $2h\le d$, since $m\le d$. Each determinant term has degree at most $(h+1)(d-h)$, subtracting the sum of its row and column indices. If $L$ is the leading coefficient of $F$, its coefficient at that degree is $L^{h+1}$ times
$$
 \det\left(\frac{[d]_{i+j}}{[D]_{i+j}}\right)_{0\le i,j\le h}.
$$
This determinant is nonzero **in the prime field**. Factor the nonzero scalar $[d]_i/[D]_i$ from row $i$, then multiply that row by $[D-i]_h\ne0$. Its entries become evaluations, at $w_i=D-i$, of the polynomials
$$
 L_j(w)=[w-m]_j[w-j]_{h-j},\qquad 0\le j\le h.
$$
These are a basis of the polynomials of degree at most $h$. In a putative relation, evaluation at $w=m$ isolates $L_0(m)=[m]_h\ne0$. Now evaluate successively at $w=h-1,h-2,\ldots,0$. At $w=t$, $L_j(t)=0$ for $j\le t$; among the coefficients still to be determined this isolates $j=t+1$. Its first factor is a product of the nonzero integers $t-m,t-m-1,\ldots,-m$ modulo $p$, and its second factor is $[-1]_{h-t-1}\ne0$. This proves independence, also covering $h=0$ with the constant basis. The nodes $D,D-1,\ldots,D-h$ are distinct modulo $p$, so evaluation at these nodes is an isomorphism. This proves
$$
                             \deg W=(h+1)(d-h).                  \tag{4}
$$

### Root multiplicities and the number of errors

Over $\mathbb F_p(X)$, $M(G_v)$ has rank at most $e_v$. Each term $2c_u(X+u)^D$ contributes the outer product of the vector with entries $(X+u)^{-i}$ with itself, scaled by $2c_u(X+u)^D$. The matrix $E=M(F)-M(G_v)$, on the other hand, has polynomial entries divisible by $(X-v)^{m-i-j}$ by (3).

For a size-$r$ minor of $E$ with row and column sets $I,J$, every term vanishes at $v$ to order at least $rm-\sum_{i\in I}i-\sum_{j\in J}j$. The sum of the largest $r$ indices in $0,\ldots,h$ is $r(2h-r+1)/2$. Hence each such minor is divisible by
$$
                         (X-v)^{r(m-2h+r-1)} .
$$
Expand $\det(M(G_v)+E)$ in complementary minors. Every summand uses an $r$-minor of $E$ and an $(h+1-r)$-minor of $M(G_v)$ on the complementary rows and columns. The latter vanishes identically if $h+1-r>e_v$. The displayed exponent increases with $r$ since $m-2h\ge1$. When $e_v<x$, taking the smallest possible $r=x-e_v$ gives
$$
                       \operatorname{ord}_v W
                         \ \ge\ (x-e_v)(a-x-e_v).
$$
When $-v\notin A$, the derivative calculation also holds at $j=m$ and yields one more order in (3). The stated estimate uses the uniform order $m$ at every shift. For $e_v\ge x$ the summand on the left of (2) is zero. Distinct $v$ provide distinct root factors. Summing the required orders and applying (4) proves (2).

### Converting the error count to signed discrepancy

The function $\phi(s)=(x-s)_+(a-x-s)_+$ is convex for $s\ge0$. On $[0,x]$ its second derivative is 2, and the left derivative $2x-a\le0$ meets the constant zero continuation at $x$. By Jensen's inequality, $\phi(\bar e)\le x(d+1-x)/b$, where $\bar e=b^{-1}\sum_{v\in B}e_v$. If $\bar e<x$, completing the square yields
$$
             a-2\bar e\ \le\sqrt{(a-2x)^2+4x(d+1-x)/b}.
$$
If $\bar e\ge x$, this inequality follows from $a-2\bar e\le a-2x$. Since $S+z=b(a-2\bar e)$, this supplies the upper bound for $S+z$. Simultaneously multiplying $A$ and $B$ by any fixed nonsquare reverses $S$ and leaves $z$ unchanged, giving the upper bound for $-S+z$ as well. Squaring the larger of these two quantities proves (1).

## The range and the constant

Suppose $a,b\to\infty$, $a\le(p+1)/2$, and $d/(ab)\to\lambda$ for fixed $0<\lambda<1$. Take $x/a\to(1-\lambda)/2$ using the nearest admissible integer. Dividing (1) by $a^2b^2$ gives
$$
 \limsup\frac{|S|}{ab}\le\sqrt{2\lambda-\lambda^2}.
$$
For $a,b=(1+o(1))\sqrt p$, $\lambda=1/2$ and $x/a\to1/4$. Thus the constant is $\sqrt3/2=0.8660254\ldots$. Lean verifies this asymptotic assertion for every sequence of primes and prescribed sets satisfying the two size limits. [Asymptotic theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleyBalancedLimit.lean) Equivalently the proportion of each of the two nonzero signs is at least $(2-\sqrt3)/4-o(1)$ at this scale, by applying the error bound to the two signs. More generally the estimate gives a strict constant whenever $ab/p$ tends to a constant greater than $1/2$. For balanced sizes $p^\epsilon$ with fixed $\epsilon<1/2$, the condition $d/(ab)<1$ eventually fails. The proof gives no power saving at the boundary $ab\sim p$.

## The degree barrier for every puncturing

Suppose $ab\le d=(p-1)/2$. Take any nonempty $A'\subseteq A$, $B'\subseteq B$ of sizes $a',b'$ for which the construction applies, and write $h=x-1$. Even if all $a'b'$ entries have the same nonzero sign, the strongest local estimate above charges at most $(h+1)(a'-h)$ per shift. This uses the full order $a'$ available away from $-A'$. The determinant degree always pays that total, since
$$
 b'(h+1)(a'-h)
 = (h+1)(a'b'-b'h)
 \le (h+1)(d-h)
 = \deg W_{A',h}.
$$
Here $a'b'\le d$ and $b'\ge1$. The same calculation holds after exchanging the sides. Thus a hypothetical monochromatic rectangle satisfies every such degree inequality on its subrectangles, as well as any nonnegative weighted sum of them. To get a saving below this product threshold from multiple auxiliary polynomials would require joint information beyond their individual degree budgets.

### Linear combinations across puncturings of the same size

Fix $2\le k\le a$ and $D_k=d+k-1<p$. The span of the auxiliary polynomials for all $k$-subsets of $A$ consists of
$$
 F_w(X)=\sum_{u\in A}w_u(X+u)^{D_k}-\mu_{k-1},
 \qquad \mu_i=\sum_{u\in A}w_u u^i,\qquad
 \mu_0=\cdots=\mu_{k-2}=0.
$$
The Vandermonde equations leave $a-k+1$ free weights. Fixing $k-1$ nodes and adding each remaining node in turn gives that many independent barycentric vectors, since each has a nonzero coordinate where all the others vanish. For $w\ne0$, the first index $j$ with $\mu_j\ne0$ lies between $k-1$ and $a-1$. The leading term is $\binom{D_k}{j}\mu_j X^{D_k-j}$, of positive degree since $a\le d+1$. Thus the minimum degree is $d+k-a$, attained by the barycentric weights on all of $A$.

One can also account for every extra zero gained by choosing the weights. Suppose $\chi(v+u)=1$ on $A\times B$. Write
$$
 \sum_{u\in A}\frac{w_u}{X+u}=\frac{P_w(X)}{\prod_{u\in A}(X+u)}.
$$
Expansion at infinity gives $\deg P_w=a-1-j$. For each $v\in B$, the first $k$ Taylor coefficients of $F_w$ vanish by the displayed moment equations and the definition of its constant correction. The coefficient at order $k+\ell$ is $\binom{D_k}{k+\ell}\sum_u w_u(v+u)^{-1-\ell}$. Up to the nonzero factor $(-1)^\ell\binom{D_k}{k+\ell}$, this is the order-$\ell$ Taylor coefficient of the rational function at $v$. This calculation holds through $\ell=\deg P_w$, since $k+\deg P_w\le a\le D_k<p$. Therefore
$$
 \operatorname{ord}_v F_w=k+\operatorname{ord}_v P_w,\qquad
 \sum_{v\in B}\operatorname{ord}_v F_w\le bk+a-1-j.
$$
For $ab\le d$, the remaining degree is at least
$$
 (D_k-j)-(bk+a-1-j)=d-ab+(a-k)(b-1)\ge0.
$$
Thus even a linear combination chosen specifically for $B$ can accommodate every prescribed root and every extra order from its coefficients in this range.

### Exact local orders at shifts with few errors

Under the hypotheses of (2), write $e=e_v<x$, $r=h+1-e$, and $s=a-\mathbf 1_{-v\in A}$. The actual multiplicity is
$$
                   \operatorname{ord}_v W=r(s-2h+r-1).
$$
Indeed, put $E=F-G_v$. When $-v\notin A$, the coefficient of $(X-v)^a$ in $E$ is $\binom Da\sum_u c_u/(v+u)$. Partial fractions give $\sum_u c_u/(v+u)=(-1)^{a-1}/\prod_u(v+u)$. When $-v\in A$, the coefficient at order $a-1$ is $-\binom D{a-1}c_{-v}$, since $\sum_u c_u=0$. Both coefficients are nonzero. Together with (3) and its off-diagonal improvement this gives $E=L(X-v)^s+\cdots$ with $L\ne0$.

In the complementary-minor expansion the unique choice achieving the smallest possible order uses rows and columns $e,\ldots,h$ from $M(E)$. The complementary $e$-by-$e$ minor of $M(G_v)(v)$ is a squared Vandermonde determinant on the distinct inverses $(v+u)^{-1}$ at the bad points, times the product of the nonzero weights $2c_u(v+u)^D$. For $e=0$ this minor equals one. The first coefficient of the residual minor is
$$
 L^r\left(\frac{[s]_{2e}}{[D]_{2e}}\right)^r
 \det\left(\frac{[s-2e]_{i+j}}{[D-2e]_{i+j}}\right)_{0\le i,j<r}.
$$
The basis argument proving (4) applies with the new degree $s-2e$, denominator parameter $D-2e$ and index $h-e$. Indeed $s\ge2h$, $D-s\ge h-e$, and $D<p$. Thus this coefficient survives. Every larger residual minor has strictly greater order, and every other choice of $r$ rows or columns loses at least one from its index sum. This proves the equality.

## Verification

Lean verifies inequality (1) for every admissible prime and every prescribed pair of sets. It also verifies the concrete upper bound 56,719 on $|S|+z$ for all 256-by-256 rectangles at $p=65537$. The following independent exact checks exercise the bound in small fields. [Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleyPrescribedRectangle.lean) For each prime in the displayed program, the test considers every admissible coordinate set $A$, every positive size $b$, every admissible $x$ and both choices of sign. For fixed $A,b$ and sign, the maximum of $\pm S+z$ over all sets $B$ is the sum of the $b$ largest individual scores, so the comparisons cover every $B$ of that size. Running this Python 3 program checks 97,211 coordinate sets and 10,922,144 inequalities.

```python
from itertools import combinations

families = 0
checks = 0
for p in (5, 7, 11, 13, 17):
    d = (p - 1) // 2
    symbols = [(0 if u == 0 else 1 if pow(u, d, p) == 1 else -1)
               for u in range(p)]
    for a in range(2, d + 2):
        for A in combinations(range(p), a):
            families += 1
            signs = [sum(symbols[(u + v) % p] for u in A) for v in range(p)]
            zeros = [int((-v) % p in A) for v in range(p)]
            for sign in (-1, 1):
                values = sorted((sign * w + z for w, z in zip(signs, zeros)), reverse=True)
                total = 0
                for b, term in enumerate(values, 1):
                    total += term
                    for x in range(1, a // 2 + 1):
                        rhs = b*b*(a - 2*x)**2 + 4*b*x*(d + 1 - x)
                        assert total <= 0 or total**2 <= rhs
                        checks += 1
print(families, checks)
```

A separate direct polynomial calculation tested 735 choices of $(p,A,h)$ at primes from 7 through 47. It constructed $F$ from the Lagrange weights $c_u=1/\prod_{u'\ne u}(u-u')$, expanded the determinant by permutations modulo $p$, and translated the resulting coefficient vectors to every field element. In 22,119 shift tests it checked (3) and the precise degree in (4). An independent replay checked that the first nonzero coefficient of $F-G_v$ occurs at the exact predicted order at all 22,119 shifts. In all 2,882 cases with $e_v<x$, it also checked that the first nonzero coefficient of $W(v+T)$ occurs at $r(s-2h+r-1)$.
