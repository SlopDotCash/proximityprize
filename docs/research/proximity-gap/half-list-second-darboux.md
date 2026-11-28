# Second-prime half-rate list safety at 701/1000 agreement

At length $n=2^{30}$ and half rate, every received word on the second named prime has at most **2,147,483,648** codewords through **321,048,805 errors**. Thus its first failure is at least **321,048,806**. The proof applies to any injective grid of this length and any positive interleaving width. It leaves the exact named cutoff open. [Exact interpolation and cofactor checks](../../../scripts/probes/probe_half_second_darboux.py)

Let $d=n/2-1$, $t=\lceil701n/1000\rceil$, $s=701/1000$, and scalarize into the algebraically closed coefficient field $k$. A primary of order sixteen and derivative degree at most four, with weight cutoff $P=16t$, has surplus **193,275,615** and total degree at most 22. Put $L=n/64$ and take the squarefree product of all factors with at least $L$ assigned words. There are at most $4L+22$ other words. The adaptive interpolation treats derivative degrees three and four throughout their weight ranges. For derivative degree two it treats weights at least $\lfloor15d/2\rfloor$. All seven rows use average order 10000 and 80 equal variance intervals. The accompanying certificate gives the derivative caps, slopes and pointwise curvature bounds and checks the mixed Bézout estimate on each row. [Adaptive product proof](joint-list-contact-boards.md#products-of-derivative-degree-two-or-three)

At lower quadratic weights, let $a$ be the ordinate degree of the coefficient of the square of the derivative variable. Its leading coefficient and its order $j$ at a site give $o\le a+j+\min(j,2)\le a+2j$. Hence $\mathbb E o\le a+2[D-2(d-1)-ad]/n$ at weight $D$. This increases with $a$ since $2d<n$. On each successive interval of weights with fixed maximum possible $a$ from zero through five, a uniform order-6000 quotient gives a strictly larger lower bound on $\mathbb E o$. The source comparison uses one derivative cap on both ends of each integer interval. These comparisons exclude all large products of derivative degree at least two. [Leading coefficient and low-weight argument](quarter-list-second-quartic-darboux.md)

An oversized list would therefore give $M=2n-4L-22=2080374762$ sections on one linear equation $A+B V=0$. Retain exactly $M$. For total degree at most two the normalized curve bound gives at most $2+2d$ isolated solutions or at most $(n-d)/(t-d)$ in the family case, leaving room for the other words. [Isolated solutions and families](first-order-normalized-curve.md)

In the remaining weights put $b d-1\le D\le(b+1)d-2$, with $3\le b\le22$. Then $\deg_Y A\le b$, $\deg_Y B\le b-1$, and the plane intersection bound is $nK=(b-1)D+b(D-d+1)-b(b-1)d$. This bound also holds at the leftmost weight where the degree cap on $A$ can be one smaller, by first increasing the denominator degree to $b-1$ and then the numerator degree to $b$. For $j\ge2$ one has $(o^2-o-1)_+\ge2jo-j(j+1)-1$. At order one the negative right side also pays for both possible exceptional slopes. Use the incidence-class proof with mean order floor $Z$ to bound the number of exceptional classes by $n[K+j(j+1)+1-2jZ]$. Divide each weight interval into sixteen subintervals, using order 20000 and one common cap and $j$ at both ends. The checker excludes every $b\ge7$ and gives the following valid bounds $Jn$ for $b=3,4,5,6$, respectively.
$$
                   J=9/10,\quad 1,\quad63/100,\quad15/100 .
$$
[Exceptional slopes and nonreceived collisions](quarter-list-darboux-cofactors.md#exceptional-collision-classes)

Use $r=b-1$ anchors on each remaining interval. The common coefficient of $Y^{b-1}$ in the cofactors is that of $Y^b$ in $A$, so evaluation at $r$ distinct anchors detects their differences. The shared received-indicator rows and the exceptional logarithmic-residue rows give
$$
 \dim\langle H_i\rangle\le r+1+n\!\left[1-(1-\mu)^r+\frac{r(r-1)}{2M}
       +r\sqrt{J\big(d/n-s^2+(1+J)/M\big)}\right],
 \qquad \mu\le\sqrt{d/n+1/M}.
$$
Here $r(r-1)/(2M)$ allows for sampling distinct anchors. For each of the four values of $b$ the resulting nullity $k_0$ gives $m\le(M-1)/(k_0-1)<3$ for the degree of the rational first integral. It has at least $l\ge k_0+1$ completely split constant fibers. The descent from logarithmic forms uses $6dM^2<p$, which holds on the named prime. [Cofactor rank](quarter-list-darboux-cofactors.md#rank-of-the-polynomial-cofactors) · [Differential descent and complete fibers](quarter-list-darboux-cofactors.md#from-cofactor-relations-to-completely-split-fibers)

If the first integral has degree one, or its branch values are stationary, the rational vector field is regular on the ordinate projective line. It is Riccati, and the constant cross-ratios exclude $M$ words at this many agreements by $Mt>n+M(M-1)d/(M-2)$. The first integral of degree two admits a direct bound in the remaining case. Its two branch labels $\beta,\gamma$ are distinct and belong to an extension $E/k(X)$ of degree at most two. Choose a constant target chart in which both are generically finite and a completely split finite target $c_0$ distinct from both labels. Put $H=\max(h_E(\beta),h_E(\gamma))>0$ and choose $\beta$ of height $H$. It is separable as a function on the smooth projective curve of $E$. Indeed the binary fiber discriminant bounds its height on its degree-at-most-two defining field by $2dM$, below $p$, and $E$ is separable over that field.

For any other completely split finite target $c$ away from the branch labels, both nonzero fiber discriminants are squares. Their ratio in $E$ is
$$
       \frac{(c-\beta)(c-\gamma)}{(c_0-\beta)(c_0-\gamma)}\in E^{\times2}.
$$
At a place with $\beta=c$, all factors except $c-\beta$ are units unless the place lies in the pole sets of $\beta,\gamma$, in their coincidence set, or above $\beta=c_0$ or $\gamma=c_0$. These sets together contain at most $6H$ places. Thus every unramified preimage of such a $c$ under $\beta$ belongs to this exceptional set.

For the genus bound, the binary form of the two branch values has coefficient height at most $2H/[E:k(X)]$ by multiplying their projective linear factors. Its discriminant, of degree two in the coefficients, has at most $4H/[E:k(X)]$ zeros on the base, including infinity. The quadratic splitting field is unramified away from those zeros and is tame. Riemann–Hurwitz gives $2g(E)-2\le4H$. Excluding the chart's point at infinity, $c_0$, and at most two stationary branch labels, at least $l-4$ of the original targets satisfy the square-class test. Counting their preimages under $\beta$ gives
$$
    (l-4)H\le2(2g(E)-2+2H)+6H\le18H.
$$
Indeed each ramified point of index $e\ge2$ accounts for at most $2(e-1)$ in its fiber degree, and at most $6H$ unramified places occur overall. Consequently $l\le22$, contradicting the certified nullity. This proves the asserted half-rate budget bound using quadratic discriminants and Riemann–Hurwitz.

```sh
python3 scripts/probes/probe_half_second_darboux.py
```
