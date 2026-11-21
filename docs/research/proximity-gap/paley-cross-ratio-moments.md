# Every second set after a typical inversion of a prescribed domain

Let $p$ be an odd prime, $\chi$ the quadratic character extended by zero, and $A\subseteq\mathbb F_p$ any prescribed nonempty set of size $m$. Send $a$ to $(a-t)^{-1}$ and let $A_t$ be the finite image, omitting the pole $t$ if it belongs to $A$. Write $S(X,B)=\sum_{x\in X,z\in B}\chi(x-z)$. Given an integer $r\ge1$, a minimum partner size $1\le b_0\le p$, and $h>0$, the fraction of poles with **any** $B\subseteq\mathbb F_p$ satisfying $|B|\ge b_0$ and $|S(A_t,B)|\ge h m|B|$ is at most
$$
 h^{-2r}\left((2r-1)!!\frac{p}{m^r b_0}+\frac{(2r-1)^2}{b_0}\right).
$$
Here $(2r-1)!!$ counts the pairings of $2r$ positions. The bound allows the partner to be selected after the pole. Earlier [projective moment estimates](paley-support-ranks.md) prescribe both marked sets before changing coordinates.

For $m,b_0\ge p^\epsilon$, choose $r$ with $(r+1)\epsilon>1$. For every $0<\delta<\min\{(r+1)\epsilon-1,\epsilon\}/(2r)$, the exceptional fraction for $h=p^{-\delta}$ tends to zero by a power of $p$. If an evaluation domain must retain all $m$ coordinates, exclude the poles in $A$ at an additional cost of $m/p$. For a pole in $A$, $|A_t|=m-1$ and the displayed finite bound uses the original $m$ in its normalization.

## Gram expansion and exceptional coordinates

Set $K(t,y)=\sum_{a\in A}\chi(a-t)\chi(a-y)$. Expanding the even moment and summing independently over the two coordinates gives the exact identity
$$
 \sum_{t,y} K(t,y)^{2r}
  =\sum_{(a_1,\ldots,a_{2r})\in A^{2r}}
       \left(\sum_x\prod_{j=1}^{2r}\chi(a_j-x)\right)^2 .
$$
When every multiplicity in the tuple is even, the inner sum is $p$ minus the number of distinct sites. Such tuples number at most $(2r-1)!!\,m^r$ by pairing equal sites. Otherwise let $o\ge1$ count the distinct sites of odd multiplicity and $e$ those of positive even multiplicity. The character equals the character of the squarefree product over the $o$ odd sites, except that it vanishes at the $e$ omitted roots. The inner sum thus has absolute value at most $(o-1)\sqrt p+e\le (2r-1)\sqrt p$. It follows that the Gram moment is at most $(2r-1)!!\,m^r p^2+(2r-1)^2 m^{2r}p$. [Weil estimate, Theorem A.1](https://link.springer.com/article/10.1007/s40879-021-00521-5)

At $z=(y-t)^{-1}$ for $y\ne t$ the row $R_t(z)=\sum_{x\in A_t}\chi(x-z)$ equals $\chi(-1)\chi(y-t)K(t,y)$. At the remaining finite site $z=0$, $R_t(0)=\sum_{a\in A}\chi(a-t)$ and $|R_t(0)|\le K(t,t)=m-\mathbf1_{t\in A}$. Thus $\sum_z|R_t(z)|^{2r}\le\sum_y K(t,y)^{2r}$ for every pole. Hölder gives
$$
 \left(\frac{|S(A_t,B)|}{m|B|}\right)^{2r}
   \le \frac{\sum_z |R_t(z)|^{2r}}{m^{2r}|B|}.
$$
Averaging this common upper bound with $|B|$ replaced by $b_0$ proves the exceptional-fraction estimate.

One can retain infinity on either side using the projective matrix $C(x,z)=\chi(\det[v_x,v_z])$, with $v_x=(x,1)^t$ and $v_\infty=(1,0)^t$. Restoring a source at infinity adds at most $|B|$ in absolute value, and the target at infinity adds at most $m$. The finite row contribution is at most $|B|^{1-1/(2r)}(\sum_z|R_t(z)|^{2r})^{1/(2r)}$ even if dropping infinity leaves fewer than $b_0$ targets. Outside the same exceptional set of poles defined by the row norm, the relative projective discrepancy is therefore less than $h+1/m+1/b_0$ simultaneously for all $|B|\ge b_0$.

To recover the original chart for $t\notin A\cup B$, the transformed sum needs weights $\chi(a-t)$ and $\chi(b-t)$ at its two vertices, and the global factor $\chi(-1)$. Hölder allows arbitrary unit target weights. The source weight here depends on the very pole being averaged. Inserting it into $K(t,y)$ cancels $\chi(a-t)$ and restores the original row. Consequently this estimate alone gives no worst-pole conclusion.

Lean proves the fourth-order result over every finite field of odd order $q$ without invoking an external character-sum axiom. If $N$ poles have a partner of size at least $b_0$ with mean row magnitude at least $T$ in the sense $|S|/|B|\ge T$, then
$$
N b_0 T^4 \le 3m^2q^2+C m^4 q,
\qquad C=64\ \text{for }q\ge3251,\quad C=196\ \text{otherwise}.
$$
This bounds the exceptional fraction by $h^{-4}(3q/(m^2 b_0)+C/b_0)$ at $T=hm$. At $m,b_0\ge q^{1/3+\gamma}$ it gives a power saving for every $0<4\delta<\min(3\gamma,1/3+\gamma)$ with $h=q^{-\delta}$. In a quadratic extension the subfield example has exactly $1/\sqrt q$ of all poles exceptional at fixed relative threshold and sizes $\sqrt q$. [Formal Gram moment, chart identity and exceptional count](../../../ArkLib/Research/ProximityGap/Frontier/PaleyGramFourthMoment.lean) · [Exact subfield obstruction](paley-square-field-charts.md)

## The quartic sum in a prescribed chart

For ordered, distinct branch points $a,b,c,d\in A$, put $Q=\sum_x\chi((x-a)(x-b)(x-c)(x-d))$. Set
$$
 u=\frac{b-c}{b-a},\qquad \lambda=u\frac{d-a}{d-c},\qquad
 L(\lambda)=\sum_z\chi(z(z-1)(z-\lambda)).
$$
The substitution $z=u(x-a)/(x-c)$ sends $a,b,c,d$ to $0,1,\infty,\lambda$. The ratio of $z(z-1)(z-\lambda)(x-c)^4$ to the quartic is $u(u-1)(u-\lambda)$ with character $w=\chi((b-a)(d-c))$. The missing affine value $z=u$ contributes $w$ to the cubic sum. Thus $Q+1=wL(\lambda)$, including the constant from infinity.

Let $V(\lambda)$ sum $w$ over the ordered distinct tuples from $A$ of cross-ratio $\lambda$, and let $N(\lambda)$ count those tuples. For $m\ge4$ the mean quartic sum is $-1+\langle V,L\rangle/(m)_4$, where $(m)_4=m(m-1)(m-2)(m-3)$. On $\lambda\ne0,1$ the trace vector has sum $1+\chi(-1)$ and squared norm $p^2-2p-3$. Indeed write $L(\lambda)=\sum_z\chi(z(z-1))\chi(z-\lambda)$, apply quadratic shift orthogonality, then remove $L(0)=-\chi(-1)$ and $L(1)=-1$. Subtract the mean $\bar V$ of $V$ on this range. A sufficient condition for the [genus-one fourth-moment criterion](paley-domain-tails.md) at $m\ge p^{1/3+\gamma}$ is
$$
 \sum_{\lambda\ne0,1}|V(\lambda)-\bar V|^2
   \ll \frac{m^{10}}{p^{2+2\eta}}
$$
for some fixed $\eta>0$. Cauchy–Schwarz bounds the centered pairing by $O(m^5p^{-\eta})$, while $|\bar V\sum L|\le 2(m)_4/(p-2)$. The two-sided square estimate suffices for the one-sided trace problem.

There is an exact signed incidence interpretation. For a projectivity $g(x)=(ux+v)/(sx+t)$ write $U=A\cap g^{-1}A$, $k=|U|$ and $z=\sum_{x\in U}\chi(sx+t)$. Because three ordered distinct points fix $g$, each pair of ordered tuples of equal cross-ratio determines exactly one $g$. On its four sites the product of their weights is $\prod_{i=1}^4\chi(sx_i+t)$ by the difference formula for $g$. Expanding the ordered distinct sum on $U$ gives
$$
 \sum_{\lambda}V(\lambda)^2
 =\sum_{g\in\mathrm{PGL}_2(\mathbb F_p)}
       \big[z^4-(6k-8)z^2+3k^2-6k\big].
$$
Replacing all the signs by one gives the ordinary collision count $\sum N(\lambda)^2=\sum_g(k)_4$. It is always at least $(m)_4^2/(p-2)$ by Cauchy–Schwarz. Consequently a bound on this raw unsigned energy cannot reach the sufficient threshold for $m\le\sqrt p$, even if the cross-ratios are evenly distributed. Warren and Wheeler's incidence bounds control intersection counts $k$, and Murphy et al. give lower bounds on the number of distinct cross-ratios. Neither estimate supplies the signed correlation with $L$. The prescribed-chart estimate for arbitrary $A$ remains open. [Warren–Wheeler, Theorems 2–3](https://arxiv.org/pdf/2107.12286) · [Murphy et al., Lemma 19](https://arxiv.org/pdf/1702.01003)

The [finite probe](../../../scripts/probes/probe_paley_cross_ratio.py) checks the two ways of computing the Gram moment, the pole and infinity corrections, the signed quartic formula, and the projective energy identity.
