# A constant list bound beyond Johnson at half rate

Let $n$ be any positive integer. On any $n$ distinct points in a field of characteristic zero or characteristic $p>425$, every received word agrees on at least $181n/256$ sites with at most **19,999** polynomials of degree at most $n/2$. The same bound holds at every positive interleaving width. Thus a length-independent list bound holds through relative error $75/256$. The agreement fraction is strictly below the asymptotic half-rate Johnson agreement, since $(181/256)^2=1/2-7/65536$. [Exact certificate](../../../scripts/probes/probe_half_list_uniform_length.py)

The proof uses the first-order hidden-derivative interpolation method, including its finite local-rank formula. Dao, Kominers and Thaler and Gabizon establish linear-in-length upper bounds beyond Johnson on prescribed grids. The argument here uses a second interpolation modulo each candidate differential factor and bounds its local orders via the coefficients of a linear equation. [Dao–Kominers–Thaler](https://eprint.iacr.org/2026/2056) · [Gabizon](https://eprint.iacr.org/2026/2048) · [Finite coefficient and content inequalities](half-list-coefficient-derivatives.md)

## A source bound uniform in the length

Write $s=181/256$ and assign $X,Y,V$ the normalized weights $1/n,1/2,1/2$. Substituting $(X,f,f')$ into a monomial of weight $w$ gives a polynomial of degree at most $nw$. For a strict weight cutoff $w$ and a derivative-degree cap $h$, write
$$
 \mathcal N_n(w,h)=
 \sum_{k=0}^h\sum_{j\ge0}\left\lceil n(w-(j+k)/2)_+\right\rceil,\qquad
 S(w,h)=\sum_{k=0}^h\sum_{j\ge0}(w-(j+k)/2)_+ .
$$
The first expression counts monomials, so $\mathcal N_n(w,h)\ge nS(w,h)$. There is also a uniform bound for the difference which occurs after quotienting. Suppose $g$ has normalized weight $D$ and derivative degree $v\le h$. Then
$$
 \mathcal N_n(w,h)-\mathcal N_n(w-D,h-v)
 \ \ge\ n\big(S(w,h)-S(w-D,h-v)\big).                           \tag{1}
$$
Choose a monomial $X^IY^JV^K$ of $g$ of weight $D$. Every positive summand $(j,k)$ of the smaller source maps injectively to $(j+J,k+K)$ of the larger one, since $K\le v$. The two positive unrounded lengths differ by the integer $I$, so their ceiling-rounding gains are equal. Every unpaired gain is nonnegative. This proves (1) for odd and even lengths and for all real cutoffs.

For interleaving width $m$, scalarize a column using the injective map $(a_0,\ldots,a_{m-1})\mapsto\sum_{i=0}^{m-1}a_i T^i$ into the rational function field in an indeterminate $T$. The polynomial degree in $X$ and the physical agreement sets are preserved. Extend this coefficient field to its algebraic closure.

## Capturing a large group

At a site $(x,y)$ substitute $(X,Y,V)=(x+u,y+uz,z+uz_1)$ with $z,z_1$ independent, and let $o(F)$ be the order in $u$. This order is additive on products. A polynomial word hitting the site gives $z=(f(x+u)-y)/u$ and $z_1=z'$. The dimension of the local image modulo $u^r$ at derivative cap $h$ is
$$
 C(r,h)=(h+1)r(r+1)/2-
         \sum_{\ell=0}^{r-1}(2\ell+1-r)_+(\ell+h+1-r)_+ .
$$
For each binomial block in the expansion the consecutive powers of $V$ are at most $h$. Its Vandermonde minors have full rank when $p>h$. This is the only characteristic restriction on the local-rank calculation. [Block derivation](sixteenth-list-quotient-jets.md#the-local-quotient)

Use primary order eleven and derivative cap two. At $P=11s$ the normalized surplus $S(P,2)-C(11,2)$ equals **123/256**. A nonzero primary polynomial thus vanishes after substitution on every list word, by the number of roots with multiplicity. Its total jet degree is at most $b_0=\lfloor2P\rfloor=15$. Assign every word to one irreducible primary factor containing its jet. Factors independent of $V$ cover at most $b_0$ words. There are at most two positive-derivative factors.

It suffices to bound every finite candidate list. Consider a group of at least $L=9992$ words on a positive-derivative factor $g$ of weight $D$ and derivative degree $v$. Where required, remove at most $b_0^2$ exceptional generic jets. On each retained word assign agreement weights in $[0,1]$ supported at true hits, with total exactly $sn$. This can be done by using ones and at most one fractional weight. Write $p_x$ for their average at site $x$ and $\mathbb E$ for the uniform average over sites. Distinct words share at most $n/2$ sites, even after scalarization. The self inner product of any weight vector is at most $sn$. Consequently
$$
 \mathbb E p=s,\qquad
 \mathbb E(p-s)^2\le\sigma^2=
           \tfrac12-s^2+(s-\tfrac12)/(L-b_0^2).
$$
All weighted order bounds hold with these fractional selections, since the true vanishing orders are counted with nonnegative weights at most one.

The secondary interpolation uses order $r=425$. Given a cap $h\ge v$, the local quotient imposes at most $C(r,h)-C(r-o_x,h-v)$ conditions at each site, where $o_x=o_x(g)$. Global multiples of the irreducible factor occupy $\mathcal N_n(rs-D,h-v)$ source dimensions. The local rank increments are nondecreasing because multiplication by $u$ injects one order-graded piece into the next. Thus (1) and the strict inequality
$$
 S(rs,h)-S(rs-D,h-v)>
 C(r,h)-C(r,h-v)
 +[C(r,h-v)-C(r-1,h-v)]\,\mathbb E o                           \tag{2}
$$
produce a secondary equation coprime to $g$ over $k(X)$. Its evaluation vanishes identically on the whole group by multiplicity at its actual hits. The two generic jet curves can contain at most $b_0\lfloor2rs\rfloor=9000$ distinct common points by affine Bézout, fewer than $L$. Singular jets deleted for the mean estimate are included in this last count.

## Mean-order inequalities

At every site $0\le o\le 2D+v$ by the leading binomial-block bound for a primitive factor. Removing its intersections with $g_V$ costs at most $b_0^2$ jets, as $p>v$ and $g_V$ is relatively prime to $g$. Evaluation gives $\mathbb E[p o]\le s+D-1/2$. Cauchy–Schwarz and the bound on the range of $o$ give the ordinary estimate
$$
       \mathbb E o\le 1+(D-\tfrac12)/s+(2D+v)\sigma/(2s) .
$$

For $v=1$ write $g=A+BV$ and put $a=\deg_Y B$, $b=\lfloor2D\rfloor$, $K=b+1$ and $e=D-1/2$. For $A\ne0$, the coefficient intersection estimate is
$$
           \mathbb E\max(0,o^2-o-1)\le aD+be-ab/2 .
$$
The proof for integer weights uses only degree bounds on the coefficients in the Sylvester determinant. Under the present weights the $X$-degree of the $Y^j$ coefficient of $A$ is at most $n(D-j/2)$, and for $B$ it is at most $n(e-j/2)$. These give the displayed normalization. [Local intersection and summed degree bound](linear-contact-quotient.md)

The coefficient and content estimates carry over with the same normalization. Explicitly, set $\phi_j(o)=\max(o-1-j,{\bf1}_{o\ge j+1})$. For $o\le a$ put $H=0$, $Q_j=\phi_j(o)$. For $o>a$ put $H=\max(1,o-a-1)$ and $Q_j=(o-j-1-H)_+$. For $0\le j<a$ and for the top coefficient respectively,
$$
 \mathbb E(H+sQ_j)\le e-j/2+\tfrac{\sigma}{2}\max_{0\le u\le K}Q_j(u),
 \qquad \mathbb E(H+Q_a)\le e-a/2 .
$$
The additional content bound is
$$
 \big(s+(1-s)/2\big)\mathbb E o
 \le s+e+(1-s)a/2+\sigma K .
$$
These follow by extracting the common $X$-factor of $B$ and evaluating $\partial_Y^j B$ on the selected words. The nonzero derivatives require only $p>a$, since $a\le15$. Their exceptional words number at most $\sum_{j=0}^a(a-j)\le b_0^2$. The arguments use no derivatives of order growing with the message degree. [Coefficient proofs](half-list-coefficient-derivatives.md#vertical-derivatives-and-the-common-factor-of-the-coefficients-in-x)

When $A=0$, irreducibility gives $g$ proportional to $V$. In characteristic zero its solutions are constant. In characteristic $p$, differences of polynomial solutions have identically zero derivative, so each distinct root has multiplicity at least $p$. Distinct solutions have at most $n/(2p)$ common hits. A group of size $L$ would imply $s^2\le1/(2p)+(s-1/(2p))/L$, which the certificate excludes even at $p=426$. This covers the case of message degrees at least the characteristic.

## Finite comparisons

For $v=2$ on $1\le D\le P$ and $v=1$ on $5\le D\le P$, the ordinary mean estimate gives normalized surplus in (2) at least **1,855** and **10,453**, respectively. For $v=1$ on $1/2\le D\le5$, divide at the changes in $b$ and use each value $0\le a\le b-1$. The verifier forms nonnegative rational combinations of the bounds above, adding the exact maximum over integer $0\le o\le K$ of the difference between $o$ and the combined left side. This gives an affine upper bound on $\mathbb E o$. With one chosen cap and combination per interval the normalized surplus is concave in $D$, since $S(rs-D,h-v)$ is convex. Exact verification at both endpoints of **51** real intervals gives normalized surplus at least **7** throughout.

No group has at least $L$ assigned words. Including the factors independent of $V$ gives the stated bound $2L+b_0=19999$. This is a written proof with an exact rational certificate.
