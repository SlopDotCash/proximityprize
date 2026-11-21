# Four-site rank on two arithmetic progressions

Fix a family of odd primes. Let $P_{xy}=\chi(x-y)$ for the quadratic character modulo $p$, and let $D(X)$ count the unordered four-subsets of $X$ whose principal minors of $P$ are singular over $\mathbb F_3$. The following three assertions are equivalent. Each asks for a power saving $O_\epsilon(p^{-\delta})$, with some $\delta(\epsilon)>0$, for every fixed $0<\epsilon<1$ and every sufficiently large prime in the family.

1. Every translated interval of length $p^\epsilon\le H\le p$ has absolute character sum $O_\epsilon(Hp^{-\delta})$.
2. For every two length-$H$ arithmetic progressions $I,J$ with a common nonzero step, $H\ge p^\epsilon$, the complex operator norm of $(P_{xy})_{x\in I,y\in J}$ is $O_\epsilon(Hp^{-\delta})$. The starting points are independent. The same bound holds after applying any one projective transformation to both progressions.
3. For every $X$ that is the union of two such progressions,
   $|D(X)/\binom{|X|}4-1/4|=O_\epsilon(p^{-\delta})$.

**Unconditional range.** For each $\kappa>0$, assertions 2 and 3 hold whenever $H\ge p^{1/4+\kappa}$. In particular, on two progressions of this length one may choose the row and column subsets *and all their signs* after seeing the matrix. For arbitrary subsets of sizes $a,b$ the discrepancy is $O_\kappa(Hp^{-\delta}\sqrt{ab})$. The bound remains a relative power saving whenever $\sqrt{ab}\ge Hp^{-\delta/2}$. This extends to both subsets of the same projective image of the union, with an absolute factor of two. The analytic input is Heath-Brown and Pierce's uniform estimate with a **linear additive twist**. [Heath-Brown and Pierce, Theorem 1.4](https://arxiv.org/pdf/1404.1677)

## From short sums to restricted operator norms

If $I=s+d[0,H)$ and $J=t+d[0,H)$ in $\mathbb F_p$, divide the differences by $d$. The global factor $\chi(d)$ has absolute value one. The differences now lie in a cyclic interval $L$ of length $\min(p,2H-1)$, centered at $(s-t)/d$. Put $K(z)=\chi(z)\mathbf1_L(z)$. Convolution with $K$ has operator norm $\max_{k}|\sum_{z\in L}\chi(z)e^{-2\pi ikz/p}|$ by finite Fourier inversion and Parseval. Extending vectors by zero gives this upper bound for the restriction to $I\times J$. The kernel may be chosen arbitrarily outside the used differences. Under a common projectivity the matrix undergoes diagonal sign changes on its rows and columns, a common sign, and reindexing. These preserve singular values, including in the projective model with infinity. [Lean proof of the finite complex-weight bound](../../../ArkLib/Research/ProximityGap/Frontier/PaleyIntervalSpectrum.lean) · [Projective signs and the four-site formula](paley-four-site-rank.md)

For the unconditional assertion take $0<\kappa\le1/8$ by decreasing it if needed. Heath-Brown and Pierce's Theorem 1.4 bounds a mixed sum of length $h<p^{1/2+1/(4(r-1))}$ by $O_{r,\nu}(h^{1-1/r}p^{1/(4(r-1))+\nu})$ uniformly in its starting point and its real linear phase. The zero frequency is covered as well (the phase $n$ has exponential one at integers). Choose $r\ge2$ with $1/(4(r-1))\le\kappa/4$ and $\nu=\kappa/(4r)$. Divide $L$ into intervals of lengths comparable to $p^{1/4+\kappa}$, for example into $\lfloor |L|/p^{1/4+\kappa}\rfloor$ parts differing by at most one. The relative exponent on each part is at most
$$
 -\frac{1/4+\kappa}{r}+\frac1{4(r-1)}+\nu
 =-\frac{\kappa-1/(4(r-1))}{r}+\nu\le-\frac{\kappa}{2r}.
$$
All parts are within the theorem's length range for large $p$, including when $L$ wraps around zero, by taking integer representatives starting at its left endpoint. Summing gives assertion 2 with $\delta=\kappa/(2r)$.

At arbitrarily small polynomial lengths, assertion 1 alone suffices for all the linear twists. To see this, take a sum of length $h\ge p^\epsilon$ with phase $e^{2\pi i\alpha n}$ and put $Q=\lfloor\sqrt h\rfloor$. Dirichlet approximation gives $1\le q\le Q$ with $\|q\alpha\|_{\mathbb R/\mathbb Z}\le1/Q$. Separate the terms into classes modulo $q$ and partition each class into successive pieces of at most $Q$ terms. There are at most $q+h/Q=O(\sqrt h)$ pieces. On each piece the exponential has total variation at most $2\pi$. Along a class $n=u+qj$ one has $\chi(n)=\chi(q)\chi(j+u/q)$ in the field. Every partial character sum on a piece has size $O_\epsilon(Qp^{-\delta(\epsilon/4)}+p^{\epsilon/4})$, using assertion 1 on long prefixes and their length on short ones. Partial summation and $Q\asymp\sqrt h$ therefore give a mixed-sum bound
$$
 O_\epsilon\!\left(h(p^{-\delta(\epsilon/4)}+p^{-\epsilon/4})\right).
$$
This proves $1\Rightarrow 2$ by applying the finite Fourier estimate to $L$.

## From the union rank to an ordinary interval sum

For $X=I\cup J$, partition $X$ into the disjoint sets $I$ and $J\setminus I$. Each of the four blocks of $P_X$ has operator norm at most the bound $M$ in assertion 2. The full norm is at most $2M$ by Cauchy–Schwarz on the two component norms. With $n=|X|$, its squared Frobenius norm is $n(n-1)$, so the sum $E(X)$ of fourth powers of singular values is at most $4M^2 n(n-1)$. The exact identity
$$
 E(X)=n(n-1)(2n-3)+8\chi(-1)\left(4D(X)-\binom n4\right)
$$
now proves assertion 3 with error $O(M^2/H^2+1/H)$ since $H\le n\le2H$. This also proves the projective version for the same union. [Four-site identity](paley-four-site-rank.md)

Conversely assume 3 and write $a=\min(\epsilon,\delta(\epsilon))$. Then $E(X)\ll_\epsilon H^4p^{-a}$ on every such union. Given $s,H$, take $I=[s,s+H)$, $J=-[0,H)$ (both are unit-step progressions after ordering), and $B=-[0,K)$ with $K=\lfloor Hp^{-a/4}\rfloor$. For all sufficiently large primes $K\asymp Hp^{-a/4}$. The rectangle fourth-moment bound gives
$$
 \frac{|S(I,B)|}{HK}\le\frac{E(X)^{1/4}}{\sqrt{HK}}\ll_\epsilon p^{-a/8}.
$$
If $T(s,H)=\sum_{i=0}^{H-1}\chi(s+i)$ then $|S(I,B)-KT(s,H)|\le K(K-1)$ by sliding the interval. Thus $|T(s,H)|/H\ll_\epsilon p^{-a/8}+K/H$, proving assertion 1. In particular, the all-scale rank law even on these two-progression unions would imply a least quadratic nonresidue of size $p^{o(1)}$ on the same prime family. An arbitrary polynomial-size set in the full Paley conjecture need not admit such a representation. [Interval comparison and nonresidue consequence in Lean](paley-interval-criterion.md)
