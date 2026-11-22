# Paley discrepancy on short arcs for almost every torus generator

Fix a split or nonsplit maximal torus $T$ in $\mathrm{PGL}_2(\mathbb F_p)$ at an odd prime. Its regular orbit $\Omega$ has $m=|T|=p-1$ or $p+1$ sites. Fix exponent sets $I,J\subseteq[0,D]\cap\mathbb Z$ before choosing the generator. Write $n=\min(|I|,|J|)$ and $N=\max(|I|,|J|)$. For a generator $g$ and starting point $x\in\Omega$, define the rectangular matrix
$$
 P_g(i,j)=\chi\big(\det(v_{g^ix},v_{g^jx})\big)\qquad (i\in I,\ j\in J),
$$
where the $v$ are nonzero homogeneous lifts and $\chi(0)=0$. Its operator norm is independent of the lifts and of $x$. A simultaneous projectivity taking $x$ to another point in $\Omega$ can be chosen in $T$, so it commutes with $g$ and only changes vertex signs and one global sign. The starting point may thus be selected after $g$. [Torus action and projective signs](paley-torus-translates.md#the-character-sum-over-the-torus)

Fix $\epsilon,\kappa>0$, and assume $n\ge p^\epsilon$, $D\le p^{1/2-\kappa}$. For an integer $r\ge2$ put $b=\min((r-1)\epsilon,\kappa)$. For every $0<\delta<b/(2r)$, the fraction of generators for which
$$
 \|P_g\|>\sqrt{nN}\,p^{-\delta}
$$
is $O_r(p^{-b+2r\delta+o(1)})$. This holds at each sufficiently large prime and for every prescribed pair of exponent sets satisfying the hypotheses. At a good generator, arbitrary weights and subsets may be chosen after inspection of the arc. In particular any row subset $A$ and column subset $B$ have absolute signed discrepancy at most $\sqrt{nN|A||B|}\,p^{-\delta}$, also for arbitrary vertex weights of modulus at most one. Constant-density subsets therefore have a power saving relative to $|A||B|$. The result allows an exceptional set of generators at the prescribed placement.

## The character polynomial in the generator

Represent torus parameters by projective classes of matrices in the two-dimensional algebra $V=\mathbb F_p\times\mathbb F_p$ or $\mathbb F_{p^2}$ acting by multiplication. Their invertible classes form $T$ inside $\mathbf P(V)$. Use a fixed vector $v$ representing $x\in\Omega$ and lifts $A^iv$ at parameter $A$. For nongenerators, keep all exponent labels even when several of them give the same projective point. Over the algebraic closure the eigenvalues $a,b$ of multiplication are two independent linear forms in the parameter coordinates. Both components of $v$ in this eigenbasis are nonzero since $x$ is in the regular orbit. For $i\ne j$, the bracket $\det(A^iv,A^jv)$ is, up to a fixed nonzero scalar and a sign depending on the order of $i,j$,
$$
 (ab)^{\min(i,j)}(a^d-b^d),\qquad d=|i-j|.
$$
The original brackets are polynomials defined over $\mathbb F_p$ in both torus cases. The displayed factorization also applies when the two eigenlines are conjugate.

Expand $\mathrm{tr}((P_AP_A^*)^r)$ in closed alternating walks with $2r$ edges. An edge between equal exponents contributes zero identically. For every other walk the product of brackets is a homogeneous polynomial $F$ of even degree, since each visited exponent contributes its degree twice. Its quadratic sign on a projective parameter is therefore independent of the representative, just as lift changes cancel around the walk.

Suppose some absolute edge distance occurs an odd number of times, and let $d$ be the largest such distance. At a parameter with $a/b$ a primitive $d$th root, the factor $a^d-b^d$ has a simple zero since $d\le D<p$. Every smaller positive distance contributes a nonzero factor, and each larger distance occurs with even multiplicity. Here $ab\ne0$. This gives $F$ a zero of odd multiplicity over the algebraic closure. The projective zeros of $F$ lie among $a=0$, $b=0$ and the roots of its at most $2r$ distance factors, giving at most $2rD+2$ distinct zeros. In a rational affine parameter chart the polynomial remains a nonsquare up to scalar since the total projective degree is even. The Weil character bound, the omitted point at infinity and deletion of at most two singular parameters give
$$
 \left|\sum_{A\in T}\chi(F(A))\right|\le(2rD+1)\sqrt p+3.
$$
This count permits even-multiplicity zeros and uses the degree in the exponent window. [Weil character estimate, Theorem A.1](https://link.springer.com/article/10.1007/s40879-021-00521-5)

If all distances occur evenly, pair equal-distance edges in at most $(2r-1)!!$ ways. Choose a starting vertex on the smaller side in $n$ ways. At a first occurrence of a pair there are at most $N$ choices of the next vertex. On the second occurrence, the distance and current exponent leave at most two choices. Thus at most $(2r-1)!!\,2^r nN^r$ walks use the trivial bound $m$. All other walks use the character estimate or contribute zero.

Every trace is nonnegative and dominates the $2r$th power of the corresponding norm. Retain only generators after summation over all of $T$. With $L_g=\|P_g\|/\sqrt{nN}$ this gives
$$
 \frac1{\varphi(m)}\sum_{g\text{ generator}}L_g^{2r}
 \le\frac{m}{\varphi(m)}(2r-1)!!\,2^r n^{1-r}
       +\frac{(2rD+1)\sqrt p+3}{\varphi(m)}.
$$
The elementary estimate $m/\varphi(m)=m^{o(1)}$ follows by bounding $\ell/(\ell-1)\le\ell^\eta$ at sufficiently large primes $\ell$ for each fixed $\eta>0$ and absorbing the finitely many smaller factors in a constant. Since $m=p\pm1$, Markov's inequality gives the stated fraction of exceptional generators.

## All arc lengths at one generator

For fixed $\epsilon,\kappa$ consider every integer $p^\epsilon\le H\le p^{1/2-\kappa}$. Test the principal blocks $I=J=[0,2^k)\cap\mathbb Z$ at the dyadic ceilings of these $H$. Their sizes are at least $p^\epsilon$ and their diameters at most $2p^{1/2-\kappa}$, which changes only the constant in the moment bound. A union bound over $O(\log p)$ tests preserves the exceptional fraction $O_r(p^{-b+2r\delta+o(1)})$. At every remaining generator the principal operator on every such $H$-term arc has norm at most $2Hp^{-\delta}$ by restricting the next larger dyadic block. The arbitrary starting point covers every cyclic translate of the exponent interval, including arcs crossing exponent zero.

In particular, let $X$ be any subset with $z=|X|\ge cH$ in any such arc, with fixed $c>0$. Compression bounds its Paley operator by $2Hp^{-\delta}$ and its squared Frobenius norm by $z^2$. Thus its fourth trace is at most $4H^2z^2p^{-2\delta}$. By the exact four-site identity, the fraction of four-subsets of $X$ with singular ternary principal Paley minor is
$$
 \frac14+O_c(H^{-1}+p^{-2\delta}).
$$
This applies simultaneously to all these dense subsets, common starting points and arc lengths at the chosen generator. [Four-site identity](paley-four-site-rank.md#exact-normalization-and-the-four-site-determinant)

Run the finite verifier from the repository root with `python3 -B scripts/probes/probe_paley_torus_generators.py`. It checks split and nonsplit parameterizations, the odd-distance square obstruction, walks with repeated sites at nongenerators, and the trace bound against independently formed Gram matrices. [Exact verifier](../../../scripts/probes/probe_paley_torus_generators.py)
