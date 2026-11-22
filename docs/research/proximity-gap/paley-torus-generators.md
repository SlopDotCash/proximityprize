# Paley discrepancy on short arcs for almost every torus generator

Fix a split or nonsplit maximal torus $T$ in $\mathrm{PGL}_2(\mathbb F_p)$ at an odd prime. Its regular orbit $\Omega$ has $m=|T|=p-1$ or $p+1$ sites. Fix exponent sets $I,J\subseteq[0,D]\cap\mathbb Z$ before choosing the generator. Write $n=\min(|I|,|J|)$ and $N=\max(|I|,|J|)$. Fix any relative translation $c\in T$, independently of the generator. For a generator $g$ and a common starting point $x\in\Omega$, define the rectangular matrix
$$
 P_g(i,j)=\chi\big(\det(v_{g^ix},v_{cg^jx})\big)\qquad (i\in I,\ j\in J),
$$
where the $v$ are nonzero homogeneous lifts and $\chi(0)=0$. Its operator norm is independent of the lifts and of $x$. A simultaneous projectivity taking $x$ to another point in $\Omega$ can be chosen in $T$, so it commutes with both $g$ and $c$ and only changes vertex signs and one global sign. This permits any two prescribed starting points, since exactly one $c$ sends the first to the second. The common starting point may also be selected after $g$ while keeping $c$ fixed. [Torus action and projective signs](paley-torus-translates.md#the-character-sum-over-the-torus)

Fix $\epsilon,\kappa>0$, and assume $n\ge p^\epsilon$, $D\le p^{1/2-\kappa}$. For an integer $r\ge2$ put $b=\min((r-1)\epsilon,\kappa)$. For every $0<\delta<b/(2r)$, the fraction of generators for which
$$
 \|P_g\|>\sqrt{nN}\,p^{-\delta}
$$
is $O_r(p^{-b+2r\delta+o(1)})$. This holds at each sufficiently large prime and for every prescribed pair of exponent sets and relative translation satisfying the hypotheses. At a good generator, arbitrary weights and subsets may be chosen after inspection of the arc. In particular any row subset $A$ and column subset $B$ have absolute signed discrepancy at most $\sqrt{nN|A||B|}\,p^{-\delta}$, also for arbitrary vertex weights of modulus at most one. Constant-density subsets therefore have a power saving relative to $|A||B|$. The result allows an exceptional set of generators at the prescribed placement.

## The character polynomial in the generator

Represent torus parameters by projective classes of matrices in the two-dimensional algebra $V=\mathbb F_p\times\mathbb F_p$ or $\mathbb F_{p^2}$ acting by multiplication. Their invertible classes form $T$ inside $\mathbf P(V)$. Use lifts $A^iv$ and $C A^jv$ at parameter $A$, where $C$ represents $c$. For nongenerators, keep all exponent labels even when several of them give the same projective point. Over the algebraic closure the eigenvalues $a,b$ of multiplication by $A$ are independent linear forms in its parameter coordinates. In this eigenbasis write the eigenvalues of $C$ as $u_1,u_2$, set $u=u_1/u_2$, and write $z=a/b$. The two components of $v$ are nonzero since $x$ is regular. Up to a fixed nonzero scalar the bracket is
$$
 a^i b^j u_2-b^i a^j u_1.
$$
When $ab\ne0$ and $d=|i-j|>0$, its zeros are $z^d=u$ for $i>j$, and $z^d=u^{-1}$ for $i<j$. At $i=j$ it is $(ab)^i(u_2-u_1)$ up to the same scalar. These brackets are defined over $\mathbb F_p$ before diagonalization, including when the eigenlines are conjugate.

Expand $\mathrm{tr}((P_AP_A^*)^r)$ in closed alternating walks with $2r$ edges. An edge between equal exponents contributes zero identically if $c=1$. For every walk without such an identically zero edge the product of brackets is a homogeneous polynomial $F$ of even degree, since each visited exponent contributes its degree twice. Its quadratic sign on a projective parameter is therefore independent of the representative, just as lift changes cancel around the walk.

Label every nonzero distance $d$ by its equation $z^d=w$, where $w=u$ or $u^{-1}$. If $u^2=1$ the two orientations have the same label. Suppose some label occurs oddly and take a largest $d$ among those labels. Write $s$ for the order of $w$, which divides $p\pm1$. There is a root of $z^d=w$ of exact order $ds$. Indeed the $d$th power of a primitive $ds$th root has order $s$. The exponent needed to reach $w$ is a unit modulo $s$ and can be lifted to a unit modulo $ds$ by avoiding the additional prime divisors of $d$. This includes $s=1$. Since $d<p$, the chosen zero is simple. No smaller positive distance $e<d$ can have a zero there, since $\operatorname{ord}(z^e)=s$ would require $\gcd(ds,e)=d$. At the same distance, any other label has a different $w$. Labels at larger distances have even multiplicity. The zero-gap and determinant factors stay nonzero at this parameter. Thus the product has an odd-multiplicity zero over the algebraic closure. The projective zeros of $F$ lie among $a=0$, $b=0$ and the roots of its at most $2r$ distance factors, giving at most $2rD+2$ distinct zeros. In a rational affine parameter chart the polynomial remains a nonsquare up to scalar since the total projective degree is even. The Weil character bound, the omitted point at infinity and deletion of at most two singular parameters give
$$
 \left|\sum_{A\in T}\chi(F(A))\right|\le(2rD+1)\sqrt p+3.
$$
This count permits even-multiplicity zeros and uses the degree in the exponent window. [Weil character estimate, Theorem A.1](https://link.springer.com/article/10.1007/s40879-021-00521-5)

If all nonzero labels occur evenly, the number of zero gaps also is even, since the walk has $2r$ edges. Pair equal-label edges (including pairs of zero gaps) in at most $(2r-1)!!$ ways. Choose a starting vertex on the smaller side in $n$ ways. At a first occurrence of a pair there are at most $N$ choices of the next vertex. On the second occurrence, the distance and current exponent leave at most two choices. Thus at most $(2r-1)!!\,2^r nN^r$ walks use the trivial bound $m$. All other walks use the character estimate or contribute zero.

Every trace is nonnegative and dominates the $2r$th power of the corresponding norm. Retain only generators after summation over all of $T$. With $L_g=\|P_g\|/\sqrt{nN}$ this gives
$$
 \frac1{\varphi(m)}\sum_{g\text{ generator}}L_g^{2r}
 \le\frac{m}{\varphi(m)}(2r-1)!!\,2^r n^{1-r}
       +\frac{(2rD+1)\sqrt p+3}{\varphi(m)}.
$$
The elementary estimate $m/\varphi(m)=m^{o(1)}$ follows by bounding $\ell/(\ell-1)\le\ell^\eta$ at sufficiently large primes $\ell$ for each fixed $\eta>0$ and absorbing the finitely many smaller factors in a constant. Since $m=p\pm1$, Markov's inequality gives the stated fraction of exceptional generators.

## Relative exponent offsets of short order

An offset specified in exponents as $g^k$ can depend on the chosen generator. Its order $s=m/\gcd(k,m)$ is fixed, so $g^k$ belongs to a set of at most $\varphi(s)$ physical translations as $g$ varies. Apply the preceding theorem to each translation and take a union bound. The exceptional fraction is
$$
 O_r\big(\varphi(s)\,p^{-b+2r\delta+o(1)}\big).
$$
In particular the half-period shift $k=m/2$ costs no factor: every generator has the same half-turn. More generally the bound accommodates offsets $k+e$ with fixed $|e|\le D$ by enlarging the exponent window to at most $2D$ after a common shift. It covers all offsets of order at most $p^\sigma$ at once with an extra $p^{\sigma+o(1)}$, since the number of possible physical translations is at most $p^\sigma$ times the divisor count of $m$. One still needs $\sigma+2r\delta<b$ for a power-saving exceptional fraction. An arbitrary prescribed physical translation already uses the original bound, whatever its order.

## All arc lengths at one generator

For fixed $\epsilon,\kappa$ consider every integer $p^\epsilon\le H\le p^{1/2-\kappa}$. Take $c=1$ and test the principal blocks $I=J=[0,2^k)\cap\mathbb Z$ at the dyadic ceilings of these $H$. Their sizes are at least $p^\epsilon$ and their diameters at most $2p^{1/2-\kappa}$, which changes only the constant in the moment bound. A union bound over $O(\log p)$ tests preserves the exceptional fraction $O_r(p^{-b+2r\delta+o(1)})$. At every remaining generator the principal operator on every such $H$-term arc has norm at most $2Hp^{-\delta}$ by restricting the next larger dyadic block. The arbitrary starting point covers every cyclic translate of the exponent interval, including arcs crossing exponent zero.

In particular, let $X$ be any subset with $z=|X|\ge cH$ in any such arc, with fixed $c>0$. Compression bounds its Paley operator by $2Hp^{-\delta}$ and its squared Frobenius norm by $z^2$. Thus its fourth trace is at most $4H^2z^2p^{-2\delta}$. By the exact four-site identity, the fraction of four-subsets of $X$ with singular ternary principal Paley minor is
$$
 \frac14+O_c(H^{-1}+p^{-2\delta}).
$$
This applies simultaneously to all these dense subsets, common starting points and arc lengths at the chosen generator. [Four-site identity](paley-four-site-rank.md#exact-normalization-and-the-four-site-determinant)

Run the finite verifier from the repository root with `python3 -B scripts/probes/probe_paley_torus_generators.py`. It checks split and nonsplit parameterizations, the odd-distance square obstruction, walks with repeated sites at nongenerators, and the trace bound against independently formed Gram matrices. [Exact verifier](../../../scripts/probes/probe_paley_torus_generators.py)
