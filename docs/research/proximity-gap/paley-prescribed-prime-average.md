# Prescribed integer sets over almost every prime

Fix integers $P\ge3$ and $1\le H\le P$. Let $A,B$ be nonempty subsets of a common interval of $H$ consecutive integers. They may be chosen anew in each dyadic range, before choosing the prime $p\in[P,2P]$. Write $a=|A|, b=|B|$, and let $M_p=(\chi_p(x-t))_{x\in A,t\in B}$, with the Legendre symbol zero on multiples of $p$. All sums over $p$ below run over the odd primes in that range. The bounds are uniform over the shapes and the location of the interval. Factors $P^{o(1)}$ can be replaced by $C_\nu P^\nu$ for every fixed $\nu>0$.

**Weights chosen on one side after the prime.** Fix any complex vector $v$ on $B$ with $|v_t|\le1$, independently of $p$. Then
\[
 \sum_p \left(\sup_{|w_x|\le1}
       \frac{|w^* M_p v|}{ab}\right)^2
 \ll P^{1+o(1)}\left(\frac1a+\frac1b\right).                       \tag{1}
\]
In particular if $a,b\ge P^\epsilon$, for every $0<\delta<\epsilon/2$ the relative discrepancy is at most $P^{-\delta}$ outside $O(P^{1-\epsilon+2\delta+o(1)})$ primes. The weights $w$ may select any subset of $A$ after seeing $p$. Its sum in (1) is normalized by the original area $ab$. A subset occupying a fixed positive fraction of $A$ therefore retains the same power saving relative to its own area. This conclusion allows $H=P$.

**Both sides chosen after the prime.** Put $m=\min(a,b)$, $n=\max(a,b)$. For the Euclidean operator norm,
\[
 \sum_p\left(\frac{\|M_p\|}{\sqrt{ab}}\right)^4
 \ll P^{o(1)}\left(\frac{P}{m}+\frac{P+H^2}{n}\right).            \tag{2}
\]
Thus if $m\ge P^\epsilon$ and $H^2\le P^{1-\epsilon}n$, then outside $O(P^{1-\epsilon+4\delta+o(1)})$ primes the operator norm is at most $\sqrt{ab}\,P^{-\delta}$ for any fixed $0<\delta<\epsilon/4$. This includes arbitrary prescribed sets in an interval of length $\sqrt P$ whenever both sizes are at least $P^\epsilon$. For $a,b\asymp\sqrt P$ it also permits $H\le P^{3/4-c}$ for every fixed $c>0$ in the feasible range. The resulting bound permits arbitrary complex weights of modulus at most one on both sides after seeing $p$. On subsets of sizes $a',b'$, the absolute bound is $\sqrt{ab\,a'b'}\,P^{-\delta}$.

The full-interval estimate (4) below allows both sides to choose weights after seeing the prime at every polynomial set size, even when $H=P$. Two other bounds give stronger exponents for shorter intervals.

The same operator bound holds simultaneously in every common projective chart at each retained prime. Applying a projectivity to lifts on the projective line changes a quadratic character of a determinant by a global sign and signs at the vertices. The resulting matrices have the same singular values, including at infinity with projective coordinates. Dropping a pole restricts the matrix. The exceptional prime sets in (1) and (2) may depend on the prescribed integer data. For a library of $L$ such choices, a union bound multiplies the exceptional counts by at most $L$. [Projective sign convention](paley-four-site-rank.md)

## The large sieve and a divisor count

For positive indices $d\le N\le P^2$ and complex coefficients $c_d$, Heath-Brown's quadratic large sieve gives
\[
 \sum_p\left|\sum_{d\le N} c_d\chi_p(d)\right|^2
 \ll P^{o(1)}(P+N)
      \sum_{d,e:\,de\text{ is a square}} |c_d c_e|.
\]
Indeed the Legendre characters are distinct real primitive characters of conductor at most $2P$. Corollary 2 permits arbitrary positive indices, including even integers and indices with square factors. Split positive and negative arguments before applying it, using $|U+\chi_p(-1)V|^2\le2(|U|^2+|V|^2)$. Zero factors contribute zero and are omitted. Every other difference has absolute value less than $H\le p$. Even when the product of two such differences exceeds $p$, neither factor is divisible by $p$. [Heath-Brown, Corollary 2, p. 238](https://doi.org/10.4064/aa-72-3-235-275)

Fix a row $x\in A$ and a sign for $x-t$. Apply the sieve with $N=H$ to the coefficients $v_t$ at the indices $|x-t|$. At this fixed sign the indices are distinct. Summing the square-pair counts over $x$, the terms $t=u$ contribute at most $ab$ over both signs. For $t\ne u$, a counted pair has $(x-t)(x-u)=z^2>0$, whence
\[
 (2x-t-u-2z)(2x-t-u+2z)=(t-u)^2 .
\]
Each ordered signed factorization determines at most one $x$. The number of choices for each $t,u$ is at most $2\tau((t-u)^2)=P^{o(1)}$, by the integer divisor bound. Therefore
\[
 \sum_p\sum_{x\in A}|(M_pv)_x|^2\ll P^{1+o(1)}(ab+b^2).
\]
Cauchy–Schwarz bounds $|w^*M_pv|^2$ by $a\sum_x |(M_pv)_x|^2$ simultaneously for all permitted $w$. This proves (1).

## Multiplicity of a squarefree part

For distinct integers $x,y$ in the interval and a prescribed signed squarefree integer $D\ne0$, the number of $t$ in the interval such that $(t-x)(t-y)=D z^2\ne0$ for some integer $z$ is $H^{o(1)}$, uniformly in $D,x,y$ as $H\to\infty$. Take $z>0$, $U=2t-x-y$, $V=2z$ and $k=|x-y|>0$. Then
\[
 U^2-DV^2=k^2,\qquad |U|\le 2H,\qquad \sqrt{|D|}\,V\le2H.
\]
If $D=1$, factor $(U-V)(U+V)=k^2$ and use the divisor bound. For the other $D$, take $g=\gcd(|U|,V)$. Then $g\mid k$, and the primitive pair $u=U/g,v=V/g$ has $u^2-Dv^2=N=(k/g)^2$. We have $(v,N)=1$, since a prime dividing both would divide $u$. Also $(D,N)=1$. A prime dividing both would divide $u$ and, since $N$ is a square and $D$ is squarefree, reduction modulo its square would contradict $(u,v)=1$.

For each $g$, the residue $r=u/v\pmod N$ satisfies $r^2\equiv D\pmod N$. There are at most $4\cdot 2^{\omega(N)}$ such classes by the Chinese remainder theorem and the square-root counts for units modulo prime powers. Use the single residue class when $N=1$. Two solutions in the same class have a quotient
\[
 \frac{u+v\sqrt D}{u'+v'\sqrt D}
 =\frac{uu'-Dvv'+(u'v-uv')\sqrt D}{N}\ \in\mathbb Z[\sqrt D]
\]
of norm one. The two divisibilities follow from $r^2\equiv D\pmod N$. For $D<0$, this ring has at most four integral norm-one elements, directly from $s^2+|D|t^2=1$. For $D>1$, a real integral norm-one element $e=s+t\sqrt D$ of absolute value greater than one satisfies
\[
 |e|-|e|^{-1}=|e-e^{-1}|=2|t|\sqrt D\ge2.
\]
Thus the distinct absolute values of $u+v\sqrt D$ in a class are separated by factors greater than two. Both real embeddings have absolute value at most $4H$ and their product is $N\ge1$, so the absolute values lie in $[(4H)^{-1},4H]$. Each class contributes $O(\log(2H))$ solutions, allowing both signs. Summation over $g\mid k$ and the residue classes proves the uniform multiplicity bound.

## The Gram matrix

Transposing $M_p$ if necessary, take the row side of size $m$ and the column side of size $n$. Reversing a difference contributes only the global sign $\chi_p(-1)$. A diagonal entry of $M_pM_p^*$ is at most $n$. For distinct rows $x,y$, its entry is
\[
 G_p(x,y)=\sum_{t\text{ on the column side}}\chi_p((t-x)(t-y)).
\]
Split the signs of the integer product and apply the large sieve at $N=H^2$. Within each sign, two positive indices have square product exactly when their squarefree parts agree. After expanding the coefficients as site counts, the sum of square-pair counts is at most $nH^{o(1)}$ by the multiplicity bound. Thus
\[
 \sum_p |G_p(x,y)|^2\ll P^{o(1)}(P+H^2)n.
\]
The fourth power of the operator norm is at most $\operatorname{tr}((M_pM_p^*)^2)=\sum_{x,y}|G_p(x,y)|^2$. The diagonal terms over all primes contribute $O(Pmn^2)$, and summing the last bound over distinct rows gives $O(P^{o(1)}(P+H^2)m^2 n)$. Division by $m^2 n^2$ proves (2), and the exceptional counts follow from Markov's inequality. This proves a statement about primes averaged after the sets are prescribed. The Paley conjecture asks for control at a fixed prime over all admissible sets.

## Two adaptive sides in intervals of length up to a fixed power below $P$

Fix $0<c<1$. For arbitrary prescribed integer sets $A,B$ in a common interval of length $H\le P^{1-c}$, both sets of weights may depend on the prime. In fact if $a,b\ge P^\epsilon$, choose any integer $r\ge2$ with $cr>1-c$, and put
\[
 \theta=\min\!\left(\epsilon,\frac{c}{r}-\frac{1-c}{r^2}\right)>0 .
\]
For every fixed $0<\delta<\theta/4$, outside $O(P^{1-\theta+4\delta+o(1)})$ primes in $[P,2P]$ one has
\[
                \|M_p\|_{2\to2}\le\sqrt{ab}\,P^{-\delta}.          \tag{3}
\]
This includes all polynomial sizes that fit the interval. It gives the same estimate after any common projectivity in projective coordinates and the same four-site rank conclusion on a single prescribed domain as the earlier norm estimate. When $A=B$ and $a\ge P^\epsilon$, the proportion of singular principal four-site minors is $1/4+O(P^{-2\delta}+1/a)$. The fourth trace is at most the squared operator norm times the squared Frobenius norm, hence at most $a^4P^{-2\delta}$. [Four-site identity](paley-four-site-rank.md#exact-normalization-and-the-four-site-determinant)

For odd $d\in[P,2P]$ let $M_d$ use the Jacobi symbol $(\cdot/d)$ in place of the Legendre symbol. Every matrix is real, so $T_d=\operatorname{tr}((M_dM_d^*)^2)\ge0$. We have the pointwise comparison
\[
 \sum_{p\in[P,2P]}\|M_p\|^4\le\sum_{d\in[P,2P],\ d\ {\rm odd}}T_d .
\]
Expansion of the right side produces sums over odd $d$ of $(K/d)$, where $K=(x-t)(y-t)(x-u)(y-u)$, for $x,y\in A$, $t,u\in B$. Zero products vanish. Write $q$ for the odd part of the squarefree kernel of $|K|$.

If $q>1$, the character $n\mapsto(n/q)$ is primitive of odd squarefree conductor $q\le H^4$. Write $K=\pm 2^e q s^2$ with $s$ odd after putting all factors of two in $2^e$. On each odd residue class modulo eight, quadratic reciprocity makes $(K/d)$ a fixed sign times $(d/q)\mathbf1_{(d,s)=1}$. Expand the indicator by Möbius inversion. For each divisor $m\mid s$, terms with $(m,q)>1$ vanish. In the others write $d=mn$. The inner variable runs over one residue class modulo eight, and $(n/q)$ there becomes a constant times an ordinary consecutive character sum, since eight is invertible modulo $q$. There are $P^{o(1)}$ divisors and each sum has length at most $2P$. The cubefree Burgess inequality therefore gives
\[
 \left|\sum_{P\le d\le2P,\ d\ {\rm odd}}(K/d)\right|
 \ll_r P^{1-1/r+o(1)}H^{(r+1)/r^2}.
\]
If the length exceeds the conductor, complete periods have sum zero. The remaining interval satisfies the same bound. [Burgess bound for cubefree moduli, formula in the authors’ abstract](https://arxiv.org/abs/2511.17778)

If $q=1$, use the trivial bound $O(P)$. The terms with $x=y$ account for at most $ab^2$ quadruples. For $x\ne y$ and fixed $t$, put $F_v=(x-v)(y-v)$. The odd squarefree kernel of $|F_u|$ must equal that of $|F_t|$. There are at most four choices for its signed squarefree part, allowing both signs and either parity of the exponent of two. The Pell equation count above allows $H^{o(1)}$ choices of $u$ in each class. Thus the total number of nonzero exceptional quadruples is $O(ab^2+a^2bH^{o(1)})$.

Dividing the trace sum by $a^2b^2$ gives
\[
 \sum_p\frac{\|M_p\|^4}{a^2b^2}
 \ll_r P^{o(1)}\left(\frac Pa+\frac Pb
          +P^{1-1/r}H^{(r+1)/r^2}\right).
\]
Substituting $H\le P^{1-c}$ and applying Markov gives (3). At $H=P$ the final term in this argument has exponent $1+1/r^2$, which yields no power saving from the individual-conductor bound at full diameter.

## Both sides adaptive throughout the full interval

Let $m=\min(a,b)$ and $n=\max(a,b)$. For any prescribed sets in an interval of length $H\le P$,
\[
 \boxed{\quad \sum_{P\le p\le2P}
   \left(\frac{\|M_p\|}{\sqrt{ab}}\right)^4
 \ll P^{1+o(1)}\left(m^{-1}+n^{-1/8}\right).\quad}                 \tag{4}
\]
Thus if $a,b\ge P^\epsilon$, for every $0<\delta<\epsilon/32$ the two-sided norm bound (3) holds outside $O(P^{1-\epsilon/8+4\delta+o(1)})$ primes. At a retained prime the bound is simultaneous for all choices of complex weights on both sides and every common projective image. With $A=B$ the singular four-site fraction is consequently $1/4+O(P^{-2\delta}+1/a)$. The exceptional set of primes may depend on the two integer sets.

More generally, for any fixed $C>0$, suppose $H\le P^C$ and choose an integer $k\ge\max(2,4C)$. Then (4) holds with $n^{-1/(2k)}$ replacing $n^{-1/8}$. If the labels include integers with equal residues modulo a prime, the matrix in this claim is indexed by the original integer labels. The graph interpretation on all labels applies at primes with injective reduction on the domain.

To prove this, use the same nonnegative trace over odd moduli and the same decomposition of $K$ as above. By transposition arrange that $a=m$ and $b=n$. For every odd squarefree $q>1$ with $q\le Q=H^4$, put
\[
 U(q)=\max_{\substack{1\le e\le2P \\ j=1,3,5,7}}
 \left|\sum_{\substack{P/e\le v\le 2P/e\\v\equiv j\bmod 8}}(v/q)\right|.
\]
The Möbius expansion over the square factor $s$ shows that the complete odd-modulus sum for this $K$ is at most $4\tau(s)U(q)$ in absolute value. It suffices that $K\ne0$ and its odd squarefree kernel is $q$, including when $s$ and $q$ share prime factors.

For fixed $e,j$, raise the inner character sum to its $k$-th power. Its coefficients $c_\ell$ count ordered $k$-tuples of the permitted integers with product $\ell\le N=\lfloor 2P/e\rfloor^k$. Thus $0\le c_\ell\le d_k(\ell)=P^{o(1)}$ uniformly, for fixed $k$. The number of ordered pairs of positive integers at most $N$ whose product is a square is bounded by
\[
 \sum_{h\le N\ {\rm squarefree}}\left\lfloor\sqrt{N/h}\right\rfloor^2
 \le N(1+\log N).
\]
Apply the arbitrary-index quadratic large sieve to these coefficients and the distinct primitive characters $(\cdot/q)$. Its bound for the sum of squared magnitudes of these $k$-th powers is $P^{o(1)}(Q+N)N$. Summing over the four classes and $e\le2P$ also bounds the maximum defining $U$. Since $Q\le P^k$, $N\le(2P/e)^k$ and $k\ge2$, summing the convergent series in $e^{-k}$ gives
\[
                         \sum_q U(q)^{2k}\ll P^{2k+o(1)} .          \tag{5}
\]
Constants may depend on $C$ and $k$. [Heath-Brown, Corollary 2](https://matwbn.icm.edu.pl/ksiazki/aa/aa72/aa7234.pdf)

For each fixed odd squarefree $q$, let $N_q$ count nonzero-product quadruples with $x\ne y$ and odd squarefree kernel $q$. Once $x,y,t$ are fixed, the odd squarefree part of $|F_u|$ is determined: its prime factors are the symmetric difference of those of $q$ and the odd squarefree part of $|F_t|$. The sign and the factor of two leave at most four signed squarefree values. The uniform Pell estimate yields
\[
             N_q\le a^2 b\,P^{o(1)},\qquad \sum_q N_q\le a^2b^2 .
\]
This holds also for $q=1$, whose contribution is bounded separately by $O(PN_1)$. Weighted Hölder and (5) give
\[
 \sum_{q>1} N_q U(q)
  \le \left(\sum_q N_q\right)^{1-1/(2k)}
       \left(\max_q N_q\sum_{q>1}U(q)^{2k}\right)^{1/(2k)}
  \ll a^2b^2 P^{1+o(1)}b^{-1/(2k)} .
\]
Finally, $x=y$ contributes at most $O(Pab^2)$ before normalization. Adding all three contributions and dividing by $a^2b^2$ proves the claim. This averaging argument gives a power saving even when the single-conductor Burgess estimate reaches its length threshold.

In fact the same exceptional-count exponent holds when normalizing by the sizes of the **distinct reductions**, even for $H\le P^C$. Suppose $0<\epsilon\le1$, $a,b\ge P^\epsilon$ and put $\eta=\epsilon/(2k)$. Truncate each side $X$ to any $s=\min(|X|,\lfloor P^{1-\eta}\rfloor)$ integer labels. Each nonzero difference of magnitude at most $P^C$ has at most $C$ prime divisors in $[P,2P]$. Thus the ordered distinct colliding pairs, summed over these primes, number $O_C(s^2)$. If fewer than $s/2$ residues survive, Cauchy–Schwarz gives more than $s$ such pairs. Exclude $O_C(P^{1-\eta})$ primes for each side. When neither side was truncated, take one representative per residue in the labelled operator. Normalizing by the distinct-image sizes loses at most a factor two, which can be absorbed by doubling the threshold in the moment estimate. If a side was truncated, the product of the full image sizes is $\gg P^{1-\eta+\min(\epsilon,1-\eta)}$. By shift orthogonality the complete Paley matrix has norm $\sqrt p$. Dividing by the square root of the image-size product saves exponent $(\min(\epsilon,1-\eta)-\eta)/2>\eta/4$, since $\eta\le\epsilon/4\le1/4$. In both cases, for every fixed $0<\delta<\eta/4$, the normalized distinct-image norm is at most $P^{-\delta}$ outside $O(P^{1-\eta+4\delta+o(1)})$ primes.
