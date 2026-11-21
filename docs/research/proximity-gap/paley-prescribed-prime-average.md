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
