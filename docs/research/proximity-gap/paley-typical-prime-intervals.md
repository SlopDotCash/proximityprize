# Paley operator norms on one progression for almost every prime

Fix $0<\epsilon\le 1$ and $0<\eta<1/2$. For all but $O_{\epsilon,\eta}(P^{1/4+\eta})$ primes $p\in[P,2P]$, the following bound holds **simultaneously** for every integer $p^\epsilon\le H\le p$, every length-$H$ arithmetic progression $I\subseteq\mathbb F_p$ of nonzero step, and every $g\in\mathrm{PGL}_2(\mathbb F_p)$:
$$
  \|M_{gI}\|_{2\to2}\ll_{\epsilon,\eta} H p^{-\delta},\qquad \delta=\delta(\epsilon,\eta)>0.
$$
Here $M_X$ is the principal quadratic Paley matrix on $X$. On finite sites its entries are $\chi_p(x-y)$, including zero on the diagonal. Both sides of a rectangle may be chosen after seeing the entire matrix. For $A,B\subseteq gI$ and complex row and column weights of absolute value at most one, the absolute weighted discrepancy is $O_{\epsilon,\eta}(H p^{-\delta}\sqrt{|A||B|})$. This gives a relative saving $O_{\epsilon,\eta}(p^{-\delta/2})$ whenever $\sqrt{|A||B|}\ge H p^{-\delta/2}$. The interval is common to the two sets. Arbitrary prescribed sets in the full Paley conjecture need not lie together in a progression of comparable size.

The exception estimate combines Heath-Brown's quadratic large sieve at short lengths with the published mixed Burgess bound at larger lengths. Using just the large sieve and the complete Paley norm gives $O_{\epsilon,\eta}(P^{1/2+\eta})$ exceptions, with the explicit saving $\delta=\eta/(2r+2)$ for $r=1+\lceil 1/(2\epsilon)\rceil$. Both exception counts are absolute numbers of primes. Their fractions among primes in the dyadic interval acquire a factor $O(\log P/P)$. [Heath-Brown, Corollary 3, p. 238](https://matwbn.icm.edu.pl/ksiazki/aa/aa72/aa7234.pdf) · [Heath-Brown and Pierce, Theorem 1.4](https://arxiv.org/pdf/1404.1677)

## A moment estimate for a fixed frequency

Let $2\le D<P$, let $z_t$ be any complex numbers with $|z_t|\le 1$, fixed independently of $p$, and set $T_p=\sum_{1\le t<D}z_t\chi_p(t)$. For each fixed positive integer $r$ and every $\xi>0$,
$$
 \sum_{P\le p\le2P}|T_p|^{2r}\ll_{r,\xi} P^\xi (P+D^r)D^r,                 \tag{1}
$$
where the sum is over odd primes. Indeed write $T_p^r=\sum_{m\le D^r}a_m\chi_p(m)$ by multiplying the $r$ sums. Each $|a_m|$ is at most the number $d_r(m)$ of ordered factorizations of $m$ into $r$ positive integers. For every $\nu>0$ one has $d_r(m)\ll_{r,\nu}m^\nu$. To see this, $d_r(\ell^a)=\binom{a+r-1}{r-1}\le r^a$ for primes $\ell$, and this is at most $\ell^{\nu a}$ for $\ell\ge r^{1/\nu}$. For each of the finitely many smaller primes the polynomial in $a$ is $O_{r,\nu,\ell}(\ell^{\nu a})$. Multiply over the prime factors.

Corollary 3 of the quadratic large sieve bounds $\sum_\chi |\sum_{m\le N}a_m\chi(m)|^2$, over all real primitive characters of conductor at most $Q$, by $O_\nu((QN)^\nu (Q+N)N\max_m|a_m|^2)$. It applies to coefficients on **all positive integers**, including squares and even integers. The Legendre characters in (1) are distinct members of the family with $Q=\lceil2P\rceil$. Take $N=D^r$ and choose $\nu$ small enough in terms of $r,\xi$ to absorb both the sieve and divisor factors into $P^\xi$. This proves (1) uniformly in the coefficients. Munsch, Shparlinski, Sun and Xiao also state this initial-interval moment explicitly in their introduction. [Heath-Brown, *A mean value estimate for real character sums*](https://matwbn.icm.edu.pl/ksiazki/aa/aa72/aa7234.pdf) · [Munsch et al., §1.1](https://arxiv.org/html/2604.23661v3#S1.SS1)

## From frequencies to interval matrices

For $0\le i,j<D$ the matrix $M_{[0,D)}$ has entry $\chi_p(i-j)$. On $\mathbb Z/(2D)$ define $c_0=c_D=0$ and, for $1\le t<D$, set $c_t=\chi_p(t)$ and $c_{2D-t}=\chi_p(-1)\chi_p(t)$. The circulant with entries $c_{i-j\bmod 2D}$ contains $M_{[0,D)}$ as its leading principal block. Its discrete Fourier eigenvalues are
$$
 T_p(k)+\chi_p(-1)\overline{T_p(k)},\qquad
 T_p(k)=\sum_{1\le t<D}\chi_p(t)e^{2\pi i kt/(2D)},\quad 0\le k<2D,
$$
up to reindexing $k$ by $-k$. Unitary Fourier diagonalization bounds the norm of the block by $2\max_k|T_p(k)|$, also for the skew matrix at $p\equiv3\pmod4$. The modulus $2D$ of this Fourier grid is independent of the prime. Applying (1) to each grid point and summing Markov's inequality over the $2D$ points yields
$$
 \#\{p\in[P,2P]:\|M_{[0,D)}\|>2D P^{-\delta}\}
 \ll_{r,\xi}P^{\xi+2r\delta}\big(P/D^{r-1}+D\big).                     \tag{2}
$$

Only dyadic $D$ are needed. For each actual $H$, choose the least power of two $D\ge H$. Its leading $H$-block has norm at most that of the $D$-block and $D<2H$ when $H\ge1$. Translation preserves all entries, and a nonzero common step $d$ contributes only the global sign $\chi_p(d)$. On the projective line use lifts $v_x=(x,1)^t$ and $v_\infty=(1,0)^t$ and entries $\chi_p(\det[v_x,v_y])$. Acting on the lifts gives one global sign and one sign per vertex, so projective images have the same singular values even when they include infinity. [Projective sign conventions](paley-four-site-rank.md)

For the $P^{1/2+\eta}$ exception count, take $r=1+\lceil1/(2\epsilon)\rceil$ and $\delta=\eta/(2r+2)$. For $P^\epsilon\le H\le P^{1/2+\delta}$, the required $D$ satisfy $P/D^{r-1}\le\sqrt P$ and $D\le2P^{1/2+\delta}<P$ for large $P$. Summing (2) over $O(\log P)$ dyadic lengths therefore costs
$$
 O_{r,\xi}\!\left((\log P)P^{1/2+(2r+1)\delta+\xi}\right)=O_{\epsilon,\eta}(P^{1/2+\eta}),
$$
say with $\xi=\delta/3$. For $H>P^{1/2+\delta}$ the complete affine matrix has norm $\sqrt p$. Its Gram matrix is $pI-J$, because the diagonal row norm squared is $p-1$ and the correlation of two distinct rows is $-1$ by the ratio substitution $y\mapsto(x-y)/(z-y)$. Thus every block has norm at most $\sqrt p\le\sqrt2 H P^{-\delta}$. In these estimates $p$ and $P$ differ by at most a factor of two.

For the sharper exception count put $\kappa=\min(\eta/4,1/16)$, $\beta=1/4+\kappa$ and $r=1+\lceil(1-\beta)/\epsilon\rceil$. At lengths $H\ge p^\beta$, the mixed Burgess estimate gives $\|M_I\|\ll_\kappa H p^{-b(\kappa)}$ for every prime, with $b(\kappa)>0$. The cited transfer allows independent interval starts at these larger lengths. For the remaining $p^\epsilon\le H<p^\beta$, all required dyadic lengths satisfy $P^\epsilon\le D\le 2(2P)^\beta$ and $P/D^{r-1}\le P^\beta$. Choose $\delta=\min(b(\kappa),\eta/(8r))$ and $\xi=\eta/8$. The total exceptional count in (2) is $O_{\epsilon,\eta}((\log P)P^{\beta+2r\delta+\xi})=O_{\epsilon,\eta}(P^{1/4+\eta})$. [Two-progression operator bound and exponents](paley-two-interval-rank.md)

There is also one family of primes for **all fixed exponents**. Fix $\eta$ and apply the sharper result with parameters $(1/j,\eta/2)$ for each positive integer $j$. Choose increasing dyadic thresholds $P_m\to\infty$ such that for $P\ge P_m$ the first $m$ bounds all hold and the sum of their exceptional-count constants is at most $P^{\eta/2}$. On a dyadic block $[P,2P)$ with $P_m\le P<P_{m+1}$, remove the union of those first $m$ exceptional sets. This deletes at most $P^{1/4+\eta}$ primes. For any fixed $\epsilon>0$, choose $j$ with $1/j\le\epsilon$. Every sufficiently large retained prime then satisfies the estimate for all $H\ge p^\epsilon$ with the fixed positive saving from that $j$. An arbitrary dyadic interval $[P,2P]$ meets at most three of the half-open power-of-two blocks, so the same order of exceptions holds there.

## Four-site ranks and labeled lists

For $X=gI$, write $\Lambda=\|M_X\|$. Every $Y\subseteq X$ of size $n\ge4$ has $\|M_Y\|\le\Lambda$ and $\|M_Y\|_F^2=n(n-1)$. Thus its four-cycle energy, the sum of the fourth powers of its singular values, is at most $\Lambda^2 n(n-1)$. If $N(Y)$ counts unordered four-subsets whose principal minor is singular modulo three, the exact four-site normalization gives
$$
 \left|\frac{N(Y)}{\binom n4}-\frac14\right|\ll \frac{1}{n}+\frac{H^2p^{-2\delta}}{n^2}.
$$
In particular the quarter law holds simultaneously for all $Y\subseteq X$ of size at least $H p^{-\delta/2}$, at every length in the theorem. [Four-site determinant and normalization](paley-four-site-rank.md)

For a coordinate subset $U\subseteq X$ of size $u>0$, form a binary word for each row label $x\in X$ by replacing its possible zero coordinate with either sign. For any binary sign center $w$ on $U$ and $t>0$ with $tu>1$, the number of row labels within Hamming distance $(1-t)u/2$ is at most
$$
 \frac{\Lambda^2 u}{(tu-1)^2}.
$$
Indeed each such label has binary correlation at least $tu$, and returning its possible diagonal site to zero decreases the correlation by at most one. The vector of all ternary correlations has squared norm at most $\Lambda^2\|w\|_2^2=\Lambda^2 u$ by zero extension. The bound counts labels with multiplicity for every center, including centers chosen after the prime and the coordinate subset. [Labeled-row decoding convention](paley-labeled-row-decoding.md)
