# A covering obstruction for the Paley torus estimates

Fix an odd prime $p$, put $N=p+1$, and choose a uniform $s$-subset $S$ of $\mathbf P^1(\mathbb F_p)$, where $1\le s\le\sqrt N$. With probability at least $1-N^{-4}$, the following holds **simultaneously** for every nonempty $x$-site template $X$ and every collection $T$ of $t$ distinct projectivities, selected even after seeing $S$:
$$
 d(S;T,X):=\frac{|S\cap TX|}{tx}
 \le 3N^{-3/8}+60(1/x+1/t).                                      \tag{1}
$$
Here $TX=\bigcup_{g\in T}gX$. The denominator $tx$ counts representations, exactly as in the torus moment bound. The actual union can be smaller. The projectivities need not commute or belong to a common torus.

Indeed, for fixed $D=TX$ and positive integer $k$, counting the $k$-subsets of $S\cap D$ gives
$$
 \Pr(|S\cap D|\ge k)\le { |D|\choose k}\frac{ {s\choose k} }{ {N\choose k} }
 \le \left(\frac{e s xt}{Nk}\right)^k
$$
when $k\le\min(s,|D|)$, with zero probability otherwise. Take $k=\lceil3xtN^{-3/8}\rceil+8(x+3t+8)$. The last bound is at most $N^{-k/8}$. For fixed $x,t$ there are at most $N^{x+3t}$ choices since $|\mathrm{PGL}_2(\mathbb F_p)|=p(p^2-1)<N^3$. Summing over $x\le N$, $t\le N^3$ gives failure probability at most $N^{-4}$. Dividing $k$ by $xt$ yields (1), using $2\le x+t$ to absorb the rounding and constant terms.

## Comparison with the full moment estimate

Take any split or nonsplit torus of order $h=p\pm1$, templates $X,Y$ on its regular orbit, and nonempty translation sets $T,U$. Write $x=|X|,y=|Y|,t=|T|,u=|U|$, $m=\min(x,y)$ and $v=\max(t,u)$. Let $R=(tu)^2/\sum_g m_g^2$, where $m_g$ counts representations of $g$ as $a^{-1}b$ with $(a,b)\in T\times U$. Thus $R\le\min(h,tu)$. For an arbitrary integer $r\ge2$ put
$$
 F=\left(\frac{h(2r-1)!!\,m^{1-r}+(2r-2)\sqrt p}{R}\right)^{1/r}.
$$
The torus theorem supplies $\|P_{TX,UY}\|\le\sqrt{xtyu F}$. For a rectangle $A\times B$ with nonempty $A\subset S\cap TX$, $B\subset S\cap UY$, compression and Cauchy–Schwarz can therefore certify a bound below $|A||B|$ only if
$$
 d_A d_B>F,\qquad d_A=|A|/(xt),\qquad d_B=|B|/(yu).
$$
The two templates, shift sets, chart and moment order may all depend on the rectangle. [Torus moment estimate](paley-torus-translates.md)

For a set $S$ satisfying (1), this criterion fails uniformly as $p,m\to\infty$. If $F\ge1$ it fails immediately. For $F<1$ and $m>1$ the following quantitative bound holds:
$$
 \frac{d_A d_B}{F}\le 3\sqrt2\,p^{-1/8}
       +120\max\{1/\log m,\,p^{-1/4}\}.                           \tag{2}
$$
To see this, use the side with $v$ transformations in (1) and bound the other density by one. This gives $d_A d_B\le 3N^{-3/8}+120/\min(m,v)$. Since $R\le p+1$, one has $F\ge 2^{-1/2}p^{-1/4}$. If $m\le v$, then $R\le h$ and $(2r-1)!!\ge r!\ge(r/e)^r$ give $Fm\ge (r/e)m^{1/r}\ge\log m$. If $v<m$, then $R\le v^2$ and $F<1$ imply $v\ge p^{1/4}$, whence $Fv\ge p^{1/(2r)}v^{1-2/r}\ge p^{1/4}$. These inequalities are uniform even for a growing choice of $r$.

This also handles multiple charts and fractional covers. Suppose each rectangle in a cover is charged its torus operator bound times the two weight $\ell^2$ norms, and all its templates obey a common lower bound $m\to\infty$. For large $p$, the charge on each pair of supported weights $f_i,g_i$ satisfies
$$
 \sqrt{x_i t_i y_i u_i F_i}\,\|f_i\|_2\|g_i\|_2
 \ge \|f_i\|_1\|g_i\|_1.
$$
If $\sum_i |f_i(a)g_i(b)|\ge1$ on the target pairs, summing the charges costs at least the number of those pairs. This rules out a worst-case proof by covering arbitrary sets and adding these bounds. It imposes no constraint on which sets have large Paley discrepancy or on arguments exploiting signs between pieces.

## Short arcs, even with exact operator norms

For $0<\kappa<1/2$, let $H\le N^{1/2-\kappa}$ and $k=\lceil5/\kappa\rceil$. A consecutive orbit arc of length at most $H$ lies among the first $H$ iterates of some $x$ under some $g\in\mathrm{PGL}_2$. All chart conjugations, generator choices, common starts and wraparounds are already included. There are fewer than $N^4$ such candidates. The same counting argument gives
$$
 \Pr(\exists I:\ |S\cap I|\ge k)\le N^4{H\choose k}(s/N)^k
 \le N^{4-\kappa k}/k!\le N^{-1}.
$$
Thus one can choose $S$ satisfying both conclusions, including at every prescribed polynomial size $s\le\sqrt N$. It can also be chosen entirely in the affine chart, since the probability of containing infinity is $s/N$. Covering $c s$ sites then requires at least $cs/(k-1)$ independently placed arcs. On any pair of these arcs, even an exact norm for a parent rectangle with $x$ distinct rows and $y$ distinct columns is at least $\sqrt{\max(x,y)-1}$ by a single row or column. Since each side meets $S$ in at most $k-1$ sites, polynomial-size arc blocks cannot beat the trivial bound by this compression method, even with independently chosen charts on the two sides. [Short-arc theorem](paley-torus-generators.md)

For **whole parent arcs** the norm obstruction extends to all polynomial lengths. At any length $H\le N$, the same hypergeometric bound with $k_H=\lceil e^2sH/N+8\log N\rceil$ gives $\Pr(|S\cap I|\ge k_H)\le N^{-8}$ for each arc $I$ of length $H$. There are at most $N^5$ choices of length, projectivity and start. With probability $1-O(N^{-3})$, simultaneously for all $|I|=H\ge p^\tau$ with fixed $\tau>0$,
$$
 \frac{|S\cap I|}{\sqrt H}\le e^2\frac{s}{\sqrt N}+O(p^{-\tau/2}\log N).
$$
For $s\le\sqrt N$ the right side is bounded. On two whole parent arcs the product of the two intersection sizes is consequently $O(\sqrt{H_1H_2})$, whereas their squared operator norm is at least $\max(H_1,H_2)-1$. Even exact parent norms cannot deliver a power saving by adding the compressed estimates. If $s\le N^{1/2-\xi}$ for fixed $\xi>0$, the displayed ratio tends to zero by a power and the charges eventually exceed the trivial bound. This argument concerns what the cover can prove for arbitrary sets. It coexists with uniform cancellation on the parent arcs.

The verifier checks the intersection counts for 140,420 template configurations over $\mathbb F_5$. Exactly 13,464 of the 18,564 six-site subsets over $\mathbf P^1(\mathbb F_{17})$ occur as six-term projective arcs. At $p=2^{61}-1$, a uniform $2^{30}$-site set has probability less than $2^{-96}$ of meeting any $2^{20}$-term arc at 24 sites. Run `python3 -B scripts/probes/probe_paley_orbit_covering_barrier.py` to replay these controls and 248 exact comparisons of moment bounds. [Finite verifier](../../../scripts/probes/probe_paley_orbit_covering_barrier.py)
