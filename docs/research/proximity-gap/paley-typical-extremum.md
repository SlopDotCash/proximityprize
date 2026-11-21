# The typical largest Paley rectangle from a random first set

Fix $0<\epsilon<1$, let $p$ tend to infinity through odd primes and set $m=\lfloor p^\epsilon\rfloor+1$. Choose an $m$-subset $A$ uniformly from $\mathbb F_p$. Write $W_b=\sum_{a\in A}\chi(a+b)$ with $\chi(0)=0$ and $S(A,B)=\sum_{b\in B}W_b$. For each sign $\sigma\in\{-1,1\}$,
$$
 \max_{|B|\ge m}\frac{\sigma S(A,B)}{|B|\sqrt{m\log p}}
 \ \xrightarrow{\ \mathrm{prob.}\ }\ \sqrt{2(1-\epsilon)} .
$$
The two conclusions hold simultaneously. Thus the positive and negative extremes have the same leading constant, including above square-root size. The maximum is attained by taking the $m$ largest values of $\sigma W_b$. Negating the second set gives the difference convention used for the Paley graph when $p\equiv1\pmod4$. The proof concerns the distribution over first sets and uses the [random-domain upper bound](paley-domain-tails.md).

## Relative tail probabilities for two prescribed shifts

Let $Q_m(t)=\Pr(\xi_1+\cdots+\xi_m\ge t)$ for independent fair signs. For $h=1,2$, distinct $b_1,\ldots,b_h$, signs $\sigma_i$ and thresholds $0\le t_i\le C\sqrt{m\log p}$ with $C$ fixed, we claim
$$
 \Pr_A(\sigma_i W_{b_i}\ge t_i\ \text{for every }i)
   =(1+o(1))\prod_{i=1}^{h} Q_m(t_i).
$$
The error is uniform in the shifts, signs and thresholds. Both the exclusion and the inclusion of sites at which a character vanishes enter the proof.

**Sign populations.** Remove the $h$ sites $-b_i$. The remaining points have $d=2^h$ possible sign patterns with populations $N_s=p/d+O(1)$. For one shift the two populations are $(p-1)/2$. For two distinct shifts $b,c$ and signs $s,t$, the population is exactly
$$
 N_{s,t}=\frac{p-2-st-s\chi(b-c)-t\chi(c-b)}4 .
$$
Indeed $\sum_x\chi(x+b)\chi(x+c)=-1$ by the bijection $x\mapsto(x+b)/(x+c)$ away from $-c$. Sum $(1+s\chi(x+b))(1+t\chi(x+c))/4$ and subtract the two exceptional sites explicitly. The two character values in the formula agree for $p\equiv1\pmod4$ and are opposites for $p\equiv3\pmod4$.

**Comparison of ordered samples.** Sample $m$ distinct field elements in order. A particular ordered sequence of nonzero sign patterns with counts $k_s$ has probability $\prod_s(N_s)_{k_s}/(p)_m$, where $(N)_k$ is the falling factorial. Its likelihood ratio to independent uniform choices among the $d$ patterns is
$$
 R(k)=\frac{d^m\prod_s(N_s)_{k_s}}{(p)_m}.
$$
Uniformly in all counts, $R(k)\le 1+o(1)$. To see this replace each $N_s$ by $D=\max_s N_s$. The product $\prod_s(D)_{k_s}$ is maximized when the counts differ by at most one, since moving one count from a larger group to a smaller one can only increase it. The balanced ratio is
$$
 \prod_{i=0}^{m-1}\frac{d(D-\lfloor i/d\rfloor)}{p-i}
 =\exp\big(O(m/(p-m))\big)
$$
because $dD=p+O(1)$. For a lower bound replace the populations by $D=\min_s N_s$. The same balanced ratio is $1+o(1)$. If $|k_s-m/d|\le K\sqrt{m\log p}$ for every $s$, use $O_d(K\sqrt{m\log p}+1)$ single transfers from balanced counts to reach $k$, moving each count monotonically. A transfer that increments $a$ and decrements $b$ multiplies the product by $(D-a)/(D-b+1)$. Its logarithm has absolute value $O_{d,K}((\sqrt{m\log p}+1)/(p-m))$. The total loss is $\exp(-O_{d,K}(m\log p/(p-m)))=1-o(1)$. Thus $R(k)=1+o(1)$ uniformly throughout this central range.

Under independent uniform patterns, the probability of leaving the central range is at most $2d p^{-2K^2}$. Indeed each cell count is binomial, and the log moment generating function of a centered Bernoulli variable has second derivative at most $1/4$ (a tilted Bernoulli variance). Exponential Markov bounds give the claim. On the other hand, uniformly for $0\le t\le C\sqrt{m\log p}$,
$$
 Q_m(t)\ \gg_C\ \frac{p^{-C^2/2}}{\sqrt{\log p}}.
$$
This follows by summing fair-binomial probabilities for admissible sums between $t$ and $t+2\sqrt{m/\log p}$. On this interval Stirling's formula gives mass $\gg_C m^{-1/2}\exp(-t^2/(2m))$ at each admissible sum, since $(\log p)^2/m=o(1)$. Choose $K$ so that $2K^2>hC^2/2$. The discarded probability is then $o(\prod_i Q_m(t_i))$. Independence of the $h$ signs in each uniform pattern, together with the bounds on $R(k)$, proves the claimed relative estimate for the event that also omits all exceptional sites.

**Restoring the zero sites.** Prescribe a nonempty subset $J$ of the exceptional sites as exactly those selected, and write $j=|J|\le h$. This has probability $O((m/p)^j)$. Conditional on that choice, the remaining $m-j$ sites are uniform in the population of size $p-h$ with the same cell counts. The preceding global upper likelihood bound applies with that denominator and sample size. Each signed row receives a deterministic contribution $e_i$ from $J$ with $|e_i|\le j$. For independent fair patterns, append $j$ patterns favorable in every signed row. This gives
$$
 \prod_i Q_{m-j}(t_i-e_i)\le 2^{hj}\prod_i Q_m(t_i).
$$
Summing the conditional upper bounds over nonempty $J$ costs $O(m/p)\prod_i Q_m(t_i)$. This proves the uniform relative estimate for the actual character sums, also for opposite choices of the two row signs.

## Counting available shifts

Fix $0<c<\sqrt{2(1-\epsilon)}$ and let $t=c\sqrt{m\log p}$. For either sign put $X=\#\{b:\sigma W_b\ge t\}$. The one-shift estimate gives $\mathbb E X=(1+o(1))pQ_m(t)\gg_c p^{1-c^2/2}/\sqrt{\log p}\gg m$. The two-shift estimate gives $\mathbb E[X(X-1)]=(1+o(1))p(p-1)Q_m(t)^2$, so $\operatorname{Var}X=o((\mathbb E X)^2)$. With probability tending to one there are at least $m$ eligible shifts for each sign. Choosing any $m$ proves the required lower bound.

For $c>\sqrt{2(1-\epsilon)}$, the probability that any $B$ of size at least $m$ has $|S(A,B)|/|B|\ge c\sqrt{m\log p}$ is at most $(2p/m)p^{-c^2/2}=o(1)$ by the exponential bound. This proves convergence from both sides. A uniform power saving for every prescribed $A$ remains a separate quantifier.
