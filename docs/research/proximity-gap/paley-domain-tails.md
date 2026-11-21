# Paley discrepancy on uniformly sampled coordinate domains

Let $p$ be an odd prime, let $1\le m\le p$, and extend the quadratic character $\chi$ by $\chi(0)=0$. For $A\subseteq\mathbb F_p$ of size $m$, write $W_A(b)=\sum_{a\in A}\chi(a+b)$ and $S(A,B)=\sum_{b\in B}W_A(b)$. Negating $B$ gives the difference convention of the Paley graph. For $2\le m\le(p+1)/2$, the signed interpolation determinants in the prize library recover each $W_A(b)$ exactly. Here we study which shift profiles occur when the evaluation domain varies. The classical conjecture requires a uniform power saving for every pair with both sizes above $p^\epsilon$. [Signed determinant identity](../../../ArkLib/Research/ProximityGap/Frontier/PaleySignedFactorization.lean) · [Kim, Yip and Yoo, §2.4](https://arxiv.org/html/2309.09124v3#S2.SS4)

## A power saving for almost every domain, simultaneously over all second sets

Choose $A$ uniformly from the $m$-subsets of $\mathbb F_p$. For every $T\ge0$,

$$
\Pr_A\!\left(\max_{|B|\ge m}\frac{|S(A,B)|}{|B|}\ge T\right)
\le \frac{2p}{m}\exp\left(-\frac{T^2}{2m}\right).
$$

For fixed $b$, the symbols across the field consist of $d=(p-1)/2$ ones, $d$ minus ones and one zero. The sum of $\exp(\theta W_A(b))$ over $m$-subsets is the coefficient of $X^m$ in $(1+X)(1+2\cosh(\theta) X+X^2)^d$. Coefficientwise this polynomial is bounded by $(1+\cosh(\theta) X)^p$. Divide by $\binom pm$ to bound the expectation by $\cosh(\theta)^m\le\exp(m\theta^2/2)$, where the last inequality follows by comparing the power series.

Take a maximizing $B$ and choose the sign of its sum. Jensen's inequality bounds the exponential of $\theta |S(A,B)|/|B|$ by the average of the exponentials over $B$. For $\theta\ge0$ this is at most $m^{-1}\sum_b(e^{\theta W_A(b)}+e^{-\theta W_A(b)})$. Markov's inequality and $\theta=T/m$ give the claim. In particular if $m\ge p^\epsilon$ and $0<\delta<\epsilon/2$, the fraction of domains admitting any partner of size at least $m$ with relative discrepancy at least $p^{-\delta}$ is at most $(2p/m)\exp(-p^{\epsilon-2\delta}/2)$.

## An unavoidable logarithmic factor for a uniform bound

Fix $0<\epsilon\le1/2$ and $0<c<\sqrt{2(1-\epsilon)}$. For every sufficiently large prime $p$ there are sets of equal size $m=\lfloor p^\epsilon\rfloor+1$ with

$$
S(A,B)\ge c\,m^{3/2}\sqrt{\log p}.
$$

In particular a uniform bound $|S(A,B)|\le C_\epsilon p^{-\delta}|A||B|$ requires $\delta<\epsilon/2$ in this range. This obstruction concerns the endpoint exponent. Positive smaller exponents remain possible.

For fixed $b$, consider domains omitting the unique zero symbol. With $j$ positive sites and $m-j$ negative sites, $W_A(b)=2j-m$. The probability of this event is
$$
\binom mj\frac{(d)_j(d)_{m-j}}{(p)_m}\ge
\binom mj2^{-m}\left(1-\frac{2m+1}{p}\right)^m,
$$
where $(x)_k=x(x-1)\cdots(x-k+1)$. The final factor is bounded away from zero since $m^2/p$ is bounded. Sum over the integers $j$ in the interval starting at $(m+c\sqrt{m\log p})/2$ of length $\sqrt{m/\log p}$. There are $\asymp\sqrt{m/\log p}$ such integers. Uniformly there, writing $w=2j-m$, Stirling's formula and the Taylor expansion of binary entropy at $1/2$ give
$$
\log\big(2^{-m}\tbinom mj\big)
=-\tfrac12\log m-\frac{w^2}{2m}+O(1+w^4/m^3).
$$
The quartic term tends to zero and $w^2/(2m)=c^2\log p/2+O(1)$. The positive tail probability is therefore at least a constant times $p^{-c^2/2}/\sqrt{\log p}$. By linearity of expectation some domain has at least $m$ shifts in this tail since $1-c^2/2>\epsilon$. Choosing any $m$ of them proves the claim. [Stirling expansion](https://dlmf.nist.gov/5.11)

## Lower bound for each supplied domain

For every nonempty supplied $A$ with $4m^2\le p$ and every integer $t\ge0$ satisfying $2t^2\le m$, there are $m$ shifts on which all row sums have the same sign and magnitude at least $t+1$. Indeed $\sum_b W_A(b)^2=m(p-m)$ and $|W_A(b)|\le m$. If each sign had at most $m-1$ shifts above the threshold, then $2\sum_b W_A(b)^2\le pm+2m^2(2m-2)$, contradicting $4m^2\le p$. This gives $|S(A,B)|\ge m(t+1)$ for every first set in the indicated range. [Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleyWorstShiftFloor.lean)

## Exact finite construction

The single-row probability $P_t=\Pr(W_A(b)\ge t)$ is
$$
\binom pm^{-1}\!\sum_{z=0}^1\ \sum_{j+k=m-z,\ j-k\ge t}\binom dj\binom dk.
$$
[Lean checks the exact row law and its sum over shifts](../../../ArkLib/Research/ProximityGap/Frontier/PaleyRowSampling.lean). Replacing $j-k$ by $|j-k|$ in the condition gives the two-sided probability. An expected count $pP_t\ge m$ produces a domain with $m$ positive shifts at height $t$. An expected two-sided count below one produces a domain with every magnitude below $t$. Both conclusions have deterministic constructions. At each step choose the next element maximizing or minimizing the mean count of bad shifts among completions. All candidates have the same number of completions. Counting each completed domain once per unchosen element in it gives the conditional averaging identity.

The integer probe verifies this identity at every extension and compares the exact tails with exhaustive enumeration at $p=3,5,7,11$. At $p=257$, $m=16$, it constructs one domain with maximum magnitude 10 across all 257 shifts and a different domain with 16 positive shifts of magnitude at least 6. For the latter the selected rectangle has signed sum 122 out of 256. Run `python3 -O scripts/probes/probe_paley_domain_tails.py` to print the actual sets. [Exact probe](../../../scripts/probes/probe_paley_domain_tails.py)

## A single genus suffices at each sparse scale

Fix $0<\epsilon\le1/2$ and $m=\lfloor p^\epsilon\rfloor+1$. The existence of a uniform power saving on all $m$-by-$m$ rectangles is equivalent to the following assertion. For some **fixed** integer $r\ge2$ with $(r+1)\epsilon>1$ and some $\eta>0$, every sufficiently large prime and every $m$-subset $A$ satisfy
$$
\frac{1}{\binom m{2r}}\sum_{\substack{I\subseteq A\\ |I|=2r}}
  \sum_{b\in\mathbb F_p}\chi\!\left(\prod_{u\in I}(b+u)\right)
  \le m p^{-\eta}.
$$

Only subsets with **distinct** branch points occur, and the inequality is one-sided. Each inner sum equals $-1$ minus the Frobenius trace of the smooth projective curve $y^2=\prod_{u\in I}(x+u)$ of genus $r-1$. Counting its affine points gives $p$ plus the character sum, and the monic even-degree model adds two rational points at infinity. Thus a lower bound on the average trace for this one genus, uniform over puncturings $A$, would suffice. A comparable bound after averaging over $A$ leaves the exceptional domains above.

To prove the equivalence, let $M=\sum_b |W_A(b)|^{2r}$ and let $D$ be the double sum in the display before dividing by $\binom m{2r}$. There are constants depending only on $r$ such that
$$
\tfrac12 M-C_r p m^r \ \le\ (2r)!D\ \le\ \tfrac32 M+C_r p m^r .
$$
At each $b$, multiply the elementary symmetric polynomial of degree $2r$ in $x_u=\chi(b+u)$ by $(2r)!$. It counts products over ordered tuples of distinct sites. Inclusion-exclusion on equal pairs expresses it as $W^{2r}$ plus an integer linear combination of products over nondiscrete partitions of the positions, where $W=W_A(b)$. An odd block gives $\sum_u x_u^j=W$ and an even block gives $\sum_u x_u^j\le m$. If a partition has $2r-2j$ odd blocks, it has at most $j$ even blocks. Every nondiscrete partition has $1\le j\le r$. The total error is at most $C'_r\sum_{j=1}^r m^j|W|^{2r-2j}$. For $|W|\ge K_r\sqrt m$ choose $K_r$ large enough that this is at most $|W|^{2r}/2$. For the remaining $W$ the error is $O_r(m^r)$. Sum over $b$ to obtain the inequalities.

If the displayed branch-point estimate holds, these inequalities give
$$
M/m^{2r+1}=O_r(p^{-\eta}+p/m^{r+1}).
$$
Hölder gives $|S(A,B)|/m^2\le(M/m^{2r+1})^{1/(2r)}$ for $|B|=m$, so $(r+1)\epsilon>1$ gives a power saving.

Conversely, assume every such rectangle has $|S(A,B)|\le m^2 p^{-\delta}$ for some $\delta>0$ and all sufficiently large $p$. The sum $T$ of the $m$ largest absolute row sums satisfies $T\le3m^2p^{-\delta}$ by the finite superset-sampling bound when $m\le p/2$. Each of these $m$ terms is at most $m$ and every remaining term is at most $T/m$. The exact second moment gives
$$
 M\le m^{2r-1}T+(T/m)^{2r-2}p m .
$$
Choose a fixed $r$ so that $(r+1)\epsilon>1$ and $(2r-2)\delta>1-2\epsilon$. Then $M/m^{2r+1}$ decays by a power of $p$. The upper estimate for $D$, together with $\binom m{2r}\asymp_r m^{2r}$, gives the displayed branch-point estimate after decreasing the exponent to absorb constants. The remaining mathematical obligation is to prove that one-sided trace bound for every prescribed $A$. [Finite comparison with absolute shifts](../../../ArkLib/Research/ProximityGap/Frontier/PaleyAbsoluteSlice.lean)

At genus one the comparison has an explicit identity. Let $D_4$ denote the double sum above for $r=2$. Then for every $m$ and odd prime,
$$
\sum_b W_A(b)^4=24D_4+p(3m^2-2m)-6m^3+14m^2-9m
   -6\sum_{a\in A} W_A(-a)^2.
$$
For a fixed row let $n_b=m-\mathbf1_{-b\in A}$. Its fourth elementary symmetric sum satisfies $24e_4=W^4-(6n_b-8)W^2+3n_b^2-6n_b$ by expanding into partitions of four positions. Summing gives the identity using $\sum_b W_A(b)^2=m(p-m)$. Consequently a power saving in the one-sided average elliptic sum relative to $m$ suffices as soon as $m\ge p^{1/3+\gamma}$ for fixed $\gamma>0$. The probe enumerates affine points on each individual curve and verifies the fourth-moment formula on every nonempty domain for $p=3,5,7,11$. [Exact check](../../../scripts/probes/probe_paley_domain_tails.py)
