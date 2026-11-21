# Prime-field Paley bounds from a small-doubling projective chart

Let $p$ be an odd prime and let $X\subseteq\mathbf P^1(\mathbb F_p)$ have size $n$. A projectivity may send one site to infinity. Write $Y=(\gamma X)\cap\mathbb F_p$, so $m=|Y|\in\{n-1,n\}$, and let $K=|Y+Y|/m$ for $m>0$. The following deductions use published prime-field character-sum estimates and the finite transfer proved below.

* **One third, four-site ranks.** Fix $\epsilon>0$ and $K_0$. If $n\ge p^{1/3+\epsilon}$ and some chart has $K\le K_0$, then for some $\tau=\tau(\epsilon,K_0)>0$ the proportion of singular four-site principal Paley minors modulo three is $1/4+O(p^{-\tau})$. The estimate holds for every such $X$. At the same sizes, all finite subsets $A,B\subseteq X$ satisfy $|S(A,B)|\le 9n^2p^{-\tau}+|A|+|B|$ after decreasing $\tau$ if necessary. Here $S(A,B)=\sum_{a\in A,b\in B}\chi(a-b)$. [Volostnov, Theorem 3](https://arxiv.org/pdf/1712.09355) · [Exact principal-minor identity](paley-four-site-rank.md)
* **Four ninths, arbitrary partner.** Under the same fixed-doubling condition, if $n,|B|\ge p^{4/9+\epsilon}$, the second set $B$ may be **any** subset of $\mathbb F_p$. For every finite $A\subseteq X$ one has $|S(A,B)|\le 9n|B|p^{-\tau}+|A|+|B|$ for some $\tau=\tau(\epsilon,K_0)>0$. Thus all such partners have a relative power saving when $A=X\cap\mathbb F_p$, or even when $|A|\ge n p^{-\tau/2}$. For example, $X$ may be the reciprocals of a prime-field interval that avoids zero. The chart assumption only involves the interval. [Chang, main result (2)](https://math.ucr.edu/~mcc/paper/131%20DL5.pdf)
* **Growing doubling, inverse conclusion.** For fixed $\epsilon>0$ there are constants $c_1,c_2>0$ such that if $n\ge p^{1/3+\epsilon}$ and the singular fraction differs from $1/4$ by more than $\exp(-c_2(\log p)^{1/5})$, then **every projective chart**, after dropping its pole, has $|Y+Y|/|Y|>\exp(c_1(\log p)^{1/5})$ for all sufficiently large $p$. This is an obstruction for the prescribed set and all its projective images. It permits large-doubling sets in every chart, for which the unrestricted rank estimate remains open. [Schoen–Shkredov, Theorem 3](https://arxiv.org/pdf/2004.01885)

## Dense subsets suffice despite arbitrary vertex signs

Suppose $Y,Z$ are finite templates, and $|\sum_{x\in U,b\in V}W(x,b)|\le H$ whenever $U\subseteq Y$, $V\subseteq Z$, $2|U|\ge |Y|$ and $2|V|\ge |Z|$. Every ternary weight $u:Y\to\{-1,0,1\}$ is a signed sum of at most three indicators of sets of size at least $|Y|/2$. Write $P=\{u=1\}$, $N=\{u=-1\}$. In $u=\mathbf1_P-\mathbf1_N$, replace each indicator of a small set by $\mathbf1_Y-\mathbf1_{Y\setminus P}$ or $\mathbf1_Y-\mathbf1_{Y\setminus N}$. If both sets are small the two copies of $\mathbf1_Y$ cancel. Applying this argument in both variables proves
$$
 \left|\sum_{x\in Y,b\in Z}u(x)v(b)W(x,b)\right|\le 9H .
$$
This uses only the bound for sets containing at least half of their own templates, including when the original supports are much smaller. Lean proves both the weighted rectangle estimate and the following energy consequence over the integers. A real upper bound $H$ for integer sums can first be rounded down. [Lean transfer](../../../ArkLib/Research/ProximityGap/Frontier/PaleyDenseCutTransfer.lean)

For $W(x,b)=\chi(x-b)$ fix two anchors $y\in Y,t\in Z$ in the signed four-cycle expansion of $E(Y,Z)$. The remaining sum is the weighted rectangle with $u(x)=W(x,t)$ and $v(b)=W(y,b)$, times $W(y,t)$. Consequently
$$
 E(Y,Z)\le 9H |Y||Z|.
$$
The projective Paley matrix transforms by a global sign and one sign per vertex. Thus each actual subrectangle of the original chart has weighted finite contribution bounded by $9H$ in the transformed chart. The terms incident to infinity contribute at most $|A|+|B|$. Likewise projective four-cycle energy is unchanged before dropping infinity. In the principal case adding back one site increases energy by at most $4n^3$, since only ordered quadruples using the site can change. [Projective signs, rank identity and normalization](paley-four-site-rank.md)

## Applying the three character estimates

For every half-size subset $U\subseteq Y$,
$$
 |U+U|\le |Y+Y|=Km\le 2K|U|.
$$
Negating a template preserves its doubling constant. Thus each difference sum required above is a sum of the kind in the cited results, using $U$ and $-V$. For all sufficiently large $p$, each half of a template of size at least $p^{\theta+\epsilon}-1$ has size strictly greater than $p^{\theta+\epsilon/2}$.

At $\theta=1/3$, apply Volostnov's Theorem 3 to $U,-V\subseteq Y,-Y$. Both doubling constants are bounded by $3K_0$, allowing the theorem's strict inequalities. Uniformly $H\le m^2p^{-\tau_0}$ for some fixed $\tau_0>0$. It follows that $E(X,X)\le9m^4p^{-\tau_0}+4n^3$. The exact relation $32\chi(-1)(N(X)-\binom n4/4)=E(X,X)-n(n-1)(2n-3)$ gives the first rank bound for either sign of $\chi(-1)$. The rectangle estimate follows directly from the two ternary weights and has no fourth-root loss. The same proof allows two different templates in a common chart when both have bounded doubling and the size threshold holds for each.

At $\theta=4/9$, take $Z=(\gamma B)\cap\mathbb F_p$. Chang's result requires small doubling on just one of the two summation sets. Every half of $Y$ satisfies it, and all halves of $Z$ satisfy the size hypothesis. The resulting $H\le m|Z|p^{-\tau_0}$ applies to arbitrary target sets and all the original subrectangles asserted above. The preliminary loss of one point on either side is included in the stated pole correction.

For growing $K$, Schoen and Shkredov assume $|U|>p^d$, $|V|>p^{1/3+d}$, $|U||V|^2>p^{1+d}$, $|U+U|<K'|U|$, $|V+V|<L'|V|$, $L'\le p^{d/2}$ and $(\log K')^5\ll d^4\log p$. For $n\ge p^{1/3+\epsilon}$ take $d=\epsilon/2$ and $K'=L'=3K$. All three size assumptions hold for all halves of $Y$. For $K\le\exp(c_1(\log p)^{1/5})$ with sufficiently small $c_1(\epsilon)>0$, the two logarithmic conditions hold. Their bound gives
$$
 H\ll m^2\exp\!\left[-c\left(\frac{d^4\log p}{(\log(3K))^2}\right)^{1/3}\right]
 \ll m^2\exp[-c_3(\epsilon)(\log p)^{1/5}] .
$$
Applying the finite energy estimate and the same density normalization absorbs the pole and diagonal terms. Reducing the exponent constant absorbs fixed multiplicative constants. Taking the contrapositive gives the all-charts inverse conclusion. The prime-specific inputs here are the published additive-doubling estimates. The transfer to the ternary four-site statistic and to arbitrary projective placements uses only signs, subsets and finite sums.
