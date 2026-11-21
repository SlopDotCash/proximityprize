# Exact MCA threshold at rate one sixteenth

Let $n=2^{30}=1,073,741,824$, $k=2^{26}=67,108,864$ and $d=k-1$. Let $p$ be prime, $n\mid p-1$, and evaluate all degree-at-most-$d$ polynomials on the subgroup $H$ of order $n$ in $\mathbb F_p$. Denote the resulting Reed–Solomon code by $C$. Write $B=\lfloor p/2^{128}\rfloor$ for the number of bad scalars permitted by the target probability. For $1\le B\le 1,295,252,617$, the first bad integer error allowance is

| Scalar budget $B$ | First bad error $j$ |
| --- | ---: |
| $1\le B\le503,316,479$ | $B$ |
| $503,316,480\le B\le1,006,632,961$ | $503,316,480$ |
| $1,006,632,962\le B\le1,295,252,617$ | $\lfloor B/2\rfloor$ |

The good real radii are exactly $0\le\delta<j/n$. Thus $j/n$ is the supremum, and $(j-1)/n$ is the largest good Hamming-grid radius. These conclusions also hold for every fixed positive interleaving width. The exact Lean statements are **rateSixteenth_threshold_curve**, **rateSixteenth_good_iff**, **rateSixteenth_interleaved_threshold_curve**, and **rateSixteenth_interleaved_good_iff**. [Threshold theorems](../../../ArkLib/Research/ProximityGap/Frontier/_TwoLineSpikeThreshold.lean)

## The bad event

Fix two received words $u_0,u_1:H\to\mathbb F_p$ and an integer error allowance $e$, with $t=n-e$. A scalar $\gamma$ is bad if there is a set $T$ of at least $t$ positions such that $u_0+\gamma u_1$ agrees with a codeword throughout $T$, and no pair of codewords agrees with $(u_0,u_1)$ throughout that same $T$. A joint explanation elsewhere is allowed. Let $b(e)$ be the largest number of distinct bad scalars over all pairs of received words. Then $\varepsilon_{\rm mca}(C,e/n)=b(e)/p$. This is Definition 4.3 in Arnon, Boneh and Fenzi. [ABF26, §4.1](https://eprint.iacr.org/2026/680) · [Lean definition](../../../ArkLib/Extensions/Data/CodingTheory/ProximityGap/Errors.lean)

Put $e_0=(n-k)/2=503,316,480$ and $E=647,626,307$. On the stated fields the exact counts are
$$
 b(e)=
 \begin{cases}
 e+1,&0\le e< e_0,\\
 2e+2,&e_0\le e\le E.
 \end{cases}
$$
At $E+1$ we use only the lower bound $2(E+1)+2$. The first jump occurs at the last uniquely decodable integer error since the minimum distance is $n-k+1$.

## Counting the selected polynomials

Choose one witness polynomial $q_\gamma$ per bad scalar and write $A_\gamma$ for its full agreement set. Any two selected points $(\gamma,q_\gamma)$ determine a unique affine line of the form $q_\gamma=P+\gamma R$. Its *core* consists of coordinates where $(u_0,u_1)=(P,R)$. The intersection of the full agreement sets of two of its points is exactly the core, since subtracting their equations recovers $R$. Consequently, agreements off the core are disjoint for different points on the line. Each point has at least one such agreement by witness-set badness. Writing $z$ for the core size and $L$ for the number of points on the line gives
$$
 z+L\max(1,t-z)\le n,\qquad L\le e+1.
$$
An off-line point has at most $d$ agreements on the core, by the root bound for $q_\gamma-P-\gamma R$. The same argument bounds the common agreements of a noncollinear triple by $d$. Cores of distinct determined lines overlap in at most $d$ positions because at least one of their two defining polynomials differs. [Core and packing lemmas](../../../ArkLib/Research/ProximityGap/Frontier/_TwoLargeCoreCount.lean)

For $M\ge3$ selected points let $m_x$ count agreements at coordinate $x$, and let $W$ be the mean number of common agreements of a triple. With $f(v)=v(v-1)(v-2)$, double counting gives $W=\sum_x f(m_x)/f(M)$. For $2\le v\le Mt/n$, the tangent inequality
$$
 f(y)-f(v)-f'(v)(y-v)=(y-v)^2(y+2v-3)\ge0\quad(y\ge0)
$$
and $\sum_xm_x\ge Mt$ give $W\ge nf(v)/f(M)$. If all lines have at most $L$ points, each pair admits at most $L-2$ collinear completions. The fraction of collinear triples is therefore at most $(L-2)/(M-2)$. [Triple-moment lower bound](../../../ArkLib/Research/ProximityGap/Frontier/_ThirdMomentJensenGeneral.lean) · [Triple-moment upper bound](../../../ArkLib/Research/ProximityGap/Frontier/_ThirdMomentUpperLineCap.lean)

For $e<e_0$, suppose there are $M=e+2$ bad points. When $3e<n-d$, any three share more than $d$ positions, forcing collinearity and contradicting the line cap. Otherwise $e>5n/16$. A line with $2z>2n-3t+4d$ forces all outside points onto a second line. Indeed, any three of them share at least $3(t-d)-2(n-z)>d$ positions outside the core. If there were no such large core, every core would have $z\le n/4+2d$, since $t\ge n/2$. Five points on a line would then require $5t-4z>n$. With at most four points per line the triple average is at most $d+2(n/4+d)/e<d+2$. Its lower bound at $v=M/2$ is $n(M-4)/(8(M-1))>n/8-6/5$, a contradiction.

Thus two lines cover the points. Each determined line has an outside point because $M>e+1$, so $t\le n-z+d$. Hence $t-z\ge n-2e-d\ge3$. Packing now gives $L\le1+\lfloor e/3\rfloor$. Two such lines contain at most $e+1$ points for $e\ge1$, the required contradiction. [Lean upper bound before the jump](../../../ArkLib/Research/ProximityGap/Frontier/_TwoLinePreUnique.lean)

For $e_0\le e\le E$, suppose instead there are $2e+3$ bad points. Every subfamily of $M\ge e+2$ points contains a line with core of size at least $t-c$, where $c=1,626,881$. Otherwise packing gives $L\le1+e/(c+1)$ throughout the subfamily. Since $M-2\ge e$, the collinear triple fraction is at most $660/n$. Collinear triples have weight equal to their core size and thus at most $t$. The upper bound becomes
$$
 W\le d+660t/n\le d+351=67,109,214.
$$
For the lower bound take $v=M\cdot426115517/n$ and $r=39685099/10^8$. Throughout the range $426115517\le t\le570425344$, $M\ge503316482$, and $v-2\ge rM$. Thus $W\ge nf(v)/f(M)\ge nr^3>67,109,214$. This proves the large-core assertion. Remove its line, losing at most $e+1$ points, and apply the assertion again to the remaining points. An outsider to both lines can agree on at most $2d$ core positions and at most $n-2(t-c)+d$ positions off the cores. Their sum is strictly below $t$, since $3t-n-3d-2c\ge24,376$. The two lines therefore cover the whole family, but their combined occupancy is at most $2e+2$. [Moment forcing](../../../ArkLib/Research/ProximityGap/Frontier/_TwoCoreMomentForcing.lean) · [Production assembly](../../../ArkLib/Research/ProximityGap/Frontier/_TwoCoreMomentApplication.lean)

## Attaining the counts

For $e<e_0$, place $(0,0)$ on $t-1$ coordinates and $(-x,1)$ at each remaining $x$. Each such $x$ yields the distinct bad scalar $\gamma=x$. The common core and $x$ witness folded agreement with zero. The core has at least $k$ coordinates and forces both explaining polynomials to vanish, which fails at $x$.

For $e_0\le e<n/2$, take two sets of size $t-1$ covering $H$. Their intersection $I$ has size $n-2e-2$. Put $Z(X)=\prod_{x\in I}(X-x)$ and assign the rows $(0,0)$ on the first set and $(XZ,Z)$ on the second. The assignments coincide on $I$, and $\deg(XZ)\le d$. Every point $x$ belonging to only one set gives the bad scalar $-x$, witnessed by the opposite set and $x$. Interpolation on that set forces the explaining pair, which fails at $x$. There are $2e+2$ such points.

For $n/2\le e\le E+1$, use two disjoint sets of size $t-1$ carrying $(0,0)$ and $(X,1)$, respectively. There are $h=n-2t+2$ further positions. At each such position $x$, choose distinct scalars $\alpha_x,\beta_x$ outside $-H$, all $2h$ labels distinct. The budget hypothesis gives $p\ge2^{128}$, so $p-n\ge2h$. Give $x$ the pair
$$
 b_x=(x+\beta_x)/(\beta_x-\alpha_x),\qquad a_x=-\alpha_x b_x .
$$
Then $b_x\notin\{0,1\}$. The fold matches the zero polynomial at $\alpha_x$ and the polynomial $X+\beta_x$ at $\beta_x$. Each ordinary core position contributes its scalar $-x$ against the opposite core. As before, each witnessing core pins down the explaining pair, which fails at the added position. The total is $2(t-1)+2h=2e+2$. [Matching constructions](../../../ArkLib/Data/CodingTheory/ProximityGap/PackingEnvelope.lean) · [Field-size verification](../../../ArkLib/Research/ProximityGap/Frontier/_PackingBudgetFirstJump.lean)

## The security threshold and its scope

An integer count passes precisely when $b(e)\le B$. On the first branch $b(B-1)=B<b(B)$. At the jump the adjacent counts are $e_0$ and $2e_0+2$. Above the plateau put $j=\lfloor B/2\rfloor$. Then $b(j-1)=2j\le B$, and the construction gives $b(j)\ge2j+2>B$, including $j=E+1$. The agreement condition depends on $\lfloor n\delta\rfloor$, and the bad event increases with $\delta$, yielding the table. Exact invariance of MCA under positive interleaving is ABF26 Theorem 4.7, due to Jo. The list-size challenge asks for another quantity. [Jo's interleaving theorem](https://eprint.iacr.org/2026/891) · [Lean interleaving theorem](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)

The first branch also follows at these parameters from BCHKS25 Theorem 1.3, ABF26 Lemma 4.6 and its Theorem 4.8. BCHKS25 measures minimum distance using maximum polynomial degree $d$. At the final pre-jump point $e=503,316,479$, the required number of close scalars rounds up to $357,913,944$, already below $e+2$. BCHKS25 Remark 2.5 explicitly gives the singleton lower construction. The incidence proof above independently recovers that branch and joins it to the exact two-line count and the threshold table. [BCHKS25, Theorem 1.3 and Remark 2.5](https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf)

## Other block lengths

A second argument gives an exact threshold for arbitrary block lengths in a narrower budget range. Let $n=16k≥3398$, let $Q≥2$ be an integer, and put $B=⌊p/Q⌋$. Suppose the prime field has an element of order $n$, $n≤B$, and $14(B-n)≤n$. At target error $1/Q$ the supremum is $⌊B/2⌋/n$. To see the upper bound on bad scalars at the preceding step, extend the evaluation domain to length $N=2⌊B/2⌋$. Multiply both received rows and each witness polynomial by the product of the new linear factors, assigning zero to the new coordinates. A joint explanation there is divisible by that product on both rows and hence restricts to a joint explanation on the original witness. Thus every originally bad scalar remains bad. The enlarged dimension satisfies $8(k+N-n)≤N$, so the rate-one-eighth bound limits the count to $N≤B$. At the next error the overlap construction supplies $N+2>B$ bad scalars. [General-length theorem](../../../ArkLib/Research/ProximityGap/Frontier/_ShortenedDomainPackingPin.lean) · [Locator extension](../../../ArkLib/Research/ProximityGap/Frontier/_RSLocatorExtension.lean)

At the second designated prime, $B=2n$ lies above this table. The two-line upper bound and a separate three-line construction enclose its supremum in $[647626308/n,\;715827882/n]$. The exact value there remains open. [Second-prime bracket](../../../ArkLib/Research/ProximityGap/Frontier/_ThreeCoreSecondPrimeBracket.lean)
