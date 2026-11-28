# A two-endpoint certificate for the first quarter-rate list bound

For the first named field at length $n=2^{30}$ and rate $1/4$, every received word at every positive interleaving width is safe through **540,186,851 errors**. This raises the lower bound on the first list failure by 41,027 relative to the [resonant-collision certificate](quarter-first-resonant-collisions.md). The argument uses that certificate's quartic primary, local contact and tame splitting lemmas. It changes how the degree-five contact and cofactor rank are bounded.

## One cap across the full weight interval

Let $R=1/4$, $M=n-1000$ and $s=(n-e)/n$ at the proposed closed-ball radius $e$. Agreement exceeds the weaker $61/125$ required by the quartic primary. Recheck the small-degree and lower-weight tests at $s$. It remains to handle $5R\le w\le6R$. Use a single quotient of order $5{,}000{,}000$ and cap $2{,}525{,}000$. Write $Z(w)$ for its mean radial order lower bound and $K(w)=4w+5(w-R)-20R$ for the intersection budget. The verifier checks the corresponding large-group Bézout size condition.

Use the order tangent $4o-7\le o^2-o-1$ for integral $o$; the difference is $(o-2)(o-3)$. The column sum used in $Z$ is a sum of positive parts of affine functions, so $Z(w)$ is concave in $w$. Define $J$ as the larger of $K(w)+7-4Z(w)$ at the two endpoints. The same bound holds on the whole interval by convexity. The minimum of $sZ(w)-w$ also occurs at an endpoint. Its verified positive value has square greater than $(J+1/4)(R-s^2+(s-R)/1000)$. By the [exterior-word variance argument](quarter-first-resonant-collisions.md), fewer than 1,000 words are exterior to the factor. These two endpoint checks replace the previous interval and tangent search.

## Four-anchor rank cost

Set $F(q)=1-(1-q)^4$ and $\eta=R-s^2+(1+J)/M$. The [local residue-row estimate](eighth-list-resonant-collisions.md#cofactor-rank-and-the-named-comparison) needs $F(u)\le a+cu^2$ for low-length classes and $4u\le3a+cu^2$ for high-length classes, for $0\le u\le1$. Its price is $aJ+c\eta$.

For $0<x<1$, take $c(x)=F'(x)/(2x)$ and $a(x)=F(x)-xF'(x)/2$. Concavity gives $F(u)\le F(x)+F'(x)(u-x)$. The difference between $a(x)+c(x)u^2$ and this tangent is $c(x)(u-x)^2$. The high-length inequality follows by completing the square whenever $3a(x)c(x)\ge4$.

This gives a lower-bound check on the choice of prices. At $x_*=\sqrt{\eta/J}$, every feasible pair satisfies $aJ+c\eta\ge JF(x_*)$, by evaluating the low-length inequality at $x_*$. The tangent prices attain equality there when the high-length condition holds. The certificate brackets $x_*$ between adjacent millionths and uses the lower rational endpoint $q$ for the actual upper bound. The price $a(x)$ increases and $c(x)$ decreases, since $F'\ge0$ and $F''\le0$. The exact check $3a(q)c(q+10^{-6})\ge4$ covers the whole bracket. This optimality concerns the two pointwise class inequalities; no claim about optimal list geometry follows from it.

The bound $F'(s)\le2c(q)s$ puts the maximum for the actual true-hit mean $\mu\ge s$ at $s$. With the original sampling correction the rank is at most
$$
5+\left\lfloor n\left[F(s)+a(q)J+c(q)\eta+(6+10J)/M\right]\right\rfloor.
$$

| Errors | Rank upper bound | Nullity lower bound $k$ | First-integral degree upper bound $m$ | Tame split-fiber upper bound $62m+5$ |
| ---: | ---: | ---: | ---: | ---: |
| 540,186,851 | 1,073,482,836 | 257,988 | 4,161 | 257,987 |
| 540,186,852 | 1,073,482,857 | 257,967 | 4,162 | 258,049 |

At the first radius there would be at least $k+1=257{,}989$ split fibers, which exceeds the upper bound. The stationary Riccati and characteristic comparisons also hold. At the adjacent radius these bounds do not contradict each other; that radius remains undecided. These are written implications from the cited lemmas and executable exact rational checks.

```sh
python3 scripts/probes/probe_quarter_first_resonant_collisions.py
python3 scripts/probes/probe_quarter_four_anchor_dual.py
```
