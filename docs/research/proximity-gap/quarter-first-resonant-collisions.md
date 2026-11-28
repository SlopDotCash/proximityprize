# A resonant contact bound on the first-prime quarter-rate list

At length $n=2^{30}$, every closed ball through **540,145,824 errors** in the first named quarter-rate code has at most $n$ words, for every injective grid and every positive interleaving width. First failure is therefore at least **540,145,825**, raising the previous lower bound by 805,306. This leaves the exact threshold open. [Previous first-prime bound](quarter-list-darboux-cofactors.md) · [Exact verifier](../../../scripts/probes/probe_quarter_first_resonant_collisions.py)

Set $d=n/4-1$, $R=1/4$, and $s=9939/20000$. Scalarize an oversized list. Its sections each meet the weaker $61/125$ agreement test used for the quartic primary. That primary and its product exclusions use no target list budget, and their characteristic comparisons hold on the first named field. With $L=\lfloor n/40\rfloor$ and primary degree cap 21, $4L+21<n$. Thus some factor is large. The product tests force a single large irreducible factor $A+B V$ and the order-3000 comparison forces its integral weight to be at most $6d-2$. At least $M_0=n-4L-21$ of the words solve this equation. [Quartic primary, derivative products and high-weight comparison](quarter-list-second-quartic-darboux.md)

Reweight $X,Y,V$ by $1,nR,nR$ and divide weights by $n$, writing $w$ for the resulting normalized degree. The original monomial weight was $i+dj+(d-1)k$, with $k\le1$. Every monomial satisfies $j+k\le5$, since an ordinate monomial of total degree six would have original weight at least $6d-1$. The reweighting adds $j+2k\le6$ before dividing by $n$, so $w<6R$.

The low-weight tests for the first-prime cofactor proof apply afresh at the stronger agreement $s$. At a nonradial site the number of possible slopes is at most six because the factor has total ordinate degree at most five. The proportion of nonradial sites is at most $7[1-s^2/(R+(2s-R)/M_0)]$. The order-6000 quotient comparisons, including the vertical-content bound for repeated denominators of degrees two or three, exclude $w<5R$. The verifier replays these inequalities at the stated $s,M_0$. [Slope count and lower linear weights](quarter-list-uniform-length.md#the-normalized-interpolation-board) · [First-prime cofactor comparison](quarter-list-darboux-cofactors.md#reduction-to-a-rational-differential-equation)

For $5R\le w\le6R$ let $K=4w+5(w-R)-20R$ bound the total plane intersection length divided by $n$. On each of 80 weight intervals the order-50000 quotient supplies a common cap and a lower bound $Z$ on the mean radial order. Either $K+j(j+1)+1-2jZ<0$, which excludes the factor, or for the chosen $j=2$ or $3$ the verifier checks
$$
 K+j(j+1)+1-2jZ\le J=131/1000,\qquad
 sZ-w>\sqrt{(J+1/4)(R-s^2+(s-R)/1000)} .
$$
Concavity of the mean-order lower bound in the weight permits the two endpoint tests with the same cap. Both tangents $2jo-j(j+1)-1$ lie below $o^2-o-1$ for every integer $o$. The same intersection estimate gives $\operatorname{Var}(o)\le J+1/4$ by completing the square at $j+1/2$. If 1000 words were exterior to the factor, their cropped hit occupancy would have variance at most $R-s^2+(s-R)/1000$. Cauchy–Schwarz against the site orders would contradict the second inequality because each exterior word has at most $wn$ weighted hits. Thus one can retain $M=n-1000$ solutions of the linear equation. [Exterior-word variance](low-rate-named-adaptive-cofactors.md#exterior-words-at-the-first-prime-eighth-rate)

Use the local intersection and contact lemma with four anchors. For an exceptional class of local length one or two the shared residue row has at most one exceptional anchor. All other classes cost at least three units of the excess $nJ$. The proof after blowing up each physical exceptional slope charges its full residual intersection length and works for either of the two tangents above. Put $F(u)=1-(1-u)^4$. The tangent at $151/1000$ proves $F(q)\le a+cq^2$ for $a=299/1000$, $c=798/100$; also $4q\le3a+cq^2$. The actual hit mean $\mu$ satisfies $\mu\ge s$ and $F'(s)\le2cs$, so the combined rank estimate is largest at $s$. Including the sampling and singleton-anchor corrections yields
$$
 \operatorname{rank}\le5+n\left[ F(s)+aJ+c\bigl(R+(1+J)/M-s^2\bigr)
             +\frac{6(1+J)+4J}{M}\right]
 \le 1,073,091,968 .
$$
The nullity is at least **648,856**, and the primitive first integral has degree $m\le1654$. Its completely split constant fibers number at least 648,857. With a moving branch label and at most five poles the tame bound is $2m+5+60m\le102,553$. The stationary-branch Riccati bound also excludes $M$ sections at agreement $s$. This completes the written all-center proof; the executable checks its finite comparisons. [Local resonance and rank lemma](eighth-list-resonant-collisions.md) · [Descent and tame splitting](quarter-list-darboux-cofactors.md#moving-branch-values)

```sh
python3 scripts/probes/probe_quarter_first_resonant_collisions.py
```
