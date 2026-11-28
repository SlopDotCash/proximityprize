# Cyclic septic quartets at 87 errors on the 128-site grid

At either designated prime, no four distinct polynomial words on $\mu_{128}$ of the form
$$
 f_j(X)=A(X)+c^j F(i^jX),\qquad j=0,1,2,3,\qquad i^2=-1,\quad c^4=1,\quad\deg F\le7
$$
can all agree with a center at 41 sites. Thus the cyclic family cannot witness a four-word list at 87 errors. Its useful coincidence count is at most **32**. The unrestricted four-word first failure on this grid is still either 87 or 88 errors. [Direct verifier at both primes](../../../scripts/probes/probe_mu128_cyclic_septic_diagonals.py) · [Unrestricted bound and witnesses](mu128-split-sextics.md)

Subtract $A$ and choose the generator of $\mu_{128}$ so that $i$ is its 32nd power. Reversing the cyclic indexing sends $(c,i)$ to $(c^{-1},i^{-1})$, so either choice of $i$ is covered. Write $P=F-cF(iX)$ for an adjacent difference and $Q=P+cP(iX)=F-c^2 F(-X)$ for an opposite difference. The four adjacent edges have the same number of roots. This number is at most six. Indeed one residue class of coefficients modulo four vanishes in $P$. If the constant or leading coefficient vanishes a septic cannot have seven nonzero roots. If its linear or degree-six coefficient vanishes, seven such roots would have zero sum of inverses or zero sum. The norm bound $7^{32}<p$ excludes either sum on this grid. The opposite difference is nonzero by distinctness and consists of one parity of powers, so it has at most six nonzero roots. [Seven-root norm proof](cubic-list-padding.md#what-a-four-word-power-map-construction-would-require-at-the-pivot)

For a physical site $x$, let $c_x$ be one less than the size of its largest equal-value class. The sum $C$ of the $c_x$ is bounded by the sum of the six pairwise root counts, hence by 36. At equality all six edges would have six roots each and their root sets would be pairwise disjoint. A pair of equalities at the same site gives strictly fewer useful coincidences than equal pairs there, whether the two pairs are disjoint or share an endpoint. Further, $C$ is divisible by four because the cyclic action on the sites is free and preserves the equality pattern up to relabelling.

Suppose $C=36$. After scaling $F$, its opposite difference is
$$
 Q=X^m(X^2-u)(X^2-v)(X^2-w),
$$
where $m=1$ if $c^2=1$ and $m=0$ otherwise, and $u,v,w$ are distinct 64th roots. The opposite edge at the next cyclic position has the negatives of these three squared-site values. Thus no two of $u,v,w$ are negatives of each other. Scaling the source by a grid element multiplies all three squared sites by a common 64th root. In exponent coordinates modulo 64, translate each of the three exponents in turn to zero and take the least resulting sorted triple. This gives exactly 620 representatives.

Write $c=i^t$. In $P$ all coefficients of degrees $j\equiv-t\pmod4$ vanish. The relation $Q=P+cP(iX)$ fixes the four coefficients of degrees with $1+ci^j\ne0$ in the nonzero parity of $Q$. This leaves just $P=P_0+\alpha X^k+\beta X^{k+4}$ with $0\le k<4$ and $k\equiv2-t\pmod4$. A root of $P$ determines a point $(x^4,P_0(x)/x^k)$ on a common affine line. The roots of the four rotated adjacent differences are disjoint only if the six selected roots have six distinct fourth powers. Disjointness from both opposite differences also excludes all fourth-power classes containing a root of either.

For each representative and each of the four scalars the verifier evaluates the fixed polynomial and counts distinct fourth powers on each line through a pair of points with different abscissas. This uses arithmetic directly in the named field. For $t=0,1$ the largest collinear counts are two, three and four for 114, 58 and 448 representatives respectively. For $t=2,3$ every maximum is two. These counts hold separately in both fields, excluding the six required abscissas. Consequently $C\le32$ and the four words can contribute at most $128+32=160$ total hits. Four lists of 41 hits would require 164.
