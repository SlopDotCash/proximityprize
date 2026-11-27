# Two further quarter-rate errors from the weighted deficit trace

Every closed ball on the second named quarter-rate grid at **536,870,933 errors** has at most $2^{31}$ codewords at every positive interleaving width. This raises the first-failure floor to **536,870,934**. The proof uses the [weighted Hermite-coordinate argument](quarter-list-residual-jets.md) and a sharper estimate for the number of pairs with small overlap. [Exact verifier](../../../scripts/probes/probe_quarter_list_weighted_deficit.py)

Keep $n,d,m,D,S,c,L,Q$ from that argument, now with $j=19$, $t=2d-j$, and $r=n-2t=42$. Write $\kappa=1/c$, $C=(L-1)(L+1)^2$, and take $R=\lceil\sqrt{C(m-1+L)}\rceil$. The normalized cubic matrix in the [spectral deficit proof](spectral-deficit-list.md) gives the entrywise bound
$$
 \sum_{ij}D_{ij}^4(1-D_{ij}^2)\le T
 =\kappa\big[L(L^2-1)+C+R\big]+\kappa^2(R+L^2-1).
$$
This intermediate bound holds for any entry cap $\kappa$, including $1/c>1$. Indeed take $W_{ij}=D_{ij}^3/\max(1,(D^2)_{ii},(D^2)_{jj})$, of operator norm at most $\kappa$ by its row sums. Immediate backtracks along the first or last edge of a length-three walk give the estimate
$$
 \sum D_{ij}^4(1-D_{ij}^2)
 \le \operatorname{tr}W(D^3-D)+2\kappa^2\sum_i(1-(D^2)_{ii})_+ .
$$
Diagonalizing $D$ and applying the spectral estimates for $\sum|\lambda^3-\lambda|$ and $\sum(1-\lambda^2)_+$ yields $T$ as stated.

Put $D'=cD$ and $\mu=1-h/d$. Since $\sum D_{ij}^4\le\kappa^2 S\le2m/c^2$, the ordered fourth mass of $D'$ on entries at most $\mu$ is at most
$$
 \frac{c^6T+2mc^2(1-c^2)}{1-\mu^2}.
$$
The full ordered fourth mass is at least $c^4(m-Q)$ by the repeated-index trace bound. Every unordered tight pair contributes at most two. At $h=36,000,000$ these estimates give more than 1,400,000 tight pairs. The maximum degree of this graph is below 35,000. Thus it contains two disjoint anchors. At $h'=195,000,000$ the ordered square-mass estimate gives at least 343,000,000 loose pairs. Their common covered sites with both anchors number more than $3d$. Applying the polynomial pencil and the value intersection inequality with $s=r+h-1$ gives an exceptional count $e\le124,000,000$.

For $e\le8,000,000$ at least 394,000,000 pairs belong to the pencil. Use $h''=250,000,000$ in the square-mass bound. For each additional pair $(f,g)$, the polynomial
$$
 A(fg-P_0)-B(f+g-S_0)
$$
of degree at most $3d$ vanishes at every ordinary site it covers, since $Ay=B$, $A\ne0$, and $N=0$ there. The zero count is at least $n-e-(r+h''-1)>3d$, so the pair satisfies the pencil identity. Euclid's lemma again gives a polynomial parameter. This also shows why the two initial tight anchors impose no overlap loss on these additional pairs.

Use the weighted coordinates of the Hermite argument with all the certified pairs for the applicable range of $e$. Here the integer dot-product numerator is bounded by $160-2h_0+q-b$. A bound at most $-2$ would give $M\le1+3e/2<343,000,000$. In the other case $q\le161$ and $W\ge2e-161$. For $e\ge20,000$ the dot products are at most $81/K$, with $K=e+q$. The following ranges employ exactly the positive kernels and trace inequality proved in the Hermite argument.

- For $20,000\le e\le500,000$ use the cubic polynomial with $s_1=81/K$ and $a_1=1/81$. It gives $M<124K<343,000,000$.
- For $500,000\le e\le4,400,000$ the same inequality gives $M<85K<394,000,000$.
- For $4,400,000\le e\le85,000,000$ take $m'=4(K+1)$ vectors. There are enough, and $L_1-1<325$. The required left side $8(K+1)$ exceeds $325\cdot327^2$.
- For $85,000,000\le e\le124,000,000$ take $m'=\lceil13(K+1)/5\rceil$. This uses fewer than 323,000,000 vectors, gives $L_1-1<212$, and the left side exceeds $212\cdot214^2$.

This leaves $e<20,000$. With bidegrees $(16,4)$, rank threshold 83 and 82 contact sections, the degree and contact bounds are unchanged. At least $343,000,000/20=17,150,000$ jets must lie on one irreducible factor, exceeding its differential Bézout bound of 7,998,800. This contradiction proves the asserted all-center safety. The field and scalar-extension hypotheses are those in the Hermite argument.
