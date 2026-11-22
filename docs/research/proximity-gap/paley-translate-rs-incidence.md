# How many Legendre translates can a Reed–Solomon code approximate?

Fix any $m$ distinct sites $A\subseteq\mathbb F_p$, with $2\le m\le(p+1)/2$ and $p$ an odd prime. The labels are all $b\in\mathbb F_p$, and their words are $u_b(a)=\chi(a+b)$ in the prime field, including $\chi(0)=0$. For fixed rate $k/m\le R<1$ and any fixed $\eta<(1-R)/2$, **at most $O_{R,\eta}(p/m)$ labels** have a translate word within $\eta m$ errors of a given generalized Reed–Solomon code. This holds uniformly over the sites and nonzero coordinate multipliers. One arbitrary affine offset gives the same bound for $\eta<(1-R)/3$. For $m\ge p^\alpha$ the captured fraction is $O(p^{-\alpha})$, including at agreement $m-C\log p$ for any fixed $C$.

The existing Lean theorem shows that containing every off-domain translate in an affine subspace requires full ambient dimension. The bounds below estimate how many labels are captured even with errors, for the more specific Reed–Solomon encoding. A dictionary covering all labels at the indicated radii needs $\Omega(m)$ such codes. Consequently one near-exact embedding of the translated signed words cannot transfer ordinary RS support-list bounds to all shifts at polynomial puncturing sizes. The field words $a\mapsto a+b$ still encode the character test by list recovery with separate accepted symbols. A prescribed $B$ could consist entirely of exceptional labels when $|B|\le O(p/m)$. [Existing affine-hull theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleyTranslateInterpolation.lean) · [Signed-word reduction](paley-labeled-row-decoding.md) · [Affine list-recovery reduction](../../../ArkLib/Research/ProximityGap/Frontier/PaleyShiftListRecovery.lean)

## Exact interpolation and puncturing

Put $d=(p-1)/2$, $1\le k<m$, $r=m-k$ and $\lambda_a=1/\prod_{t\in A,\ t\ne a}(a-t)$. Taking the coefficient of $X^{m-1}$ in Lagrange interpolation gives $\sum_a\lambda_a a^j=0$ for $0\le j<m-1$ and $1$ for $j=m-1$. Ordinary RS words are the evaluations of $\deg f<k$. For generalized RS fix $v_a\ne0$ and evaluate $v_a f(a)$. Write $c_a=\lambda_a/v_a$.

Let $D=d+r-1$ and $H(B)=\sum_a c_a(B+a)^D$. If $u_b(a)=v_a f(a)$ on every site, its $j$th Hasse derivative for $0\le j<r$ is
$$
 H^{[j]}(b)=\binom Dj\sum_a c_a(b+a)^d(b+a)^{r-1-j}
           =\binom Dj\sum_a \lambda_a f(a)(b+a)^{r-1-j}=0.
$$
The last polynomial in $a$ has degree at most $m-2$. Euler's criterion applies at zero too, since $d>0$. The translates $(B+a)^D$ are linearly independent. Indeed $m-1\le D<p$ and the top $m$ coefficients form a Vandermonde matrix with nonzero binomial row multipliers. Thus $H$ is nonzero. When $v_a=1$, its leading term is $\binom D{m-1}B^{D-m+1}$ and its degree is exactly $d-k$. Counting roots with multiplicity gives
$$
 \#\{b:u_b\text{ lies in the code}\}
 \le
 \begin{cases}
 \lfloor(d-k)/(m-k)\rfloor & \text{ordinary RS},\\
 \lfloor(d+m-k-1)/(m-k)\rfloor & \text{generalized RS}.
 \end{cases}
$$

For agreement $\ell$ take any integer $k+1\le j\le\ell\le m$. Denote the appropriate preceding exact-membership bound at size $j$ by $U(j)$. Counting incidences with all $j$-subsets of $A$ gives
$$
 \#\{b:\exists f,\ \deg f<k,\ \#\{a:u_b(a)=v_a f(a)\}\ge\ell\}
 \le \left\lfloor\frac{\binom mj\,U(j)}{\binom\ell j}\right\rfloor .
$$
Each counted label has at least $\binom\ell j$ qualifying restrictions, including when it has several interpolants. Each restriction inherits its coordinate multipliers. The same double count works for any prescribed affine offset using a valid affine exact-membership bound on $j$ sites, for example the next theorem with $e=0$. If its hypotheses on $j$ give no nontrivial bound, $U(j)=p$ always works.

## Interpolation checks that tolerate errors and offsets

Fix $s\ge0$ arbitrary words $w_1,\ldots,w_s\in\mathbb F_p^A$. Enlarge the code to
$$
 \mathcal C=\{(v_a f(a))_{a\in A}:\deg f<k\}
             +\operatorname{span}\{w_1,\ldots,w_s\}.
$$
A prescribed affine offset belongs to the case $s=1$, since adjoining its whole span can only increase the count. For an error budget $e=m-\ell$, choose integers $h,L$ with
$$
 h>e,\qquad L>e,\qquad h+(s+1)L\le r+1.
$$
Set $D=d+L-1$. The number $N_e$ of labels within $e$ errors of $\mathcal C$ satisfies
$$
 N_e\le\left\lfloor\frac{h(D-h+1)}{(h-e)(L-e)}\right\rfloor .
$$
For ordinary RS with no augmentation take $L=r-h+1$. The sharper numerator is $h(d-k-h+1)$. The choice $h=1$ at zero errors recovers the exact ordinary bound.

Take polynomials $Q$ of degree at most $r-L$ satisfying the $sL$ linear conditions
$$
 \sum_a c_a Q(a)w_i(a)a^j=0\qquad(1\le i\le s,\ 0\le j<L).
$$
Their space has dimension at least $r-L+1-sL\ge h$. Choose any $h$-dimensional subspace and map it into polynomials in $B$ by
$$
 Q\longmapsto H_Q(B)=\sum_a c_a Q(a)(B+a)^D .
$$
Here $m-1\le d\le D<p$ since $L\le r\le m-1$ and $m\le d+1$. The shifted powers are independent by the same Vandermonde argument. All $c_a$ are nonzero and $\deg Q<m$, so the map is injective. Write $W$ for its image.

For a captured label $b$, choose one approximating codeword. Requiring $Q$ to vanish at its at most $e$ error sites costs at most $e$ dimensions. For every resulting $Q$, $H_Q$ has a root of multiplicity at least $L$ at $b$. Indeed for $j<L$, its $j$th Hasse derivative divided by $\binom Dj$ is
$$
 \sum_a c_a Q(a)u_b(a)(b+a)^{L-1-j}.
$$
At error sites the summand vanishes. On replacing $u_b$ by the approximant, the offset contributions vanish by the imposed conditions. For its RS contribution the barycentric sum vanishes because $\deg(Q(X)f(X)(b+X)^{L-1-j})\le(r-L)+(k-1)+(L-1)=m-2$. This includes $a=-b$, and $\binom Dj$ is invertible since $j\le D<p$.

Take the ordinary Wronskian of a basis of $W$, the determinant of its derivatives of orders $0,\ldots,h-1$. A change of basis multiplies it by a nonzero constant. Choose a basis with distinct degrees $0\le d_1<\cdots<d_h\le D<p$. Its leading coefficient is the product of the leading coefficients times $\prod_{i<j}(d_j-d_i)$, by the determinant of the falling factorials, with derivative orders indexing rows and basis elements indexing columns. It is nonzero and has degree $\sum d_i-\binom h2\le h(D-h+1)$. For ordinary RS choose $Q=1,X,\ldots,X^{h-1}$. Their weighted moments give $\deg H_{X^i}=D-m+1+i$ exactly. The Wronskian degree is then $h(D-m+1)=h(d-k-h+1)$.

At a captured label use instead a basis with strictly increasing orders of vanishing $\nu_1,\ldots,\nu_h$. Since at least $h-e$ dimensions vanish to order $L$, $\nu_{e+1+j}\ge L+j$ for $0\le j<h-e$. Every $\nu_i\ge i-1$. Every Wronskian determinant term thus has order at least $\sum_i\nu_i-\binom h2\ge(h-e)(L-e)$. The global degree bound proves the claim. This uses the classical Wronskian subspace-design argument. Its character-specific input here is the subspace of shifted powers created by the RS parity checks. [Guruswami and Kopparty, *Explicit Subspace Designs*](https://eccc.weizmann.ac.il/eccc-reports/2013/TR13-060/)

For fixed $s,R$ and $\eta<(1-R)/(s+2)$, take $k\le Rm$, $e\le\eta m$, and $h=L=\lfloor(r+1)/(s+2)\rfloor$. Both factors $h-e,L-e$ are then bounded below by a positive constant times $m$ for sufficiently large $m$. This proves $N_e=O_{s,R,\eta}(p/m)$ for every such $A$. Completing each zero of $\chi$ by either sign changes at most one coordinate per label, so the completed-row version uses $e+1$ in the same bounds. A fixed fractional gap in $\eta$ absorbs this change.

This also covers every fixed injective, site-dependent encoding of two signs in a characteristic-$p$ field. Each encoding has the form $\sigma\mapsto t_a+c_a'\sigma$ with $c_a'\ne0$, since $p$ is odd. Pulling a GRS code back through these maps changes its multipliers and adds one fixed offset. All polynomial, Vandermonde and Wronskian arguments above work over an extension of $\mathbb F_p$, with the sites and shift labels still in the prime subfield. A common fractional-linear reparametrization of the sites away from its pole is already absorbed by GRS multipliers: substitution into $\deg f<k$ and multiplication by the denominator to the power $k-1$ is an invertible linear transformation on these polynomials.

For discrepancy alone, a bias $\delta$ only guarantees closeness to one of the two constant words at about $e=(1-\delta)m/2$ errors for a biased row. Inserting $k=1$ and $h,L$ near $m/2$ in the ordinary Wronskian bound yields the scale $p/(\delta^2m)$ for these shifts, also obtained by the two-point identity. When $m\ll\sqrt p$, a prescribed set of $m$ labels can lie inside an exceptional set of this size.

## Low-rate alternative using only distance

For any code on these sites in which distinct words agree at at most $k-1$ coordinates, another counting argument applies. Put $t=\ell-1$ and assume $2t>m$ and $t^2>2m(k-1)$. The number of distinct codewords taking values in $\{-1,1\}$ on at least $t$ sites is at most
$$
 L_0=\left\lfloor\frac{2m(t-k+1)}{t^2-2m(k-1)}\right\rfloor .
$$
Choose exactly $t$ valid incidences per word. Write $n_{a,\pm}$ for their counts at each site and sign. If there are $L$ words, then $\sum n_{a,\pm}=Lt$ and $\sum n_{a,\pm}(n_{a,\pm}-1)\le L(L-1)(k-1)$. Cauchy–Schwarz on the $2m$ bins gives the displayed bound.

Complete the valid signs of each such word arbitrarily to $\sigma\in\{-1,1\}^A$. A translate agreeing with this word on at least $\ell$ sites contributes $\sum_a\sigma_a\chi(a+b)\ge 2t-m$, allowing one zero. The two-point character identity gives the sum of the squares of these correlations over $b$ as $pm-(\sum_a\sigma_a)^2\le pm$. Thus the number of captured labels is at most $L_0\left\lfloor pm/(2t-m)^2\right\rfloor$. This applies to an affine translate of GRS because its pairwise agreement bound is unchanged. [Two-point character identity](../../../ArkLib/Research/ProximityGap/Frontier/_R16LegendreCosetFace.lean)

The [finite verifier](../../../scripts/probes/probe_paley_translate_rs_incidence.py) computes actual distances to code spaces by checking all retained-coordinate sets, then checks the puncturing bounds. It constructs the auxiliary polynomial spaces and checks the Wronskian degree and each local multiplicity by Taylor elimination over the prime field. The checks cover 1,152 membership problems, 1,454 puncturing bounds and 1,133 Wronskians. They include every site set in the stated size range at primes 3, 5 and 7, and further prescribed examples at 13, 23 and 41. Run them with Python 3.

~~~sh
python3 -B scripts/probes/probe_paley_translate_rs_incidence.py
~~~
