# Prescribed Paley discrepancy against a multiplicative subgroup

Let $F$ be a finite field of odd characteristic and order $q$. Let $H$ be a multiplicative subgroup of $F^\times$ and let $A\subseteq F^\times$ meet each coset of $H$ in at most $K$ points. Put $a=|A|$, $h=|H|$, and let $S=\sum_{x\in A,\,y\in H}\chi(x-y)$, where the quadratic character has $\chi(0)=0$.

For any $\epsilon>0$, if $a,h\ge q^{1/4+\epsilon}$ and $q^\epsilon\ge4C(q)K$, then at the supplied coordinates
$$
 |S|\ \le\ q^{-\epsilon/4}ah ,
 \qquad C(q)=\begin{cases}11&q\ge3251,\\17&q<3251.\end{cases}
$$
In particular this is a power saving for a partial transversal, which may contain any one representative from each occupied coset. The proof applies to arbitrary choices of these representatives. The uniform Paley conjecture allows both sides of the rectangle to vary without the subgroup and occupancy hypotheses. [Lean proof, including the explicit power saving](../../../ArkLib/Research/ProximityGap/Frontier/PaleySubgroupTransversal.lean)

## Two finite moment bounds

For $B\subseteq F$ write $W_B(x)=\sum_{y\in B}\chi(x-y)$. If multiplication by every element of $H$ preserves $B$, then $W_B(ux)=\chi(u)W_B(x)$ for $u\in H$. Hence its square is constant on each nonzero $H$-coset. Each occupied coset contributes at most $K$ copies of that square from $A$, while the full field contributes $h$ copies. The exact character second moment is $\sum_x W_B(x)^2=|B|(q-|B|)$. Cauchy–Schwarz therefore gives
$$
 h\left|\sum_{x\in A}W_B(x)\right|^2\le aK|B|(q-|B|).
$$
In particular $|S|^2\le aK(q-h)$. [Exact second moment](../../../ArkLib/Research/ProximityGap/Frontier/_R16LegendreCosetFace.lean)

For $1\le r\le h$ with $r^4\le q$, choose any $r$-point subset $T\subseteq H$. Each $t\in T$ gives a permutation $u\mapsto t/u$ of $H$. Multiplicativity and $\chi(u)^2=1$ then give
$$
 \sum_{u\in H}\chi(u)W_T(ux)=rW_H(x).
$$
Sum over $x\in A$. The fourth power of this sum is at most $(ah)^3$ times the sum of the fourth powers of its $ah$ summands. Every nonzero product $ux$ arises at most $K$ times, since all possible $x$ lie in one coset and each determines $u$. The unconditional quadratic-character moment bound in Lean yields $\sum_{v\in F}W_T(v)^4\le C(q)qr^2$. Consequently
$$
 |S|^4 r^2\ \le\ C(q)K(ah)^3 q.
$$
With $r=\lfloor q^{1/4}\rfloor$ we have $q^{1/4}\le2r$. Thus $(|S|/(ah))^4\le4C(q)K\sqrt q/(ah)$ whenever $a>0$ and $h\ge q^{1/4}$. Substitution of the two size hypotheses proves the stated power saving. For $h^4\le q$, choosing $r=h$ instead gives $(|S|/(ah))^4\le C(q)Kq/(ah^3)$. [Unconditional fourth moment](../../../ArkLib/Research/ProximityGap/Frontier/_R23ParameterChoice.lean)
