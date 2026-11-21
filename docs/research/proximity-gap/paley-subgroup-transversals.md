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

## The two production fields

Take $H$ to be the order-$2^{30}$ subgroup used as the smooth evaluation domain at either named production prime $p$. Every partial transversal $A$ of size at least $2^{77}$ satisfies $2|S|\le |A||H|$. Indeed, $|H|^4\le p$ and $176p\le 2^{77}|H|^3$, so the fourth-moment inequality with $r=|H|$ and $K=1$ gives the result. At $|A|=2^{77}$ both sides have size below $\sqrt p$ and the field has more than $2^{77}$ distinct nonzero $H$-cosets from which to choose representatives. Lean checks the two numerical comparisons and the rectangle theorem. [First modulus](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30.lean) · [Second modulus](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30Second.lean) · [Production rectangle bound](../../../ArkLib/Research/ProximityGap/Frontier/PaleySubgroupTransversal.lean)

## Signed occupancy and uneven cosets

For each nonzero multiplicative coset $D$ of $H$, put $n_D=|A\cap D|$ and $d_D=\sum_{a\in A\cap D}\chi(a)$. Thus $d_D$ counts square sites minus nonsquare sites. The Lean function indexes cosets by $x\in F$, so $d(x)=d_{xH}$ when $x\ne0$ and $d(0)=0$. Each coset occurs exactly $h$ times. In particular $\sum_{x\in F}|d(x)|^s=h\sum_D |d_D|^s$ for $s>0$.

Grouping the amplified identity by the product site $x$ yields $rS=\sum_{x\in F}d(x)\chi(x)W_T(x)$. Hölder's inequality with exponents $4/3$ and $4$, followed by the same unconditional fourth moment, gives
$$
  |S|^4 r^2 \le C(q)q h^3\left(\sum_D |d_D|^{4/3}\right)^3.
$$
Repeated Cauchy–Schwarz also gives $|S|^4r^2\le C(q)q h^3(\sum_D|d_D|)^2\sum_Dd_D^2$. Since $\sum_D|d_D|\le a$, the quarter-scale saving above holds under the single condition $\sum_Dd_D^2\le Ka$ in place of the intersection cap. For example, it applies when $d_D^2\le Kn_D$ on each occupied coset, even if a coset contains a positive fraction of the sample. If $H$ contains a nonsquare, each coset has equally many square and nonsquare sites, so arbitrarily large balanced selections inside that coset are possible as $h$ grows. If every $d_D$ vanishes, the exact identity gives $S=0$.

The Hölder estimate also tolerates concentrations with no sign cancellation. Suppose one coset contains $t\le a^{3/4}$ points and each remaining coset contains at most one. Then $\sum_D|d_D|^{4/3}\le t^{4/3}+a-t\le2a$. More generally, $\sum_D|d_D|^{4/3}\le Ma$ costs $M^3$ in the fourth moment. In the example the explicit saving $|S|\le q^{-\epsilon/4}ah$ follows when $a,h\ge q^{1/4+\epsilon}$ and $q^\epsilon\ge32C(q)$. The location and signs of all sites are arbitrary under these hypotheses. [Signed occupancy, weighted fourth moment, and power savings](../../../ArkLib/Research/ProximityGap/Frontier/PaleySubgroupSignedEnergy.lean)
