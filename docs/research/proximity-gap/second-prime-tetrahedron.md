# Six tetrahedron edges lower the second-prime half-rate MCA ceiling

At length $n=2^{30}$ and dimension $n/2$, a single received pair on the second named subgroup has **2,147,483,649 distinct bad scalars at 387,740,104 errors**. The integer budget is $2^{31}$, so the operational supremum is at most $387740104/1073741824$. The same witness works for every dimension from 536,870,912 through 686,001,719 and every positive interleaving width. This lowers the preceding upper bound by 14,913,081 errors. Safety at the predecessor remains open. [Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeTetrahedron.lean) · [Earlier rectangular grid and its exact construction-class limit](second-prime-hyperbola-grid.md)

## The four vertices and six heads

Put $s=n/8$ and $t=x^s$. Let $z$ be the primitive eighth root supplied by the domain generator. Take four points $(a,a^2,a^3)$ for $a\in\{1,z,z^2,z^3\}$. Each pair of vertices gives one polynomial head by evaluating the line between them in the slice with first coordinate $t$. Its two coordinates before the fixed linear change are
$$
U_{ab}(t)=(a+b)t-ab,\qquad
W_{ab}(t)=(a^2+ab+b^2)t-ab(a+b).
$$
Use $V_{ab}=W_{ab}+7U_{ab}$ to avoid vertical directions in the selected comparisons. At each vertex fiber the three incident edges agree. From that common point, the other three edges give three distinct directions. Away from the vertices, a received value equal to one edge gives three distinct foreign directions after duplicates in the faces of the tetrahedron are removed. A received value of $(17,29)$ on the selected off-head sites gives six distinct directions. Lean checks every selected agreement, nonzero denominator and direction determinant over the named field. [Finite geometric checks](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeTetrahedron.lean) · [Independent integer verifier](../../../scripts/probes/probe_second_prime_tetrahedron.py)

## Counting common agreements and labels

Give the common locator $J$ exactly $3s-2=402653182$ distinct roots outside the four vertex fibers. Its degree leaves room for the site-separating term $xJV_{ab}(x^s)$ at half rate. Each head agrees at all common roots and on its two vertex fibers. Of the remaining $s+2$ sites, use $44,739,241$ for the off-head value. Distribute the other $89,478,489$ sites among the six edge values. Three receive $14,913,082$ each and three receive $14,913,081$ each. The joint cores therefore have 686,001,720 and 686,001,719 sites. One further agreement gives the claimed error count.

Every vertex or edge-owned site supplies three directions. Every off-head site supplies six. Writing $v=44739241$, the number of chosen labels is
$$
3(4s)+3(s+2-v)+6v=15s+6+3v=2147483649.
$$
At a foreign site, a chosen head has a different second coordinate from the received value. Its scalar has the form $c\,(u-U_{ab})/(V_{ab}-v_0)-d x$, where $(u,v_0)$ is the received value before multiplication by $J$. The coefficient of $d$ distinguishes sites and the coefficient of $c$ distinguishes the selected directions at each site. The field size bounds the number of forbidden parameter lines, giving a common pair $(c,d)$ that separates all these labels. The joint core determines any degree-bounded explanation, which the second coordinate at the fresh site then contradicts. [Selected-site construction](../../../ArkLib/Research/ProximityGap/Frontier/PlanarQuartetMass.lean)

The error count is sharp for one-fresh allocations using these six fixed heads, degree allocation and site-separating shear. At the preceding error count, five heads contribute at most $5(387740103+1)<2^{31}$ labels, so all six must be active. Let $r$ be the number of common roots where the received pair equals the common value, $o$ the number of other sites receiving a head value, and $a$ the number among those on a vertex fiber. Then $r\le3s-2$, $a\le4s$, and for minimum core size $c$ and label count $L$ one has $6c\le6r+o+2a$ and $L\le6(n-r)-3o$. The first inequality counts each owned site once, adding up to two extra owners at a vertex. The second uses at most three distinct foreign directions per owned site and at most six elsewhere. For $L>2^{31}$ these inequalities force $c\le686001719$. An earlier unrestricted failure can still arise from other heads or a different way of serving labels. [Owned-site bounds and integer optimization](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeTetrahedron.lean)

Independent verified kernel replay accepted 29,716 declarations for the witness and its operational upper bound. The standard-library verifier reproduces the group orders, the six core sizes and the label count. [Reproduction script](../../../scripts/probes/probe_second_prime_tetrahedron.py)
