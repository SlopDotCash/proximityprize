# Quarter-rate list safety from a word outside a differential equation

Every closed ball through **537,870,914 errors** on the second named prime at rate $1/4$ contains at most $2n$ words. Its first failing error count is at least **537,870,915**. Here $n=2^{30}$, $d=n/4-1$ and $t=n-537870914$. The proof covers every injective grid and every positive interleaving width. [Exact arithmetic](../../../scripts/probes/probe_quarter_list_exterior_contact.py)

The [linear coefficient intersection proof](linear-contact-quotient.md) bounds the local contact order $o_x$ of an irreducible equation $g=A(X,Y)+B(X,Y)V$ at the received pair $(x,y)$. In its notation, the local intersection multiplicity $I_x$ of $A,B$ satisfies $I_x\ge o_x^2-o_x-1$. If there is a list word $f$ outside the equation, choose $t$ of its agreement sites $S$. The nonzero polynomial $g(X,f,f')$ has degree at most the weight $D$ of $g$ and vanishes to order at least $o_x$ at each $x\in S$. Thus $\sum_{S}o_x\le D$.

For each integer $j\ge2$,
$$
 I_x\ge 2j o_x-j(j+1)-1+2(j-o_x)_+ .
$$
Indeed $(o_x-j)(o_x-j-1)\ge 2(j-o_x)_+$ by integral spacing. Consequently the existence of even one exterior word gives the strengthened mean bound
$$
 2jn\,\overline o\ \le\ n[j(j+1)+1]+aD+b(D-d+1)-dab-2(jt-D)_+ ,            \tag{1}
$$
where $a=\lfloor(D-d+1)/d\rfloor$, $b=\lfloor D/d\rfloor$. This uses $\sum_x(j-o_x)_+\ge (jt-D)_+$ and the weighted Sylvester bound for $\sum_x I_x$. [Local and summed integer inequalities](../../../ArkLib/Research/ProximityGap/Frontier/LinearEquationContactBounds.lean)

Use a primary jet interpolant of order seven and derivative cap two. Its space of solutions has dimension at least **263,870,675**. Call a positive-derivative factor large if it carries at least $L=n/8$ distinct list words. The derivative-independent factors account for at most $b_0=\lfloor(7t-1)/(d-1)\rfloor=13$ words. The second interpolant uses order 6000. The strict dimension comparison, its implication by Bézout, and the local rank formula are those of the [quotient interpolation proof](sixteenth-list-quotient-jets.md#the-local-quotient).

| Derivative degree | Weights checked | Mean-order bound | Least endpoint surplus |
|---:|:---|:---|---:|
| 2 | $2(d-1)\le D<7t$ | Agreement variance with $M_0=L-b_0^2$ | 746,469,558,725,805 |
| 1 | $6d-1\le D<7t$ | Coefficient intersection | 2,629,569,129,577,135 |
| 1 with an exterior word | $5d-1\le D<7t$ | Equation (1) | 1,061,239,334,088,485 |

For the first row the verifier uses the squarefree product of the large factors when their combined derivative degree is two. Its $V$-derivative is coprime to either factor. On each group there remain at least $M_0$ regular solutions. The variance estimate applies to their union after identifying distinct words, and every group already exceeds the Bézout cap. Hence the secondary interpolant would be divisible by every factor of the product, contradicting the quotient dimension comparison. This rules out a quadratic large factor and two distinct large linear factors. For the last two rows split the weight range wherever $a,b$, or the sign of any $jt-D$ changes. On each interval a single derivative cap and a single $j$ give positive endpoint surpluses. The resulting surplus is concave on that interval, proving the comparison for every integral weight in it.

If all groups are small, their total is at most $2L+b_0$. Otherwise there is exactly one large factor, which is linear. If the entire list lies on it, its total $(Y,V)$-degree is at most five by the second row. The [normalized linear-equation bound](first-order-normalized-curve.md) gives at most $5+8d=2n-3$ words in the isolated case and at most $(n-d)/(t-d)$ in the integral-family case. If there is an exterior word, the third row forces total degree at most four. Even adding the other small factor and all derivative-independent factors gives at most $4+6d+L+b_0<2n$ in the isolated case. The integral-family bound is below $L$. This establishes the stated closed-ball bound. The geometric proof is written and the finite dimension comparisons are checked in exact arithmetic.
