# What the coding support ranks determine about Paley graphs

The universal prize formulas determine the two coding thresholds for a supplied domain. A Paley discrepancy is also a function of the **relative placement** of two sets in the field. The same indexed Reed–Solomon codes can give a complete bipartite Paley graph at one placement and exactly half its edges at another. Even the support ranks on a single larger domain with both subsets marked can survive a change in discrepancy. [Universal coding theorem](../../../ArkLib/Research/ProximityGap/RankReview.lean) · [Classical discrepancy conjecture, Conjecture 2.12](https://arxiv.org/html/2309.09124v3#S2.SS4)

## An explicit instance at the prize tolerance

Write \(\chi\) for the quadratic character, extended by zero, and \(S(A,B)=\sum_{a\in A,b\in B}\chi(a-b)\). Let \(H=\mu_{16}\) in the prime field of order \(p=680564733906249808969588989158290882561\). All elements of \(H\) are squares because \(32\mid p-1\). For \(c\ne0\) outside \(H\), the two cosets are disjoint. The substitution \(u=y/x\) for \(x,y\in H\) gives
\[
 S(H,cH)=16\sum_{u\in H}\chi(1-cu).
\]
For \(c=122764\) all sixteen signs are positive. For \(c=6\) eight are positive and eight negative. Thus the first pair has all 256 edges and the second has 128 edges, with signed discrepancies 256 and zero. The same counts hold in the sum convention because \(H=-H\). [Lean discrepancies and code equality](../../../ArkLib/Research/ProximityGap/Frontier/PaleyCodingCosets.lean) · [Independent field arithmetic](../../../scripts/probes/probe_paley_coding_cosets.py)

Index each coset by \(h\in H\). Its degree-below-\(k\) evaluation code is exactly the code on \(H\), since \(f(X)\mapsto f(cX)\) bijects the polynomial space. This preserves every folded and joint agreement space. It also induces a linear bijection on every Vandermonde kernel, preserving dimensions with any list supports and any chosen collision edges. Each individual domain therefore has the same MCA and list rank data at every tested support. At tolerance \(2^{-128}\) each has first failing MCA error count two at all four rates, and first failing list counts \(5,8,10,11\) in decreasing rate order, at every positive interleaving width. [Length-16 threshold theorem](../../../ArkLib/Research/ProximityGap/Frontier/BudgetTwoSixteenReview.lean)

## Prescribing every coset discrepancy in a logarithmic range

Let \(p\) be an odd prime and \(H\) a subgroup of order \(n\) with \(2n\mid p-1\). For every prescribed sign vector \((s_h)_{h\in H}\) the number of \(c\in\mathbb F_p^\times\setminus H\) satisfying \(\chi(1-ch)=s_h\) for all \(h\) is at least
\[
 {p\over 2^n}-\left({n\over2}-1+2^{-n}\right)\sqrt p-{n\over2}-1.
\]
In particular, whenever this lower bound is positive, the same two indexed codes admit all \(n+1\) signed discrepancies \(n(2j-n)\), \(0\le j\le n\), by changing their relative coset. This applies uniformly for \(n\le(1/2-\eta)\log_2 p\) for every fixed \(0<\eta<1/2\) and sufficiently large \(p\), subject to the same divisibility. It gives no instance with both sides growing as a fixed positive power of \(p\).

To count the wanted parameters, sum \(2^{-n}\prod_{h\in H}(1+s_h\chi(1-ch))\) over the field. Outside the \(n\) distinct roots it is the indicator of the sign pattern. Each root contributes at most \(1/2\), and excluding \(c=0\) costs at most one. In the expansion, a nonempty subset of \(j\) factors gives the character of a squarefree polynomial of degree \(j\). Weil's bound gives absolute complete sum at most \((j-1)\sqrt p\). Summing these errors uses \(\sum_{j=1}^n{n\choose j}(j-1)=2^{n-1}n-2^n+1\). The empty subset gives \(p\). Finally each \(u\in H\) occurs exactly \(n\) times as \(y/x\) and \(\chi(x)=1\). This is the classical prescribed-adjacency argument applied to the relative placement of evaluation codes. [Weil character estimate, Theorem A.1](https://link.springer.com/article/10.1007/s40879-021-00521-5) · [Blass, Exoo and Harary](https://doi.org/10.1002/jgt.3190050414)

## A single domain with both subsets marked

There is a stronger invariance if both subsets are marked inside \(\mathbb F_p^\times\). For each \(k\ge1\), reverse the \(k\) coefficients of every RS polynomial by setting \(g(X)=X^{k-1}f(1/X)\). At the inverted site \(1/x\) its value is \(x^{1-k}f(x)\). Multiplication by this nonzero coordinate weight on both received rows, each center and every codeword is an invertible linear transformation. It commutes with scalar folding and preserves all equalities at marked coordinates. Coefficient reversal also preserves word-collision equations. Thus every MCA support-space dimension and every list-kernel dimension is the same on the identically indexed domain \(x\mapsto1/x\), including patterns that use both marked subsets. The two enumerations have the same range, the full multiplicative group. [Reciprocal transport of the literal MCA event](../../../ArkLib/Research/ProximityGap/Frontier/ReciprocalChartMCA.lean) · [List rank matrix](../../../ArkLib/Research/ProximityGap/Frontier/ListSupportRank.lean)

Nevertheless \(\chi(a^{-1}-b^{-1})=\chi(-1)\chi(a)\chi(b)\chi(a-b)\) for nonzero \(a,b\). Fix any \(t\) distinct nonzero sites \(a\in A\) at \(p\equiv1\bmod4\). Prescribe \(\chi(a-b)=1\) for all of them, and also prescribe \(\chi(b)=\sigma\) for either sign. The same product argument on the \(t+1\) distinct linear roots \(A\cup\{0\}\) gives at least
\[
 M={p\over 2^{t+1}}-
 \left({t+1\over2}-1+2^{-(t+1)}\right)\sqrt p-{t+1\over2}
\]
choices of \(b\) for **each** sign. Here the excluded root \(b=0\) is already counted in the root correction. If \(M\ge1\), choose \(\lfloor M\rfloor\) solutions of each sign and let \(B\) be their union. We get
\[
 S(A,B)=|A||B|,\qquad S(A^{-1},B^{-1})=
 \chi(-1)\left(\sum_{a\in A}\chi(a)\right)
          \left(\sum_{b\in B}\chi(b)\right)=0.
\]
For \(t\le(1/2-\eta)\log_2 p\) this permits \(|B|\) of order at least \(p^{1/2+\eta}\) for large \(p\). The logarithmic side explains exactly why the example is compatible with the conjecture. In the polynomial-size range, the missing arithmetic estimate bounds the number of shifts of a prescribed set that have a large excess of square or nonsquare symbols. [Exact list-recovery reduction](../../../ArkLib/Research/ProximityGap/Frontier/PaleyShiftListRecovery.lean)

For an example on one smooth domain, take \(p=65537\), so \(\mathbb F_p^\times\) has order \(2^{16}\). Set \(B=\{1,\ldots,11,13,8456,22253,29382,54291,61673,64033\}\) and take \(A\) to be all nonzero \(x\) for which every \(x-b\) is a nonzero square. Exact enumeration gives \(|A|=|B|=18\) and nine squares in \(B\). Thus \(S(A,B)=324\), and every row after inversion has nine squares and nine nonsquares. All 162 edges in that second rectangle are counted directly by the same certificate. The full domain remains \(\mathbb F_p^\times\) under inversion. [Reproducible rectangle check](../../../scripts/probes/probe_paley_coding_cosets.py)

## Cancellation under a common projective change of coordinates

For arbitrary \(A,B\subseteq\mathbb F_p\), write \(a=|A|,b=|B|\) and assume \(ab>0\). For each pole \(t\), take the discrepancy \(S_t\) after applying \(x\mapsto(x-t)^{-1}\) to **both** sets, omitting the pole wherever it occurs. For every nontrivial multiplicative character at an odd prime, the following written estimate holds.
\[
 \frac1p\sum_t\left|\frac{S_t}{ab}\right|^2
 \le \frac{2}{ab}+\frac{3}{\sqrt p}.
\]
Indeed, write \(E=\{(x,y)\in A\times B:x\ne y\}\). For the quadratic character an edge contributes
\(\chi(-1)\chi(x-y)\chi(x-t)\chi(y-t)\), including the correct zero at either pole. On expanding the square, the correlation for two edges is a complete character sum of four linear factors. At most two ordered partners per edge have the same unordered endpoints, contributing at most \(p\) each. For every other partner the polynomial has a root of odd multiplicity, so the absolute sum is at most \(3\sqrt p\) by Weil's theorem. Sum the bounds and use \(|E|\le ab\). [Weil bound and hypotheses, Theorem A.1](https://link.springer.com/article/10.1007/s40879-021-00521-5)

For a character of order \(m>1\), the two denominator factors in the edge term are conjugated. Expanding \(|S_t|^2\), a pair of edges \((x,y),(x',y')\) gives the character of \(((t-x)(t-y))^{m-1}(t-x')(t-y')\), times a constant of modulus one. Unequal unordered pairs leave at least one root with multiplicity \(1\) or \(m-1\). The polynomial cannot be a constant times an \(m\)-th power and has at most four distinct roots. Thus the same Weil estimate applies independently of the character order.

For \(a,b>p^\epsilon\) and \(0<\delta<\min(\epsilon,1/4)\), the fraction of all poles with \(|S_t|\ge ab\,p^{-\delta}\) is at most \(2p^{2\delta-2\epsilon}+3p^{2\delta-1/2}\). If the two sets are marked in an evaluation domain \(D\), at most \(|D|/p\) additional poles are inadmissible. For every remaining pole, translation followed by coefficient reversal gives the same joint coding ranks by the argument above. A projective image of a smooth domain can lose smoothness. This proves a power saving for almost every joint chart of any supplied sparse domain with \(|D|=o(p)\). The original chart is prescribed in the Paley conjecture. For the quadratic character, undoing the inversion weights requires partitioning each vertex set according to \(\chi(x-t)\). The two partitions depend on the pole. The moment above controls fixed vertex sets as the pole varies. A uniform bound for those varying subrectangles would require an additional estimate.

For the quadratic character there is also a kernel-checked projective estimate over every finite field of odd order \(q\). Its normalized mean-square bound is \(2/(ab)+14/\sqrt q\), improved to \(2/(ab)+8/\sqrt q\) when \(q\ge3251\). It uses the repository's Stepanov estimate for quartic sums. The Lean theorem identifies the actual two chart images and proves a relative bound on the number of exceptional poles. The constant 3 and the arbitrary-character and higher-moment results here use the cited Weil bound in the written proof. [Lean moment and exceptional-pole count](../../../ArkLib/Research/ProximityGap/Frontier/PaleyProjectiveMoment.lean)

### Higher moments for sparse sets

For each fixed integer \(r\ge1\), let \(B_{4r}\) be the number of set partitions of \(4r\) labelled elements. The same written argument gives
\[
 \frac1p\sum_t\left|\frac{S_t}{ab}\right|^{2r}
 \le \frac{B_{4r}}{(ab)^r}+\frac{4r-1}{\sqrt p}.
\]
Expand \(r\) edge terms and \(r\) conjugates. The positions of their endpoints consist of \(2r\) labels from each vertex set. If some endpoint occurs just once, its root has multiplicity \(1\) or \(m-1\), so the complete character sum is bounded by \((4r-1)\sqrt p\). For all other tuples, partition the \(4r\) positions by equal values. A block with \(\alpha\) positions from \(A\) and \(\beta\) from \(B\) has at most \(a^{\alpha/2}b^{\beta/2}\) choices. For a pure block this follows from its size being at least two. For a mixed block use \(|A\cap B|\le\sqrt{ab}\). Multiplication gives at most \((ab)^r\) tuples per partition. Bound the complete sum for each such tuple by \(p\) and divide by \(p(ab)^{2r}\).

For both sizes above \(p^\epsilon\), choose \(r\) with \(2r\epsilon\ge1/2\). For every \(0<\kappa<1/2\), taking \(0<\delta\le\kappa/(2r)\) bounds the fraction of poles with relative discrepancy at least \(p^{-\delta}\) by \((B_{4r}+4r-1)p^{-1/2+\kappa}\). The pole-free condition for an entire coding domain is as above.

## Moving one of the two sets by translations

For any finite field, any nontrivial multiplicative character, and the sum convention, let \(S_v=\sum_{x\in A,y\in B}\chi(x+y+v)\). Lean proves
\[
 \sum_v |S_v|^2=qE^+(A,B)-(ab)^2.
\]
Here \(E^+\) counts ordered solutions \(x+y=x'+y'\). In particular, if \(M=\max(a,b)>0\) and both sets are nonempty, the fraction of \(v\) with \(|S_v|\ge\eta ab\) is at most \((1/M-1/q)/\eta^2\) for \(\eta>0\). This holds separately for every prescribed nonzero dilation of \(B\). Taking \(M\ge q^\epsilon\) and \(\eta=q^{-\delta}\) gives an exceptional fraction at most \(q^{2\delta-\epsilon}\), which tends to zero for \(\delta<\epsilon/2\). This controls the distribution even when the identity placement is exceptional. [Exact translation identity and relative bound](../../../ArkLib/Research/ProximityGap/Frontier/PaleyTranslationEnergy.lean)

A separate finite comparison quantifies what the intersections of two translates of the accepted symbol set can determine. At a prime congruent to three modulo four, a cyclic list with the same pair intersections as the genuine quadratic list admits a strictly larger perfect-agreement list. [Exact multishift counts](paley-cyclic-list-design.md)
