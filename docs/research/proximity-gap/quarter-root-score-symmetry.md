# Galois quotients and reflection pencils at the first prime

On the actual order-$n=2^{30}$ subgroup $H$ in the first named field, the maximum reduced three-head score among **all geometrically Galois rational maps** of degree $m\le268435454$ is **402653184**. Arbitrary changes of source and target coordinates over the algebraic closure are included. This falls below the existing cubic score **603979776**. A separate fixed-prime test of degree-fourteen rational maps with a specified involution and two seven-root trace fibers also fell below the cubic on the order-64 quotient. The unrestricted first-error interval remains $[447392428,480946859]$. [Root score and its relation to the actual threshold](quarter-three-head-root-score.md)

## The production subgroup detects projective symmetries

For a reduced map $f=P/Q$ put $U=f^{-1}(\{0,1,\infty\})$ on the geometric projective line and $W=H\cap U$. Then $|U|\le3m$. The score is $s=2|W|-3m$. Fix a projective linear transformation $L$. Both $W$ and $L^{-1}W$ have size $|W|$. They lie in $U\cup L^{-1}U$, so
\[
 |H\cap L^{-1}H|\ge s-|L^{-1}U\setminus U|.
\]
If $L$ is neither a scaling nor a scaled reciprocal, the left side is at most **3960117**. Indeed it counts regular points on a nonsingular fractional-linear graph with both coordinates in $H$. The integral Stepanov bound in Lean applies over the algebraic closure as the characteristic exceeds $2^{40}$. Its hypotheses allow affine maps and zeroes or poles at infinity. Corvaja and Zannier independently give a bound of 4993531 from their positive-characteristic gcd theorem. Thus any candidate at least as good as the cubic must lose at least **600019659** points under every such attempted symmetry. [Lean graph bound](../../../ArkLib/Research/ProximityGap/Frontier/MobiusSubgroupBound.lean) · [Score inequality](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRootScoreSymmetry.lean) · [Corvaja and Zannier, Theorem 2](https://doi.org/10.4171/JEMS/409)

In particular a symmetry of $U$ for a candidate with $s>3960117$ must be $cX$ or $c/X$. There is at least one pair $x,L(x)\in H$, hence $c\in H$ as well. The entire stabilizer of the three-fiber union belongs to the dihedral group of $2n$ such transformations. If $f$ is geometrically Galois, its $m$ deck transformations preserve $U$, so $m\mid 2n$. Since $m<n/4$ and $n$ is dyadic, $m\le n/8$. Such a map has $s\le3m\le402653184$. A map of score at most 3960117 also satisfies this upper bound. For attainment put $m=n/8$ and choose three distinct eighth roots $a,b,c$. The map $\frac{c-b}{c-a}(X^m-a)/(X^m-b)$ has three disjoint size-$m$ fibers above $0,1,\infty$ in $H$. For the full-split successor degree $m=n/4-2$, divisibility by both $m$ and $2n$ leaves at most two deck transformations even without a Galois hypothesis. [Other restrictions on inner factors of the full-split map](quarter-split-pencil-pullbacks.md)

## Searching a non-Galois reflection family on 64 sites

A reflection $X\mapsto c/X$ with $c\in H$ remains possible. On the order-64 quotient, scaling reduces the reflection parameter to $c=1$ or $c=w$, where $w$ is a primitive 64th root in the first prime. The invariant coordinate is $T=X+c/X$. Every trace node has two preimages except for fixed points of the reflection, which have one. We searched $f=G(T)$, where the numerator and denominator of $G$ are disjoint seven-root vanishers on these nodes. The reduced degree of $f$ is fourteen. To improve the existing quotient score 36 its three fibers together would need at least forty original sites.

For each endpoint, its seven trace nodes form at most two intervals in **one** angular ordering. The orderings of the two endpoints vary independently. Specifically, represent the orbit $\{i,a-i\}$ by its smaller exponent modulo 64 for $c=w^a$, sort these representatives, and form the intervals in that ordering. Allow all exponent reindexings $i\mapsto ti+b$ with $t$ odd and $2b=a(1-t)\bmod64$ before taking the orbit representatives again. The program enumerates the resulting sets without identifying Galois conjugates in the actual prime field.

| Reflection | Seven-node endpoint sets | Disjoint pairs | Pairs with a third fiber on two or more trace nodes | Maximum score |
| --- | ---: | ---: | ---: | ---: |
| $1/X$ | 32504 | 80248896 | 0 | 18 |
| $w/X$ | 31040 | 71183152 | 128 | 22 |

Two disjoint vanishers $A,B$ have the same ratio at distinct available nodes $u,v$ precisely when $A(u)/A(v)=B(u)/B(v)$. Grouping endpoints by these exact residues checks every disjoint pair that can contribute a multi-node third fiber. For the remaining pairs the third fiber contains at most two original sites and the score is at most 18. The best score **22** in either reflection class remains below 36. This computation tests the given trace sets, leaving arbitrary reflection-invariant rational maps and nonsymmetric pencils open. [Reproducible fixed-prime enumeration](../../../scripts/probes/probe_quarter_reflection_root_score.py)
