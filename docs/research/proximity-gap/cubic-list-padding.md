# Exact small lists from cubic witnesses

On the smooth order-64 subgroup of the 130-bit prime field of order \(p=(3\cdot2^{48}+69)2^{80}+1\), the first list failure at rate \(1/16\) and tolerance \(2^{-128}\) is **44 errors**. The integer budget is three. The MCA first failure on this same length-64 input is **3 errors**. At length \(2^{30}\) and rate \(1/16\), the worst closed list has **exactly three** words throughout **654,311,425 to 704,643,073 errors** on each designated field. Both assertions hold at every positive interleaving width. [Direct checks and named-field witness evaluations](../../../scripts/probes/probe_cubic_list_padding.py)

## Length 64 and a budget of three

More generally let \(4\mid n,\ n\ge32\), and suppose the domain contains a coset of the order-32 subgroup. Use message dimension four. The largest agreement count attained by four words with one received center is **\(n/4+4\)**.

Indeed choose the four cubics and their center on the 32 cyclic sites supplying twelve hits per word. The sixteen distinct pair-only assignments are given by the six exponent sets
\[
 \{0,1,2\},\ \{7,9,23\},\ \{11,25,27\},\
 \{6,20\},\ \{14,28\},\ \{13,17,21\}.
\]
Their integral identities specialize in every field containing the subgroup. Rescaling the variable transports them to any coset. Partition the \(n-32\) other sites into four equal sets and receive the corresponding word on each. All four attain \(12+(n-32)/4=n/4+4\) hits. [Kernel-checked cubic witness](../../../ArkLib/Research/ProximityGap/Frontier/Mu32CubicList.lean) · [Polynomial formulas and sites](mu32-list-threshold-large-characteristic.md#dimension-four-at-the-same-length)

For the converse let \(m_x\) count matches to the center among four distinct words. Then \(m_x\le1+\binom{m_x}{2}\), and each pair has at most three common hits. This uses any row where the vector polynomials differ. Thus \(\sum_xm_x\le n+18<4(n/4+5)\). Replicating the scalar lower example in every row gives the result at all widths. Taking \(n=64\) gives first failure \(64-20=44\), last safety at 43 and operational supremum \(11/16\). The staircase and spike theorem also gives first MCA failure \(B=3\) since \(4+3(B-1)\le64\) and \(4+B+1\le64\). Its operational supremum is \(3/64\). [General MCA theorem](../../../ArkLib/Research/ProximityGap/RankExecutable.lean#L302) The chosen prime has \(64\mid p-1\), \(\lfloor p/2^{128}\rfloor=3\), and an existing primality certificate. [Concrete budget-three field](mu32-list-threshold-large-characteristic.md)

## The two named length-\(2^{30}\) domains

Set \(h=n/64,\ k=4h,\ d=4h-1\). On the order-16 subgroup with generator \(w\), take \(P,Q\) to be the scaled cubic vanishers on the exponent sets \(\{0,1,8\}\) and \(\{2,9,10\}\), with the scalar on \(Q\) making \(P(w^3)=Q(w^3)\). The third fiber, on which \(P=Q\), has exponents \(\{3,5,7\}\). These three full fibers are disjoint in both named fields. Embed them in the order-64 quotient. Let \(H\) be the monic vanisher of \(h-1\) physical points in an unused quotient fiber. The polynomials \(0,H(X)P(X^h),H(X)Q(X^h)\) have degree at most \(4h-1\). Receive their common value at the \(h-1\) common roots and the repeated value at every point of the nine double fibers. Each word now has \(7h-1\) agreements. The \(54h+1\) unused sites suffice for \(18h\) more private agreements per word. Thus all three have at least \(25h-1\) agreements. [Integral split-cubic identity](quarter-three-heads-32-fibers.md)

Four words would have total agreements at most \(n+6d\) by pair counting. Hence for \(\lfloor(n+6d)/4\rfloor+1\le t\le25h-1\) the exact worst list is three. These are the stated closed error counts, including the first step \(671088640\) in the length-\(2^{30}\) three-head MCA interval. At the second prime's exact MCA first failure \(e=715827882\), the same lower construction still supplies three words. Five would require \(5(n-e)\le n+10d\), which fails. The worst list at that pivot is therefore either three or four. [Exact MCA result](full-prize-review.md)

## What a four-word power-map construction would require at the pivot

Consider four candidate words \(f_i(X)=A(X)+J(X)F_i(X^s)\), with \(s\mid n\), after translating one \(F_i\) to zero. Write \(D=\max_i\deg F_i\), so \(\deg J+sD\le d\). On the quotient \(\mu_{n/s}\) let \(C\) be the sum, over its sites, of the maximum multiplicity of a value among the four \(F_i\) minus one. Then \(C\le6D\) by the six pair differences. For any physical center the total number of hits is at most
\[
                    n+sC+3\deg J\ \le\ n+3d+s(C-3D).
\]
This allows any location for the zeros of \(J\). At \(t=(n+2)/3\), one needs \(s(C-3D)\ge(n+8)/3-3d\). Every power quotient with at most 64 sites fails this test: \(n/s\) is a power of two, \(D\le k/s-1\) when \(s\le k\), and \(3sD\le3(k-s)\le9n/64\), strictly below \((n+8)/3-3d\). When \(s>k\), all quotient polynomials are constant and \(C=0\).

On the 128-site quotient the integer requirements become **\(D=7,\ C\ge40\)**. Since all six differences have degree at most seven, only two lost pair equalities are tolerable. In particular the four quotient polynomials cannot take the cyclic form \(F_j(Y)=c^jF(i^jY)\), where \(i\) has order four and \(c^4=1\), even after a common additive shift. The four adjacent differences are rotated, scaled copies of \(P=F(Y)-cF(iY)\), so each would need all seven roots on the 128 sites. Write \(i^a=c^{-1}\), \(0\le a<4\). The coefficients of \(Y^j\) with \(j\equiv a\bmod4\) in \(P\) vanish. For \(a=0\) the constant term vanishes and for \(a=3\) the septic leading term vanishes. For \(a=2\) the degree-six coefficient vanishes, forcing the sum of the seven roots to be zero. For \(a=1\) the linear coefficient vanishes, forcing the sum of their inverses to be zero.

Seven distinct 128th roots have nonzero sum at either named prime. Lift them to the complex 128th roots. Their sum is nonzero since reduction of the integral cyclotomic ring at \(1-\zeta_{128}\) sends every root to one in characteristic two. The mean square of the sum over the 64 complex embeddings is at most seven. Indeed the average of \(\zeta_{128}^{aj}\) over odd \(a\) equals zero except for \(j=0,64\), where it equals \(1,-1\) respectively. The arithmetic-geometric mean bound on the absolute norm is consequently \(7^{32}\), smaller than each named prime. Thus neither prime can annihilate the sum or the corresponding sum of inverses. This excludes the cyclic family. General degree-seven quartets and larger power quotients remain possible, as do constructions outside the specified class.
