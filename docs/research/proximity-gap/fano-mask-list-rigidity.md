# Seven binary hyperplane masks cannot support a Reed–Solomon list in odd characteristic

The \(n+1\) quarter-rate supports from the first-prime packing construction cannot be the chosen agreements of distinct codewords under **any bijection** to an injective evaluation grid. Seven homogeneous masks already give a contradiction. The conclusion holds over every field of odd characteristic and at every positive interleaving width. At \(n=2^{30}\) it excludes this support construction at the first open error count of 536,870,914. Deciding that count still requires control of other support families. [Support packing and cyclic indexing](oriented-fiber-list-bounds.md#pairwise-support-packing-at-the-first-open-quarter-rate-step)

Partition a domain into eight classes of \(b\) distinct sites, indexed by \(x\in\mathbb F_2^3\). For each nonzero \(a\in\mathbb F_2^3\), let its mask be the four classes with \(a\cdot x=0\). Suppose a received word agrees with a distinct polynomial \(f_a\) of degree below \(2b\) on each such mask except at most \(h\) sites per mask. If \(h\ge1\) and \(b>63h-6\), this is impossible. In the cited construction restrict to seven normals in one three-dimensional subspace of the binary dual. Their classes have \(b=2^{27}\), their degrees are below \(2b\), and \(h=2\). This proof even permits \(h=2130440\) deletions per word at that length.

## Short relations on the Fano lines

Scalarize any interleaving by mapping a column \((u_i)\) to \(\sum_i u_iT^i\) in the rational function field over the original alphabet field. The codeword degree in the evaluation variable \(X\), the comparisons at sites and the distinctness of the words are preserved. Write \(k\) for the resulting scalar field.

All seven polynomials agree with the received word on at least \(b-7h\) common sites in class zero. Subtract one reference word from each and divide by the monic vanisher of those sites. This gives seven distinct polynomials \(p_a\) of degree at most \(D=b+7h-1\). The divisor is nonzero on each other class. For each nonzero class \(x\), the three normals with \(a\cdot x=0\) form a line in the Fano plane of normals. Their three polynomials agree with each other at at least \(b-3h\) sites of class \(x\). Let \(V_x\) vanish simply at these sites. For the three indices \(i,j,k\) write \(p_i-p_j=V_x q_{ij}\), and likewise for the other pairs. All three quotients are nonzero and have degree at most \(c=10h-1\). The identity
\[
 q_{jk}p_i+q_{ki}p_j+q_{ij}p_k=0
\]
follows by substitution, and the three coefficients sum to zero. This produces seven rows over \(k[X]\), indexed by the Fano lines. Each is supported precisely on its three incident columns. The resulting matrix kills the all-ones vector and the vector of seven polynomials.

## The rank over the rational function field

Put \(K=k(X)\). The matrix has rank exactly five over \(K\). The two displayed kernel vectors are independent since the \(p_i\) are distinct. If there were a third independent vector \((w_i)\), the seven projective points \([1:p_i:w_i]\) over \(K\) would be distinct, span a plane, and be collinear on every Fano line by the seven row relations.

To see the characteristic obstruction directly, take the three points indexed by the binary basis vectors. They span the plane, since every other binary label is obtained by successive sums and hence lies on one of the corresponding lines. Make these three points the coordinate axes. The points indexed by pairwise sums then have coordinates \([a:b:0],[c:0:d],[0:e:f]\), with all six entries nonzero. Write the seventh point as \([x:y:z]\). Its three incidences with a basis point and the opposite sum yield \(ay=bx,\ cz=dx,\ ez=fy\). All of \(x,y,z\) are nonzero, whence \(ade=bcf\). But collinearity of the three pair sums gives \(ade+bcf=0\). This contradicts \(2bcf\ne0\) in odd characteristic. [Kernel-checked coordinate identity](../../../ArkLib/Research/ProximityGap/Frontier/FanoMaskRigidity.lean)

## The polynomial degrees give the contradiction

Fix two indices 1 and 2. The other five matrix columns are independent, since a kernel vector zero at 1 and 2 must be zero by the kernel description and \(p_1\ne p_2\). Select five rows making these columns an invertible matrix over \(K\) and let \(B\in k[X]\) be its determinant. Solve for the normalized kernel vector with entries \((p_i-p_1)/(p_2-p_1)\). Cramer's rule gives numerators \(A_i\) such that every entry is \(A_i/B\), including \(A_1=0,A_2=B\). Each determinant has degree at most \(5c\), since every entry has degree at most \(c\). In particular
\[
 B(p_i-p_j)=(A_i-A_j)(p_2-p_1),
 \qquad A_i-A_j\ne0\quad(i\ne j).
\]
For each of the seven nonzero classes choose two incident normals. Their difference vanishes on the selected \(b-3h\) sites there. The base difference \(p_2-p_1\) must vanish at all those sites except possibly the at most \(5c\) roots of the corresponding numerator difference. These classes are disjoint. Thus the base difference has at least \(7(b-3h-5c)\) distinct roots. Substituting \(c=10h-1\) and \(b>63h-6\) gives \(7(b-3h-5c)>D\), contradicting its degree.

The same argument applies to unrelated supports whenever seven words have a common core and seven disjoint collections of sites arranged with these Fano triple incidences. If dividing out the core leaves degree at most \(D\), and the seven respective collections have sizes \(s_x\le D\), put \(C\) equal to the sum of the largest five values of \(D-s_x\). Each row then has degree at most its own \(D-s_x\), so every determinant above has degree at most \(C\). The inequality \(\sum_x\max(0,s_x-C)>D\) excludes that incidence pattern. A collection larger than \(D\) makes two words equal directly. [Exact degree and finite-field checks](../../../scripts/probes/probe_fano_mask_list_rigidity.py)

## A characteristic-two control

On the additive grid \(\mathbb F_{2^m}\) of length \(n=2^m\), all \(n-1\) homogeneous binary hyperplane masks occur at once with at most one missing agreement each. For nonzero \(\alpha\), the normalized trace polynomial \(R_\alpha=\operatorname{Tr}(\alpha X)/\alpha^{n/2}\) is monic of degree \(n/2\) and has zero constant term. The polynomial \(f_\alpha=(X^{n/2}-R_\alpha)/X\) has degree at most \(n/4-1\). Its leading coefficient is \(-\alpha^{-n/4}\), distinct for each \(\alpha\) because raising to the power \(n/4\) is an iterate of Frobenius. At every nonzero point of the trace hyperplane \(\operatorname{Tr}(\alpha x)=0\), it agrees with the one center \(X^{n/2-1}\). The trace pairing supplies all binary linear functionals on the grid. In particular the seven-word pattern is realizable in this characteristic with \(h=1\), even at production length. This gives \(n-1\) words at radius \(n/2+1\).
