# A fixed involution pairs the fresh directions in a saturated quarter-rate attack

Let $d=2^{28}-1$ and $n=4d+4$. Suppose four two-row heads at the second prime generate more than $2n$ distinct bad scalars at $n/2$ errors. There is one nonidentity projective involution $J$ over the original field that sends each side direction of the four heads to the opposite side direction, as an identity of rational functions of the coordinate. The same $J$ interchanges the two distinct fresh directions at every double site. At least $4d-1=1,073,741,819$ different $J$-orbits of directions must occur there. [Saturated allocation and general constraints](quarter-saturated-symmetry.md) · [Birationality and displacement](quarter-saturated-birational.md)

## Computing the constant involution

Write $W_i=(A_i,B_i)$. Let $D_0,D_1,D_2$ denote the determinants with four rows $(1,A_i,B_i,Q(A_i,B_i))$ for $Q=X^2,XY,Y^2$ respectively. Their coordinate degrees are at most $4d$. At each of the $4d$ double sites two rows agree, so every determinant vanishes. Thus $D_0=aL$, $D_1=bL$, $D_2=cL$ with constant field elements $a,b,c$ and the common monic locator $L$ of the double sites. If $\Delta_{ijk}$ is the oriented triangle determinant, one has
\[
D_1^2-D_0D_2=\Delta_{012}\Delta_{013}\Delta_{023}\Delta_{123}.
\]
This follows by translating the first head to zero and expanding. Every triple determinant is nonzero, so $b^2-ac\ne0$.

For opposite edge differences $u=(u_1,u_2)$ and $v=(v_1,v_2)$, the product of affine linear equations for the two edge lines vanishes on all four heads. Its quadratic part is $(u_2 X-u_1Y)(v_2X-v_1Y)$. The linear and constant parts make no contribution to the determinant because its first three columns are $1,A,B$. Linearity of the last column therefore gives
\[
a u_2v_2-b(u_1v_2+u_2v_1)+c u_1v_1=0.
\]
Hence $v$ represents the same projective point as
\[
 Ju=(bu_1-au_2,\;cu_1-bu_2).
\]
This matrix squares to $(b^2-ac)I$. It is nonscalar in odd characteristic since its trace is zero and it is invertible. In particular the involution is defined over the original field, even when its two fixed directions require a quadratic extension. Lean checks the discriminant, the constant form on all three opposite pairings and the two linear-representative identities. [Formal polynomial proof](../../../ArkLib/Research/ProximityGap/Frontier/FourHeadCoreDeterminant.lean)

## Coincidences and fresh directions

For each $i=1,2,3$, write $s_i$ for the size of the double stratum of pair $0i$. Its opposite pair has the same size. The gcd of the two coordinates of $W_i-W_0$ is exactly that stratum's monic locator up to a constant: a further common zero, excessive multiplicity, or a common zero of the degree-$d$ homogenizations at infinity would give an additional zero to both triangles containing the edge. Divide by that locator to define the direction map $\phi_i:\mathbb P^1\to\mathbb P^1$. Its degree is $m_i=d-s_i$, since at least one coordinate has full degree $d$ by the nonzero triangle determinants at infinity. The $m_i$ are positive and have sum $d$. The primitive vector for the opposite side is a nonzero constant times $J$ applied to this primitive vector, by coprimality on both sides.

Fix a permutation $i,j,k$ of $1,2,3$. At the $s_i$ sites where heads $j,k$ match, $\phi_j=\phi_k$. At the $s_i$ sites where heads $0,i$ match, $\phi_j=J\phi_k$. Neither direction identity is generic: the first would make heads $0,j,k$ collinear, and the second would make heads $0,i,j$ collinear after replacing $J\phi_k$ by the opposite-edge direction. Each coincidence determinant has degree at most $m_j+m_k=s_i$. Thus the indicated two strata are their complete simple coincidence divisors on the projective line. At each of those double sites the fresh directions form the two-element orbit of $\phi_j$ (using opposite edges for the stratum owned by $j,k$). The two directions are distinct because the three distinct head values at that site are noncollinear, as follows from the exact roots of the other triangle determinants.

If there are $B$ occupied involution orbits on the double sites, these sites can supply only $2B$ distinct directions. The four singleton sites supply at most twelve. Exceeding $2n=8d+8$ therefore requires $B\ge4d-1$. Among the $4d$ double sites, at most one occurrence can repeat an orbit already used. This is a necessary condition on a genuine four-head attack; existence or exclusion at this error count remains open.
