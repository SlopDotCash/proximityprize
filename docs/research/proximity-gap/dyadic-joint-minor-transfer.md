# Joint determinant bounds for dyadic-root matches

Let $n$ be a power of two and let $z$ have order $n$ in the prime field of order $p$. Write $h=\varphi(n)$. The estimates below use all the determinants attached to one configuration. The single-determinant estimate $54^h<p^4$ for involutions and its length-512 prize endpoint have passed Lean. The joint involution test and the four named length-512 bounds have also passed Lean. The seven-site projectivity estimate below is a written proof pending its full Lean assembly. [Single-determinant transfer](../../../ArkLib/Research/ProximityGap/Frontier/DyadicMeanPairTransfer.lean) · [Length-512 prize endpoint](../../../ArkLib/Research/ProximityGap/Frontier/DyadicList512.lean)

## A lower bound for each surviving complex determinant

Take any minor which is zero in the prime field. Its integer Laurent polynomial vanishes at both $z$ and $z^{-1}$. For the involution matrix, inversion exchanges the constant and product columns after multiplying each row by its nonzero pair product. For the general projectivity matrix, multiplication by $xy$ exchanges both pairs of reciprocal columns. As $n>2$, the roots $z,z^{-1}$ are distinct. The integer cyclotomic resultant is divisible by $p^2$. For an ordinary polynomial obtained by clearing a monomial, its norm is unchanged in absolute value. If the determinant at one primitive complex root is nonzero, its squared absolute norm is consequently at least $p^4$. AM–GM over the $h$ primitive embeddings shows that its mean squared absolute value is at least $p^{4/h}$. This applies to all the surviving minors of the same marked configuration. [Two-root resultant divisibility](../../../ArkLib/Research/ProximityGap/Frontier/RatioProductNorm.lean)

## Involutions

Suppose a non-dihedral involution in the prime field exchanges $L\ge4$ disjoint pairs of sites. In each complex embedding consider the $L$ rows $(1,x_i+y_i,x_iy_i)$ of a matrix $M$. Every two rows are linearly independent, since the rows record the unordered pair through its monic quadratic. No line in the affine sum-product plane contains four rows. Indeed, two disjoint pairs give a unique involution, whose determinant equals the product of their four cross-pair differences. Four collinear rows would therefore give four transpositions over the complex dyadic grid, forcing the involution there to be dihedral. In the inversion case its first two pairs have the same product. In the negation case both pairs are antipodal. The first identity transfers back by exponent addition. The second transfers by squaring and the distinctness of the two sites. Either pattern forces the original involution in the prime field to be dihedral. [Field descent for two distinguished pairs](../../../ArkLib/Research/ProximityGap/Frontier/DyadicFourPairPrime.lean)

Every unordered pair of rows participates in at most one zero three-row minor. At least
$$
G=\binom L3-\left\lfloor\binom L2/3\right\rfloor
$$
minors are thus nonzero. Cauchy–Binet identifies the sum of squared absolute values of all the three-row minors with $\det(M^*M)$. Hadamard's Gram bound gives $\det(M^*M)\le L^2\sum_i|x_i+y_i|^2$, because the constant and product columns each have squared norm $L$. Every distinct dyadic pair has conjugate-average squared sum at most two. Adding the lower bounds for the surviving minors gives
$$
G\,p^{4/h}\le 2L^3 .
$$

Hence $G^h p^4>(2L^3)^h$ excludes $L$ transpositions. Replacing $G$ by $L(L-1)(L-3)/6$ gives the simpler sufficient inequality $p^{4/h}>12L^2/((L-1)(L-3))$. At length 512 the integer test excludes 56 pairs at the named 237-bit prime, 17 pairs at either Pasta prime, and 16 at the BLS12-381 scalar prime. A conjugation by the coset scalar transfers the same conclusions to all smooth cosets of that size. [Joint involution theorem](../../../ArkLib/Research/ProximityGap/Frontier/JointPairThreshold.lean) · [Four length-512 fields](../../../ArkLib/Research/ProximityGap/Frontier/JointPair512.lean) · [Dyadic pair-sum cancellation](../../../ArkLib/Research/ProximityGap/Frontier/DyadicChordEnergy.lean)

## Seven matches for an arbitrary projectivity

Use the seven rows $(1,x_i,y_i,x_iy_i)$ in a configuration of matched distinct sources and targets. Any three rows are independent. For example, if the first three columns are linearly dependent, the three pairs obey $y=Ax+B$ with $A\ne0$ by distinctness. Adding $xy$ then gives the independent three columns $1,x,x^2$ after elementary column operations. Every fourth row in their span expresses a match on the unique projectivity through the three marked pairs.

If the complex matrix has rank four, at least 20 of the 35 four-row determinants are nonzero. Let $r$ be the largest number of the seven rows in a three-dimensional linear subspace. If $r=6$ or $r=5$, taking three of those rows and one outside gives $\binom r3(7-r)=20$. If $r\le4$, a dependent four-set cannot share any triple with another dependent four-set, so at most $\lfloor\binom73/4\rfloor=8$ four-sets are dependent. This proves the lower bound in every rank-four case.

In every embedding all four columns have squared norm seven. Cauchy–Binet and Hadamard bound the sum of squared absolute values of the 35 minors by $7^4=2401$. Rank four would force $20 p^{4/h}\le2401$. Thus
$$
20^h p^4 > 2401^h
$$
forces rank at most three, so a single complex projectivity matches all seven pairs. Complex dyadic rigidity makes it a scaling or reciprocal scaling. Equality of the corresponding exponent differences or sums transfers this conclusion back to the original prime field. At order 256 the test holds whenever $p\ge 2^{222}$, including the named 237-bit witness and both Pasta fields. [Absolute seven-site rigidity](../../../ArkLib/Research/ProximityGap/Frontier/DyadicSevenProjectivities.lean) · [Reconstruction from three pairs](../../../ArkLib/Research/ProximityGap/Frontier/SevenSiteTransfer.lean)
