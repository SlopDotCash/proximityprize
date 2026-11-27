# Six-site fibers of a septic on the second-prime 32-point subgroup

Let $H=\mu_{32}(\mathbb F_p)$, where $p=730750818665451459101842416358141509841924915201$ is the second named prime. Suppose a reduced degree-seven rational map $R$ over this field has at least three distinct fibers meeting $H$ in at least six points each. No nonidentity dihedral symmetry $s$ of $H$ can satisfy $R(sx)=b(R(x))$ throughout $H$ for a target projectivity $b$. The half-rate tetrahedron construction on this quotient would need **four** such fibers to improve its earlier production ceiling of 387,740,104 errors. Combined with the existing quintic and sextic results, every remaining 32-node reparameterization that could improve that ceiling has trivial dihedral equivariance. Arbitrary rational maps on this quotient remain possible. [Production reduction and sextic analysis](second-prime-tetrahedron.md#rational-quotients-on-sixteen-and-thirty-two-nodes)

## Reducing to a six-element support and one parameter

Homogeneous cross multiplication extends the covariance identity to the projective line. Its degree is at most fourteen, and the 32 input points are distinct. A nonidentity dyadic rotation has the half turn as a power. Reflections already have order two. In either case the resulting target action squares to the identity since $R$ is nonconstant. If the target action were the identity, changing source coordinates to make the involution $y\mapsto-y$ would give a rational function in $y^2$, of even degree. Indeed the even rational functions are precisely the fixed field $\mathbb F_p(y^2)$ of this quadratic extension. We can therefore assume a nonidentity target involution.

There are at most two fixed target values. One large fiber is exchanged with another. Send their target values to zero and infinity. The two corresponding divisors, including multiplicities and points outside the subgroup, are images of each other under the source involution. After scaling the target the resulting degree-seven function is $F(y)/F(-y)$, where $F$ has degree seven and $F(0)\ne0$. Neither fixed point $0,\infty$ can be a zero or pole, since the corresponding fibers are disjoint. The values at these two fixed points are therefore $1,-1$, respectively.

Choose any six points $A$ of the zero fiber on the transformed board. They come from six distinct nonfixed source pairs, and
\[
 F(y)=\prod_{u\in A}(y-u)(y-\lambda)
\]
up to a nonzero constant. The remaining root $\lambda$ belongs to the base field. A reduced septic has $\lambda\ne0$ and $-\lambda\notin A$. Write $h_x=\prod_{u\in A}(x-u)/\prod_{u\in A}(-x-u)$. At the remaining nonfixed sites the value is
\[
                  T_\lambda(x)=h_x(\lambda-x)/(\lambda+x).
\]

## Recovering every candidate

Take one representative from each remaining source pair. A third large fiber with value $v\notin\{0,\infty\}$ forces at least three of these representatives to have the same value. If $v\ne v^{-1}$, the six sites are distributed between the representatives and their negatives, and passing to negatives replaces $v$ by $v^{-1}$. If $v=v^{-1}$, the fiber contains whole nonfixed pairs and at most one fixed site, since the two fixed source points have different values. It again contains at least three complete pairs.

For distinct representatives $x_i,x_j$ the condition $T_\lambda(x_i)=T_\lambda(x_j)$ gives
\[
 (h_i-h_j)(\lambda^2-x_i x_j)+(h_i+h_j)(x_j-x_i)\lambda=0 .
\]
When $h_i=h_j$, there is no finite nonzero solution because $p$ is odd and both $h_i$ and $x_i-x_j$ are nonzero. Otherwise divide by $h_i-h_j$ and write the result as $\lambda^2+B_{ij}\lambda+D_{ij}=0$. For a third representative $x_k$, the constants $D_{ij}=-x_i x_j$ and $D_{ik}=-x_i x_k$ differ. If the two linear coefficients agree the quadratics have no common root. Otherwise subtraction gives the only candidate $(D_{ik}-D_{ij})/(B_{ij}-B_{ik})$. The verifier substitutes it back into the first quadratic and evaluates all surviving reduced maps directly on the 32 points.

For the half turn, use $y=x$. A reflection is $x\mapsto z^{2a}/x$ with $z$ a primitive 64th root. Conjugation by rotations reduces $a$ to 0 or 1. The coordinate $y=(x-z^a)/(x+z^a)$ sends that reflection to negation, with a zero denominator representing infinity. All rotations and reflections preserve the half-turn search. For each fixed reflection the two rotations $x\mapsto\pm x$ and their two compositions with the reflection preserve its search. Taking one support per orbit under these actions preserves existence.

| Source involution | Six-site support orbits | Reduced maps recovered with a third six-site fiber |
|---|---:|---:|
| Half turn | 8,190 | 0 |
| Reflection fixing two board sites | 80,220 | 0 |
| Reflection fixing no board sites | 128,352 | 0 |

Run `python3 scripts/probes/probe_septic_tetrahedron_symmetry.py` from the repository root. The integer search uses only the Python standard library. A positive control recovers the missing seventh root for $y^7$ on $\mu_{42}(\mathbb F_{337})$, which has six seven-site fibers. A second control compares all recovered parameters against direct enumeration in $\mathbb F_{97}$. [Exact verifier](../../../scripts/probes/probe_septic_tetrahedron_symmetry.py)
