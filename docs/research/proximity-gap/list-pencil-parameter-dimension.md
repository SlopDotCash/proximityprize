# How many split members can lie in a low-dimensional parameter space?

At **536,870,914 quarter-rate errors** on the second prime, every hypothetical over-budget list forces a pencil of split quadratics. Its polynomial parameters have affine span of dimension **at least ten** over the algebraic closure of the alphabet field. In particular at most 64 of its distinct parameters can lie in an affine plane, 512 in an affine three-space and 134,228,107 in an affine nine-space. The matching supplies at least 1,072,766,345 distinct parameters. [Extraction and homogeneous normalization](complementary-list-pencil.md) · [Exact counts and small-field checks](../../../scripts/probes/probe_list_pencil_dimension.py)

Write $d=2^{28}-1$ and use the coprime binary forms $A_*,B_*$ from the reconstruction. Their degrees are $d-\ell,2d-\ell$, with $\ell\le1538$. Write $S_0,P_0$ for the homogeneous sum and product forms of degrees $d,2d$. The parameter $U$ is homogeneous of degree $\ell$. Indeed both $A U$ and $B U$ in affine coordinates obey the respective degree bounds $d,2d$, giving $\deg U\le\min(d-\deg A,2d-\deg B)=\ell$, with a zero coefficient imposing no restriction. Define
$$
 S=S_0+A_*U,\qquad P=P_0+B_*U,\qquad J(U)=S^2-4P,\qquad
 N_*=B_*^2-A_*B_*S_0+A_*^2P_0 .
$$
A split member gives a square $J(U)=(f-g)^2$. The form $N_*$ of degree $4d-2\ell$ has at least $2^{30}-3080$ distinct roots. Its sum of multiplicities in excess of one over the projective line is therefore at most $3076-2\ell$. The identity
$$
              A_*^2 J(U)=(A_*S-2B_*)^2-4N_*
$$
also implies $J(U)$ cannot vanish identically, since $N_*$ has a simple root. All arguments below are over the algebraic closure of the coefficient field.

## A varying family cannot keep many repeated roots

Take any positive-dimensional irreducible family of distinct parameters in an affine space of binary forms $U$. At its generic point, with function field $K$, some derivation over the constants makes $\dot U\ne0$. Indeed the coefficients of $U$ generate $K$, which has positive transcendence degree and a separating transcendence basis over the perfect constant field. The splitting field of $J(U)$ is separable over $K$, because every irreducible polynomial involved has degree at most $2d<p$. Extend the derivation there.

At a root of multiplicity $m$ of $J(U)$, differentiating its factorization with respect to the family parameter shows that $\dot J$ vanishes to order at least $m-1$. This works in a local affine coordinate at infinity as well. As $\dot J=2(A_* S-2B_*)\dot U$, all excess multiplicities together contribute at most $\ell$ from $\dot U$, plus the sum over the roots of
$$
          \min\{m-1,\operatorname{ord}(A_* S-2B_*)\}.
$$
For a positive summand, $A_*$ is nonzero there by coprimality. If $b=\operatorname{ord}(A_* S-2B_*)\ge1$, the identity for $N_*$ gives $\operatorname{ord}N_*\ge\min(2b,m)\ge1+\min(m-1,b)$. The generic excess multiplicity of $J(U)$ is consequently at most $\ell+(3076-2\ell)\le3076$.

## Isolated square points and their multiplicities

In any affine $r$-space of parameters the locus of $J(U)$ with total excess at least 3077 has dimension zero, by the preceding argument on each possible positive-dimensional component. Explicit equations are obtained from the two homogeneous partial derivatives of $J$. Each has degree $s=2d-1$. The corank of their $2s$-row Sylvester matrix is the degree of their homogeneous gcd, exactly the excess multiplicity because $p>2d$. This follows also from the map $(G,H)\mapsto GJ_X+HJ_Z$ on forms of degree $s-1$. The kernel is given by multiples of the primitive syzygy after the gcd is removed. Taking the minors of size $k=2s-3076$ therefore cuts out precisely this locus.

Each minor has parameter degree at most $2k$. At a square point the two gradients share the degree-$d$ square root. The matrix rank is at most $2s-d$, so every such minor vanishes there to order at least $k-(2s-d)=d-3076$. To see the order directly, expand each column into its value and its variation. Every nonzero determinant term must use at least $d-3076$ varying columns.

Choose $r$ generic linear combinations of the minors. They have zero-dimensional common affine locus: at each step a generic combination avoids vanishing identically on every positive-dimensional component, since the full common zero set is finite. Affine Bézout bounds the sum of isolated intersection multiplicities by $(2k)^r$, including when there are intersections at infinity. At a square point their local intersection multiplicity is at least $(d-3076)^r$. Indeed their parameter ideal lies in that power of the maximal ideal, so its Hilbert–Samuel multiplicity is at least that of the maximal-ideal power. The local ring is regular, so for a parameter ideal this multiplicity equals its colength. Thus the number of square points in the affine space is at most
$$
          \left\lfloor\left(\frac{8d-6156}{d-3076}\right)^r\right\rfloor .
$$
The bound counts geometric points and permits repeated roots of the square root. At $r=9$ it is strictly below the forced matching size. It allows that many points at $r=10$. The [moving-section argument](quarter-list-moving-jets.md) also handles the larger parameter spaces.
