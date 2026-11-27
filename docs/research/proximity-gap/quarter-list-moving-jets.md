# Low-degree parameters and quarter-rate list safety

Every closed ball at **536,870,914 errors** on the second named quarter-rate domain has at most $2^{31}$ codewords, at every positive interleaving width. The proof covers every injective grid of this length in the named field. [Exact contact arithmetic](../../../scripts/probes/probe_quarter_list_moving_jets.py)

Set $n=2^{30}$, $d=n/4-1$, and work over the algebraic closure of the second named field. Suppose a quarter-rate list contains $2n+1$ words with $t=2d$ agreements to one received word. Identify each interleaved symbol with one element of a field extension, if necessary. The complementary-pair argument supplies at least $M=1,072,766,345$ distinct polynomials $U_i$ of degree at most $u=1538$, a monic nonzero $A$, a polynomial $B$ coprime to $A$, and one $N$ of degree at most $n-4$ with at least $n-3080$ distinct physical roots. Put $S_0=f_0+g_0$ and $P_0=f_0g_0$ for one of the pairs. Then
$$
 N=B^2-AS_0B+A^2P_0,\qquad
 (S_0+A U_i)^2-4(P_0+B U_i)=(f_i-g_i)^2 .
$$
The polynomial $N$ has at least $n-6156$ simple finite roots, since twice the number of distinct physical roots minus its degree bounds the number of simple ones from below. It has at most 3076 distinct multiple roots. [Pair extraction](complementary-list-pencil.md)

## Contacts on the double cover

On the smooth projective curve $C$ with function field $k(X,Y)$, $Y^2=N$, let
$$
 H=(2B-AS_0+2Y)/A^2,\qquad V=dH/dX .
$$
The hyperelliptic involution $\sigma$ sends $Y$ to $-Y$. Write $D$ for the total pole order of $H$. The distinct maps $H,H\circ\sigma$ to the projective line coincide at no more than $2D$ points counted with multiplicity, by their homogeneous cross-difference. They coincide at all branch points, including the simple roots above. Thus $D\ge(n-6156)/2$. The degree of the pole divisor of $V$ is at most $4D$. Indeed $dH$ has poles of total order at most $2D$, and the zeros of $dX$ are simple finite branch points of the tame double cover, numbering at most $2D$. Norms satisfy
$$
       (H-U_i)(H\circ\sigma-U_i)=(f_i-g_i)^2/A^2 .
$$
At a simple finite root of $N$, $A$ is a unit by coprimality. If $H-U_i$ vanished there, its order would be one: the rational part has an expansion in $X-x$, while the term $2Y/A^2$ has order one in a local square-root uniformizer. At a ramified point the base valuation of the norm equals the valuation upstairs, contradicting the square identity. Thus none of these contact divisors contains a simple-root branch point.

Let $F(X,Z,W)$ have degrees at most $e=160\cdot38u$, 30 and 8 respectively. Suppose $F(X,U_i,U_i')=0$ identically for at least $r=159$ distinct parameters. Then $F(X,H,V)=0$. Otherwise its pole degree is at most $2e+62D$. We show its zero degree exceeds that bound.

Choose exactly $r$ of the parameters. Discard those for which $H-U_i$ has a zero at infinity. This costs at most two indices: there are at most two places above infinity and a nonzero polynomial $U_i-U_j$ cannot vanish at either. Each remaining $H-U_i$ has total zero order at least $D-2u$ by the pole-degree triangle inequality. At a finite contact place let $a_i>0$ denote its order. Odd contact orders occur only above unramified places, by the square norm. At such a point the conjugate place must also have odd valuation. It is either a pole of $H$ or another zero of $H-U_i$. In the latter case $H=H\circ\sigma$. Hence the odd contacts, taken as a union of points, occupy at most $3D$ places. Counting them with the index included adds at most $J=2u\binom r2$, since common zeros of $H-U_i,H-U_j$ contribute at most $2u$ total minimum order for each pair.

At a finite contact both $H$ and $V$ are regular. At unramified places, $\operatorname{ord}(V-U_i')\ge a_i-1$ by differentiation. At a finite branch contact $a_i\ge2$ and dividing by $dX$ costs one more order. Consequently substitution in $F$ gives order at least $a_i-1$ at unramified places and at least $a_i-2$ at branch contacts. There are at most 3076 possible finite branch contacts per index, all over multiple roots of $N$. The inequality $a_i-1\ge(a_i-\mathbf1_{a_i\ {\rm odd}})/2$ and one more subtraction of $J$ to pass from a sum to a maximum at shared contact sites give the lower bound
$$
 \frac{(r-2)(D-2u)-3D-J}{2}-3076r-J.
$$
This exceeds $2e+62D$ even at $D=(n-6156)/2$, and its slope in $D$ is larger. This proves the claim. No lower bound on the number of distinct contacts of an individual section is required.

## Interpolating the jets

Over $k(X)$ evaluate the 279 monomials $Z^jW^h$, $0\le j\le30$, $0\le h\le8$, at the distinct points $(U_i,U_i')$. Each entry is a polynomial in $X$ of degree at most $38u$. The resulting matrix has rank below 160. Otherwise choose 160 independent columns including the constant and 160 rows giving a nonsingular square matrix. The cofactors give one interpolation polynomial per selected row, zero on the other 159 and equal to the determinant on that row. The sum of these polynomials equals the same nonzero determinant as a polynomial in $Z,W$: both belong to the chosen column span and have those values on the unisolvent rows. Each summand has coefficient degrees at most $e$ and must vanish at $(H,V)$ by the contact estimate. Their sum cannot vanish.

Take a maximal independent set of columns and adjoin one dependent column. Cramer's rule on independent rows gives a nonzero $F$ with the same degree bounds vanishing on *all* parameter jets. Factor over $k[X,Z,W]$, ignoring factors in $X$ only, which are units over $k(X)$. There are at most 38 nonconstant factors in $Z,W$ counted with multiplicity. One irreducible factor $G$ therefore contains at least $\lceil M/38\rceil$ of the jets. Its separate degree bounds are inherited from $F$. Those jets include 159, so $G(X,H,V)=0$ as well. It must involve $W$, since a polynomial in $Z$ alone of degree at most 30 cannot vanish at so many distinct parameters in $k(X)$.

Moreover $G_W(X,H,V)\ne0$. Over $k(X,Z)$, $G$ is irreducible of positive $W$-degree less than the characteristic; its resultant with $G_W$ is nonzero. This resultant has $X$-degree at most $15e<D$. Any nonzero polynomial relation in $X,H$ must have $X$-degree at least $D$, because $k(X,H)=k(C)$ and $[k(C):k(H)]=D$. The resultant cannot vanish at $H$.

The differential argument now bounds the number of low-degree parameter jets on this one factor by 4,443,188, less than $\lceil M/38\rceil$. This contradicts the assumed list. [Differentiating on the irreducible factor](quarter-list-jet-derivation.md)
