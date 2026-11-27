# Reconstructing two split fibers from the first fiber and the holes

At the first-prime quarter-rate successor, fix only one candidate fiber of size \(D=268435454\) and the \(268435462\) sites outside all three fibers. There are **at most two** ways to partition the remaining \(2D\) sites into an unordered pair of fibers. Both can be recovered from the critical polynomial below. At odd degree there is **at most one** completion. This applies to each degree-\(268435455\) pencil required at the first-prime half-rate successor. [Quarter-rate equivalence](quarter-successor-split-pencil.md) · [Half-rate fiber patterns](half-four-fiber-parity.md)

Two completions of the same quarter-rate data force a rational map \(T\) of degree \(134217727\) with six full fibers in the actual subgroup. After a target normalization their values are \(0,\infty,1+r,1-r,-1+r,-1-r\) for \(r\) in the ground field. Each part of the first completion meets each part of the second in exactly \(134217727\) sites. In particular, any completion whose map admits no quadratic outer factor is unique for these data. [Remaining production stages](quarter-split-wronskian-suborbits.md)

The reconstruction checks finitely many exact polynomial identities for each choice of fixed fiber and holes. The remaining choice of these sets at length \(2^{30}\) is exponential. Existence at \(447392428\) errors and the production threshold remain open. [Lean polynomial lemmas](../../../ArkLib/Research/ProximityGap/Frontier/SplitPencilSquareCompletions.lean) · [Executable reconstruction and independent census](../../../scripts/probes/probe_split_pencil_square_completions.py)

## The square test and the two-candidate bound

Work over a field of characteristic different from two, with a finite set of distinct evaluation sites. Fix disjoint sets \(Z,U\) of sizes \(d,2d\) where \(d\ge1\). Write \(A=L_Z\) and \(F=L_U\) for their monic locators. On \(H=\mu_n\), if \(K\) is the monic hole locator, then \(F=(X^n-1)/(AK)\).

An unordered completion of \(U\) is equivalent to a nonzero scalar \(\lambda\) for which
\[
 W^2=A^2-\lambda F. \tag{1}
\]
Indeed the monic locators of the two parts can be independently scaled to \(B,C\) with \(A=B+C\). Then \(W=B-C\) and \(4BC=\lambda F\). Conversely \((A-W)(A+W)=\lambda F\). The factors each have degree at most \(d\), so both have degree exactly \(d\). Their roots partition the squarefree \(F\). Changing the sign of \(W\) interchanges the two parts. Distinct completions give distinct \(\lambda\), since the square root is unique up to sign. These arguments work over the ground field. Even a geometric completion yields two locators over that field because all the sites are rational and their linear dependence descends.

Choose \(a\in Z\) and change coordinates to \(X=a+1/Y\), homogenizing \(A,W\) to degree \(d\) and \(F\) to degree \(2d\). In these coordinates \(A\) has degree \(d-1\), \(F\) degree \(2d\), and every candidate \(W\) degree \(d\) because \(W(a)^2=-\lambda F(a)\ne0\) in the original coordinates. Retain the same letters for the transformed polynomials. Set
\[
 J=AF'-2A'F .
\]
It has degree \(3d-2\), since the two leading derivative terms leave a factor \(2\). Differentiating (1) gives \(\lambda J=2W(A'W-AW')\), so \(W\mid J\). Distinct parameters have coprime square roots since a common zero would force both \(F\) and \(A\) to vanish. Three square roots would contribute total degree \(3d>\deg J\). The Lean theorem proves this cap directly from the transformed polynomial hypotheses.

For computation suppose \(p>3d-2\) as at production. Form the one-variable resultant
\[
 H(v)=\operatorname{Res}_{Y}(J,F-vA^2).
\]
It has degree \(3d-2\) because \(A\) has no zero at a root of \(J\). Indeed \(A\) has simple roots disjoint from \(F\). For a valid parameter every root of \(W\), counted with its multiplicity, is a root of \(J\) with at least that multiplicity and maps under \(F/A^2\) to \(v=1/\lambda\). The resultant product formula gives \((v-1/\lambda)^d\mid H(v)\).

The squarefree part of \(\gcd(H,H',\ldots,H^{(d-1)})\) therefore supplies at most two candidate values. Test (1) for each nonzero rational candidate. For example, expand at any \(\beta\in U\), choose \(W(\beta)=A(\beta)\ne0\), and recover the remaining \(d\) coefficients in order by dividing by \(2W(\beta)\). Squaring the result checks the entire identity. The method uses polynomially many field operations per selected \(Z,U\) and one quadratic root calculation. At the production quarter successor the critical degree is \(805306360\).

## Two solutions determine a common right factor

Suppose (1) holds at distinct parameters \(\lambda_1,\lambda_2\). Write \(t_j=W_j/A\) and \(f=F/A^2\). The value \(r=W_1(a)/W_2(a)\) at any root \(a\) of \(A\), in the original coordinates, satisfies \(r^2=\lambda_1/\lambda_2\). Thus \(r\ne0,1,-1\) and
\[
 T=t_1+r t_2,\qquad T'=t_1-r t_2,\qquad TT'=1-r^2 .
\]
Each \(a\in Z\) is a simple pole for both \(t_j\). At such a point exactly one of \(T,T'\) has a simple pole. They cannot both be regular because their sum has a pole, and they cannot both have a pole because their product is a nonzero constant. Their poles are all in \(Z\), and \(T'=(1-r^2)/T\). Consequently \(Z\) is the disjoint union of the complete simple zero and pole fibers of \(T\). This gives \(d=2\deg T\), proving uniqueness for odd \(d\).

At a root of \(F\) each \(t_j\) is \(1\) or \(-1\). The four joint sign patterns give the four distinct \(T\) values \(\pm1\pm r\). The \(2d=4\deg T\) root sites fill all four fibers, proving the intersection counts. Conversely, if a degree-\(d/2\) map \(T\) has the six stated full fibers, the rational functions
\[
 t_1=\frac{T+(1-r^2)/T}{2},\qquad
 t_2=\frac{T-(1-r^2)/T}{2r}
\]
have simple poles exactly on the prescribed \(Z\). The two functions \(A t_j\) are polynomials of degree at most \(d\), since all poles of \(t_j\) are finite and are cleared by \(A\). Their squares yield (1) at distinct nonzero parameters because \(1-t_1^2=r^2(1-t_2^2)\), and both sides vanish at all \(2d\) sites of \(U\). The original split-pencil map for each completion differs from \(t_j\) by a target Möbius transformation, so \(T\) is a common right factor.

At both named production fields the bound of two is attained at \(d=n/8\). On the order-16 quotient choose exponents \(0,8\) for \(Z\) and \(1,15,2,14\) for \(U\). The coordinate \((Y-1)/(Y+1)\) sends \(Z\) to \(0,\infty\), and inversion of \(Y\) negates this coordinate. Its other four values are \(\pm u,\pm v\) with \(u\ne\pm v\). Multiplication by \(2/(u+v)\) gives the required \(\pm1\pm r\). Pulling back by \(Y=X^{n/16}\) gives the claimed degree on all \(n\) sites.

## An arithmetic test when the selected sets have a symmetry

If \(Z,U\) are antipodally closed in a dyadic grid, both locators are even. Equation (1) forces \(W(-X)=W(X)\) or \(W(-X)=-W(X)\). In the first case the completion descends by \(X^2\). In the second case \(d\) is even and the odd polynomial \(W\) has degree less than \(d\), forcing \(\lambda=1\) by leading coefficients. Its zero at the origin also forces \(F(0)=A(0)^2\). Writing \(A=A_0(X^2)\), \(F=F_0(X^2)\), this case occurs precisely if \((A_0^2-F_0)/Y\) is a polynomial square in \(Y\). At the production degree, \(d/2\) is odd, hence there is at most one descended completion. In particular, when \(F(0)\ne A(0)^2\), all three fibers of any completion descend individually by squaring.

For a scaled reflection \(I(X)=b/X\) preserving \(Z,U\), the rational function \(f=F/A^2\) satisfies \(f\circ I=f(0) f\) and \(f(0)=\pm1\). This follows from the invariant divisors and \(f(\infty)=1\). If \(U\) contains both reflection-fixed points, they are simple zeros of \(f\). The derivative of \(I\) at each is \(-1\), so \(f(0)=-1\). Any solution \(1-\lambda f=t^2\) then gives \(1+\lambda f=(t\circ I)^2\). Thus a single completion already forces a second. Here \(r^2=-1\) and scaling the four nonzero finite target values converts them to \(\{1,-1,i,-i\}\), where \(i^2=-1\). A pencil with these reflection-invariant data at the production quarter successor must therefore factor through a degree-\(134217727\) map with full fibers at \(0,\infty,1,-1,i,-i\), up to target coordinates.

## A cubic-cover test without knowing any of the colors

At the first-prime quarter successor, only the occupied set \(B\) of \(3d=805306362\) sites is needed for the following necessary condition. Put \(G_B=\prod_{b\in B}(X-b)\). The zeta numerator of the smooth projective curve \(C_B:Y^3=G_B(X)\) must be divisible in \(\mathbb Z[T]\) by \(1+pT^2\). In particular \(p+1\) must divide \(\#\operatorname{Jac}(C_B)(\mathbb F_p)\). This test allows every partition of \(B\) and imposes no symmetry condition.

Indeed let \(P,Q,P-Q\) be the three scaled locators and write \(P Q(P-Q)=cG_B\). The functions \(z=P/Q\) and \(w=Y/Q\) satisfy \(cw^3=z(z-1)\). Thus \(C_B\) maps to the smooth genus-one curve \(E_c:cw^3=z(z-1)\). Its cyclic triple cover is totally ramified over the three branch values \(0,1,\infty\), and its rational point \((0,0)\) supplies an origin. Comparing the projections to the \(X\) and \(z\) lines shows the map has degree \(d\). At the first prime \(p\equiv2\pmod3\), so cubing permutes the field. There is one rational point above each finite \(z\), and one above infinity. Hence the elliptic trace is zero. Pullback and norm on Jacobians compose to multiplication by \(d\), so the image of the elliptic Jacobian is an abelian subvariety up to isogeny. Its Frobenius factor gives the test. This establishes a geometric requirement at every such prime and degree. It leaves the existence of a qualifying production set \(B\) open.

The condition is an **exact** uncolored pencil test in the six-site case \(p=17,\ H=\mathbb F_{17}^{\times},\ d=2\). Of the \(\binom{16}{6}=8008\) occupied sets, **5,896** pass the factor test and have a partition into three two-point fibers; **2,112** fail the test and admit none. For example \(\{1,2,3,4,5,7\}\) has no completion with any of its possible colors fixed. The verifier enumerates all six-subsets, grouping them into ten projective classes by sending each ordered triple to \(\infty,0,1\). Projective equivalence preserves the pencil of binary quadratics and the isomorphism class of \(C_B\): changing the source variable changes the sextic by a sixth power of a linear denominator and a ground-field scalar, itself a cube. On each representative the program checks collinearity of the three monic quadratic locators independently of the point counts.

For these six-site curves the genus is four by Riemann–Hurwitz. All odd-extension point counts equal \(17^j+1\) because cubing is bijective there, including at the monic sextic's unramified fiber at infinity where exactly one cube root of unity is rational. The functional equation therefore gives zeta numerator \(1+a_2T^2+a_4T^4+p^2a_2T^6+p^4T^8\). From the point counts \(N_2,N_4\) over the quadratic and quartic extensions, Newton's identities give \(2a_2=N_2-p^2-1\), \(4a_4=N_4-p^4-1+2a_2^2\). The divisibility condition is precisely \(2p^2-2pa_2+a_4=0\). The program computes both point counts by enumerating the whole field and verifies its multiplicative generator covers every nonzero element in each extension. [Independent cubic-cover and pencil census](../../../scripts/probes/probe_split_pencil_cubic_cover.py)

## An elliptic trace test on the union of the three fibers

Continue with the reflection that fixes two sites in \(U\), and work over the first named prime field. The following necessary test uses only the union \(B=Z\cup U\), with no assignment of its sites to colors. Let \(G_B=\prod_{x\in B}(X-x)\), and put \(g=(|B|-2)/2=402653180\). Write \(c_j=[X^j]G_B^{(p-1)/2}\), taking missing coefficients as zero. Form the \(g\)-square matrix \(M_{ij}=c_{pi-j}\) over \(\mathbb F_p\), with indices \(1\le i,j\le g\). At least one of the two matrices
\[
 M-1201616412679574549121762\,I,\qquad
 M+1201616412679574549121762\,I
\]
must have nullity at least two. The Jacobian of \(C:Y^2=G_B(X)\) must contain two copies up to isogeny of the same quadratic twist of \(E:y^2=x^3-4x^2+2x\). Consequently its Frobenius polynomial in the zeta-function convention has \((1-tT+pT^2)^2\) or \((1+tT+pT^2)^2\) as a factor, for \(t=1201616412679574549121762\).

To see this, normalize the six target values of the degree-\(m=134217727\) rational function to \(0,\infty,\pm1,\pm i\). Call the normalized function \(s\). All points of these fibers are simple, finite and occupy exactly \(B\). Therefore \(s^5-s\) has odd valuation precisely at \(B\): one at its four finite nonzero target fibers and at its zero fiber, and minus five at its pole fiber. The divisor of \((s^5-s)/G_B\) is even. Factoring its numerator and denominator over the ground field shows it is a nonzero constant times a rational square there. The curve \(C\) thus maps to a quadratic twist of \(v^2=s^5-s\) by sending the first coordinate to \(s(X)\). The map has degree \(m\), by comparing the two hyperelliptic projections, and is separable since \(p>m\).

Choose \(\xi\in\mathbb F_p\) with \(\xi^4=-1\), available since \(8\mid p-1\). After setting \(s=\xi u\) and incorporating the constant into the twist, the target takes the form \(v^2=c(u^5+u)\) for one \(c\in\mathbb F_p^\times\). It has two elliptic quotients. Put \(z=u+1/u\) and \(w_\pm=v(u\pm1)/u^2\). Direct multiplication gives \(w_\pm^2=c(z^2-2)(z\pm2)\). The plus quotient, translated by \(x=z+2\), has equation \(w^2=c(x^3-4x^2+2x)\). The minus quotient is isomorphic to the plus one over the same field via \((z,w)\mapsto(-z,iw)\). Their invariant differentials \(dz/w_\pm\) pull back to \((u\mp1)du/v\), which are independent. Hence the two quotient maps give a separable isogeny from the genus-two Jacobian to the product of these elliptic curves. Pulling back along \(C\) injects these two independent differentials and supplies the abelian factors up to isogeny. [Lean identities for the quotient equations](../../../ArkLib/Research/ProximityGap/Frontier/SplitPencilSquareCompletions.lean)

On a smooth elliptic curve \(v^2=cP(u)\), the Cartier operator on \(du/v\) acts by the coefficient of \(u^{p-1}\) in \((cP)^{(p-1)/2}\). This coefficient is the trace modulo \(p\): sum the quadratic character of \(cP(u)\) over the field, using \(\sum_u u^{p-1}=-1\) and \(\deg P=3\). Pullback commutes with Cartier for these separable maps. On \(X^{j-1}dX/Y\) on \(C\), write the differential as \(Y^{-p}X^{j-1}G_B^{(p-1)/2}dX\). Extract the powers congruent to \(p-1\) modulo \(p\) to obtain the matrix above. Thus both differentials in the pullback have the same eigenvalue, equal to the trace or its negative according to the twist.

The [integer certificate](../../../scripts/probes/probe_split_pencil_square_completions.py) checks the trace of the untwisted \(E\) by elliptic-curve addition. Set \(q=52447244997910193717739548112237131\) and take the point \((1,125829621549097067457234094028236226857884909488)\). The integer \(N=p+1-t=6966531976032q\) annihilates this point, while \(N/q\) does not. Pocklington certificates prove \(q\) prime. Consequently \(q\) divides the true group order. The integer \(N\) lies in Hasse's interval and \(q>4\sqrt p\), so \(N\) is its unique multiple there. The verifier also counts the two elliptic quotients and the genus-two curve directly on every smooth member \(v^2=c(u^5+a u^3+u)\) over \(\mathbb F_{17}\) for both twist classes. The verifier constructs the Cartier matrices for the degree-one, two and three pullbacks of \(s=(X-3)/(3X-1)\) by \(X\mapsto X^e\) over \(\mathbb F_{17}\) and checks the required eigenspace dimensions directly. The isogeny and Cartier arguments are written proofs. No particular production union \(B\) is assumed to pass or fail this test.

## Finite verification

The independent census groups monic \(d\)-site locators by the projective direction of their coefficient vector from the fixed locator. Two locators give a completion exactly when their vectors lie on the same line. Multiplication by a grid element transports the calculation between fixed-fiber orbit representatives. The entries count all ordered choices of \(Z,U\), with the complementary two fibers unordered.

| Field | Grid order | \(d\) | No completion | One | Two |
| --- | ---: | ---: | ---: | ---: | ---: |
| \(\mathbb F_{17}\) | 8 | 2 | 312 | 96 | 12 |
| \(\mathbb F_{17}\) | 16 | 2 | 96,096 | 22,176 | 1,848 |
| \(\mathbb F_{17}\) | 16 | 3 | 912,384 | 48,576 | 0 |
| Each designated prime | 16 | 2 | 116,304 | 3,648 | 168 |
| Each designated prime | 16 | 3 | 960,768 | 192 | 0 |

Run the full check with the command below to compare the resultant reconstruction against every orbit representative in every table row. It also checks intersection sizes and the order-16 seed of the production construction.

~~~sh
python3 -BO scripts/probes/probe_split_pencil_square_completions.py --full
~~~
