# A fixed off-domain apolar locator at the first step beyond unique decoding

Let $H=\mu_{4h}$ in a finite field with $h\ge8$, and let $k=2h$. At $e=h+1$ errors there is a single received pair with **exactly $3h+2$ MCA-bad scalars**. At each of these scalars the unique projective degree-$h$ apolar locator is $Y^h$. Its only root is outside the evaluation domain, and the domain vanisher times its divided polynomial is nonzero at that root. Thus the vanishing used by the sharp predecessor proof can fail simultaneously on $3h+2$ actual bad scalars.

For $h=2^{28}$, this gives 805,306,370 bad scalars at 268,435,457 errors on each of the two named production fields. Their respective budgets are 1,073,741,824 and 2,147,483,648. This construction leaves both operational threshold brackets open.

## Received pair and exact count

Partition $H$ into the four cosets $A_1,A_2,A_3,A_4$ of $\mu_h$. Write $a_i=y^h$ on $A_i$. Choose two distinct elements of $A_4$, forming $D$. For $i=1,2,3$ put $C_i=A_i\cup D$, $B_i=H\setminus C_i$ and $V_i(Y)=\prod_{y\in B_i}(Y-y)$. Write $G_U$ for the monic vanisher of any finite set $U$. Use the following rows on $H$:
$$
u(y)=yV_1(y)/y^h,\qquad v(y)=-V_1(y)/y^h.
$$
Since $G_{C_i}=(Y^h-a_i)G_D$ and $V_iG_{C_i}=G_H$, all three $V_i$ are unit scalar multiples of one another modulo $Y^h$. In fact $a_iV_i\equiv a_1V_1\pmod{Y^h}$. Put $b_i=a_i/a_1$ and $L_i=(V_1-b_iV_i)/Y^h$. The numerator has degree at most $3h-2$, hence $\deg L_i\le2h-2$ when nonzero.

For every $t\in C_i$, the polynomial $P_{i,t}=(Y-t)L_i$ has degree below $k$. Its residual is
$$
u(y)+t v(y)-P_{i,t}(y)=b_i(y-t)V_i(y)/y^h.
$$
The exact error set is $C_i\setminus\{t\}$, of size $h+1$. The agreement set $B_i\cup\{t\}$ has no joint explanation. On $B_i$ the rows agree with $YL_i,-L_i$, and $|B_i|=3h-2\ge k$ forces those choices for any joint explanation. At $t$ the second row differs from $-L_i(t)$ by $-b_iV_i(t)/t^h\ne0$.

Conversely, suppose a polynomial $P$ of degree below $2h$ agrees with $u+tv$ except on $E$, where $|E|\le h+1$. The polynomial $N=(Y-t)V_1-Y^hP$ has degree at most $3h-1$. It is nonzero because $V_1(0)\ne0$ and the factor $Y-t$ cannot supply $h$ zeros at zero. Thus $|E|=h+1$ and $N=cG_{H\setminus E}$ with $c\ne0$. Multiply by $G_E$, cancel the unit $V_1$ modulo $Y^h$, and use $G_H=V_1G_{C_1}$. The result, for some $Q$ of degree at most two and $b\ne0$, is
$$
(Y-t)G_E(Y)=Y^h Q(Y)+bG_D(Y).
$$
At least three elements of $E$ belong to one $A_i$ because $h+1>8$. The quadratic $a_iQ+bG_D$ vanishes on all three, so it is zero. Monicity now gives $(Y-t)G_E=(Y^h-a_i)G_D$. The case $i=4$ is impossible since its right side has two distinct double roots, whereas the left side has at most one. For any of $i=1,2,3$ this equality forces $t\in C_i$. This excludes even a neighboring polynomial at all other parameters. The count follows from $|C_1\cup C_2\cup C_3|=3h+2$.

## A unique locator that misses every error

Put $C=C_1$, $V=V_1$ and write the syndrome functional on polynomials of degree up to $2h-1$ using the usual weights $1/G_H'(y)$. The receive rows vanish off $C$. For every scalar $t$ the functional therefore has the form
$$
\lambda_t(q)=\sum_{y\in C}\frac{(y-t)q(y)}{y^h G_C'(y)}.
$$
If $q$ has degree at most $h-1$, the Lagrange leading-coefficient identity applied to $(Y-t)q$ gives $\lambda_t(Y^h q)=0$. Now let $g$ have degree at most $h$ and suppose $\lambda_t(gq)=0$ for all such $q$. In the space of functions on $C$, with pairing $\langle U,W\rangle=\sum_{y\in C}U(y)W(y)/G_C'(y)$, the orthogonal complement of degree-at-most-$(h-1)$ evaluations is exactly the space of affine-linear evaluations. Inclusion follows from the same leading-coefficient identity. Equality follows because the weighted pairing is nondegenerate, $|C|=h+2$, and the evaluation map on polynomials of degree below $|C|$ is injective.

Hence some affine-linear $L$ satisfies $(y-t)g(y)=y^hL(y)$ on all of $C$. Both sides have degree at most $h+1$, so the identity holds everywhere. If $t\ne0$, evaluation at $t$ forces $L(t)=0$, which gives $g$ proportional to $Y^h$. The same argument over the rational function field with $t=T$ proves uniqueness on the generic fiber. A locator of smaller degree would also satisfy the degree-$h$ apolar equations and is therefore zero.

For $f(Y)=Y^h$ the divided locator tested at zero is $Y^{h-1}$. The identity $1/G_C(X)=\sum_y 1/[G_C'(y)(X-y)]$ and $\sum_y 1/G_C'(y)=0$ give
$$
W_f(t,0)=\lambda_t(Y^{h-1})=\frac{t}{G_C(0)}.
$$
Every one of the bad $t$ lies in $H$ and is nonzero. Since $G_H(0)=-1$, even ordinary evaluation witnesses $f\nmid G_H W_f(t,\cdot)$ throughout this family.

## The relation that survives on a general successor fiber

For an atomic functional $\lambda(q)=\sum_{y\in E}w_yq(y)$ with nonzero weights, suppose $|E|=s+2$ and $\lambda(fq)=0$ for $\deg q\le s$. Set $c=\lambda(fY^{s+1})$. Every monic degree-$(s+1)$ test has the same value after multiplication by $f$, since subtracting $Y^{s+1}$ lowers the degree. Applying this to $G_{E\setminus\{y\}}$ yields
$$
w_yf(y)G_E'(y)=c\qquad(y\in E).
$$
The locator therefore vanishes at every site if $c=0$, and vanishes at none if $c\ne0$. Let $W_f(X)=\sum_y w_y(f(X)-f(y))/(X-y)$. Multiplying by $G_E$ gives
$$
G_E W_f=f\sum_y w_y G_{E\setminus\{y\}}-c .
$$
Indeed the remaining degree-at-most-$(|E|-1)$ polynomial interpolates $c$ at all sites. This identity includes multiplicities of the roots of $f$. The error-set vanisher is an inverse of the divided polynomial modulo $f$ on the hard fibers, up to the scalar $-c$. It gives a different interpolation target for the range beyond unique decoding.

The [small-field exhaustive verifier](../../../scripts/probes/probe_apolar_successor_three_cosets.cpp) checks all supports at $n=32$ and all field scalars. The [Lean fiber identity](../../../ArkLib/Research/ProximityGap/Frontier/ApolarSuccessorDefect.lean) concerns the general atomic relation above. The production count and the three-coset classification are the proof in this note.

## A fixed rational pencil with a five-point secant stays within both named budgets

Take the production length $n=4h=2^{30}$, rate $k=2h$ and radius $e=h+1$. On any injective domain $H$ consider two rows $N_0/f,N_1/f$ with $\deg f=h$, no domain zeros of $f$, and $\deg N_i\le3h-1$. If a single pair of degree-below-$k$ polynomials $P_0,P_1$ has five different parameters $t$ for which $P_0+tP_1$ decodes an MCA witness, **the total number of bad scalars is at most $n$**, including all other decoding polynomials. This covers the analogous fixed degree-$h$ apolar locator without domain roots. The degree-below-$n$ interpolant $N_i$ of $f$ times row $i$ has degree at most $n-h-1=3h-1$, by its parity checks through degree $h-1$ and the Lagrange leading-coefficient identity applied in descending degree.

Let $B$ be the full joint agreement set of $P_0,P_1$. If $|B|>3h-1$, both polynomials $N_j-fP_j$ vanish identically, and both rows are codewords. Otherwise put $b=3h-1-|B|$. Fresh agreements for different scalars are disjoint outside $B$, so the five decoders require $5b\le4h-|B|=h+1+b$. As $4\mid h$, this gives $b\le h/4$. Factor $N_i-fP_i=G_B A_i$ with $\deg A_i\le b$. If $A_0,A_1$ are linearly dependent, the two residual rows are scalar multiples of one word, and at most one folded residual coefficient vanishes. At all other parameters a folded decoder gives joint row polynomials by rescaling. The case where both residuals vanish has zero bad scalars.

Assume independence. No entire folded word is a codeword. Such a polynomial would equal $P_0+tP_1$ on at least $k$ sites of $B$, and therefore everywhere. The nonzero numerator $G_B(A_0+tA_1)$ would then vanish on all $n$ sites despite its degree being at most $3h-1$. For every bad $t$ choose a decoding polynomial $P_t$ and its true error set $E_t$. The nonzero polynomial $N_0+tN_1-fP_t$ has degree at most $3h-1$, so $|E_t|=e$ and it equals $c_tG_{H\setminus E_t}$ for some nonzero $c_t$.

Write $D=\gcd(A_0,A_1)$, $A_i=DA'_i$, $J_t=A'_0+tA'_1$, and $j=\max(\deg A'_0,\deg A'_1)$. Thus $1\le j\le b$. Modulo $f$, the true-error identity gives $G_B D J_tG_{E_t}=c_tG_H$. Its right side is a unit, so $G_BD$ is invertible modulo $f$. In particular all $J_tG_{E_t}/c_t$ have one common residue $U$ modulo $f$. Take $\deg U<h$ and put
$$
  J_tG_{E_t}/c_t=U+fQ_t,\qquad \deg Q_t\le j+1 .
$$
The $Q_t$ all agree with the same word $-U/f$ on their $e$ error sites. For distinct $Q$ classes those selected sets intersect on at most $j+1$ sites.

In a class containing two or more parameters, $J_tG_{E_t}/c_t$ is constant as a polynomial. The various $J_t$ in that class have the same degree because all $|E_t|=e$. At most one $J_t$ over the entire field has degree below $j$, by cancellation of its leading coefficient. Thus every member of a nonsingleton class has degree $j$. The $J_t$ at distinct scalars are pairwise coprime, so $J_t$ divides $G_{E_s}$ for any other $s$ of the same class. All its $j$ distinct roots belong to $H$. Different parameters use disjoint such roots, even across classes. Hence all nonsingleton classes together have at most $n/j$ parameters. Individually each has at most $e+j$ parameters, since its $J_t$ divide one common polynomial of degree $e+j$.

If $j=1$, five distinct classes would cover at least $5e-10\cdot2>n$ sites, by pairwise inclusion-exclusion. Thus there are at most four. With no singleton the disjoint roots give the bound $n$. With a singleton there are at most $3(e+1)+1\le n$ total parameters.

If $2\le j\le h/4-1$, let $L$ be the number of distinct classes, choose one error set per class, and let $a_y$ count the sets containing $y$. Cauchy–Schwarz and pairwise intersections give
$$
 L^2e^2=\left(\sum_y a_y\right)^2
 \le n\sum_y a_y^2\le n\big(Le+L(L-1)(j+1)\big).
$$
Since $e^2-n(j+1)\ge 2h+1$, one has $L\le n(e-j-1)/(2h+1)<2h$. Adding the at most $n/j\le 2h$ nonsingleton parameters proves the bound. More generally this argument and the $j=1$ case apply whenever the two numerator residues modulo $f$ are a common unit times a coprime, linearly independent pair of degree at most $h/4-1$, without assuming any five-point secant. Such a pair precludes an identically decoded scalar since $\deg J_t<h$ and $J_t\ne0$.

It remains to treat $j=h/4$. Here $b=j$ and $D$ is constant. The five original head decoders have one common class $Q_*$, since their numerator is $G_BA_t$ and $J_tG_{E_t}/c_t$ is a fixed scalar multiple of $G_{H\setminus B}$. Thus $Q_*$ agrees with $-U/f$ on all $m=e+j=5h/4+1$ sites of $H\setminus B$. For any other class choose an error set. At most $j+1$ of its $e$ sites lie in $H\setminus B$. Assign weight $4$ to that part and weight $5$ to $B$. Each chosen set then has weight at least $a=5e-(j+1)$, and the sum of squared site weights is $b_2=16m+25(n-m)$. For the $L$ other classes, weighted Cauchy–Schwarz gives
$$
 L^2a^2\le b_2\big(Le+L(L-1)(j+1)\big).
$$
At $h=2^{28}$ this bounds $L$ by the integer part of
$$
 \frac{b_2(e-j-1)}{a^2-b_2(j+1)}
 =\frac{4796333601337638912}{27021584745103385}<178 .
$$
Counting also $Q_*$ gives at most $178$ classes. There are at most $n/j=16$ nonsingleton parameters, for a total bound of $194$ in this endpoint case.

This proof leaves moving generic locators, locators with domain poles, and higher-degree fixed pencils whose every decoded affine head has at most four labels.

## A fixed rational pencil with a twelve-point secant stays within the first budget

Let $h\ge76$, $n=4h$, $k=2h$, and $e=h+1$. Consider an arbitrary injective domain $H$ in a field. Suppose on $H$ the two rows are $N_0/f,N_1/f$, where $f$ has degree $h$, has no domain roots, and $\deg N_i\le3h-1$. Suppose a single pair of degree-below-$k$ polynomials $P_0,P_1$ has at least twelve different parameters $t$ for which $P_0+tP_1$ is a decoder on an MCA witness. Then **the total number of bad scalars for these rows is at most $n$**, including scalars decoded by unrelated polynomials. This condition suffices on either named field. It also applies to a degree-$h$ fixed apolar locator without domain roots. Indeed $N_i$ can be taken as the degree-below-$n$ interpolant of $f$ times row $i$. Its parity checks through degree $h-1$ force degree at most $n-h-1=3h-1$, by descending on the top $h$ coefficients using the Lagrange leading-coefficient identity.

Let $B$ be the full joint core of $P_0,P_1$ and put $b=3h-1-|B|$. No two distinct parameters can have a fresh agreement at the same site outside $B$. If $b>0$, the twelve decoders need at least $12b$ fresh incidences, and there are $4h-|B|=h+1+b$ available. Thus $11b\le h+1$. If $|B|>3h-1$, each $N_j-fP_j$ vanishes identically by degree, and the rows are codewords. So only $b\ge0$ needs consideration. Write $N_j-fP_j=V_B A_j$ where $V_B=G_B$ and $\deg A_j\le b$.

The polynomials $A_0,A_1$ must be linearly independent for a row pair with more than one bad scalar. Otherwise the two rows modulo their displayed codewords are constant multiples of a single word. At any scalar where the folded residual coefficient is nonzero, a decoded folded polynomial supplies both joint row polynomials by scaling. At most one finite scalar has zero residual coefficient, except when both entire rows are codewords and every agreement is joint.

An *exactly decoded* scalar needs separate attention from an arbitrary neighboring polynomial at this step. If the entire folded word is a codeword, that polynomial agrees with $P_0+tP_1$ on $B$. Here $|B|\ge k$ since $11b\le h+1$. Equality on $B$ implies these polynomials are identical, so $V_B(A_0+tA_1)$ vanishes on $H$. Its degree is at most $3h-1<n$, forcing $A_0+tA_1=0$ and contradicting independence.

For every remaining bad $t$, choose a polynomial $P_t$ witnessing the event and its exact error set $E_t$. The nonzero $N_0+tN_1-fP_t$ has degree at most $3h-1$, so $|E_t|=h+1$ and the numerator is $c_t G_{H\setminus E_t}$ for $c_t\ne0$. Reducing modulo $f$, multiplying by $G_{E_t}$ and cancelling the unit $G_B$ gives a polynomial $Q_t$ with
$$
  (A_0+tA_1)G_{E_t}/c_t=G_{H\setminus B}+fQ_t,\qquad \deg Q_t\le b+1.
$$
Each $Q_t$ agrees with the fixed word $-G_{H\setminus B}/f$ on all $h+1$ sites of $E_t$. Distinct polynomials agree at at most $b+1$ sites. Five different $Q_t$ would occupy at least $5(h+1)-10(b+1)>4h$ sites by the two-term inclusion-exclusion bound. Thus there are at most four different $Q_t$.

Divide $A_0,A_1$ by their polynomial greatest common divisor. Their reduced linear combinations $J_t$ are pairwise coprime at distinct parameters. Within any single $Q$ class, the polynomials $J_t G_{E_t}$ are proportional to one fixed nonzero polynomial of degree at most $h+1+b$. Two members $t,t'$ of the class have $J_t\mid G_{E_{t'}}$. Their $J$ polynomials have equal degrees since all $|E_t|=h+1$. In a class containing at least two parameters this degree must be positive. Otherwise both reduced $A$ polynomials would be constants, contradicting their linear independence. Hence each member of such a class has a root $y$ in $H$. All classes use the same reduced polynomials $A_0,A_1$, so the chosen roots for distinct parameters are distinct. This bounds the total number of parameters in nonsingleton classes by $n$, and each individual class by $h+1+b$. If there is a singleton class, there are at most three nonsingleton classes, with at most $3(h+1+b)+1\le4h$ parameters in total. This proves the bound.

The off-domain hypothesis is used in cancelling $G_B$ and in defining the auxiliary received word. At production length, the five-point secant argument above also handles heads carrying five to eleven labels.

## An unconditional requirement for failure at the successor

For any actual row pair, let $G_0,G_1$ be its bad-scalar sets at $h,h+1$ errors respectively. The checked sharp bound gives $|G_0|\le3(h+1)=805306371$. Failure of the first named budget would require at least **268,435,454** scalars in $G_1\setminus G_0$. Failure of the second would require at least **1,342,177,278**. At each such scalar, the chosen actual MCA decoder has exactly $h+1$ errors, since any larger full agreement retains the no-joint witness and qualifies at the previous radius. Every nonzero degree-at-most-$h$ locator apolar through $h-1$ misses every one of those errors, by the atomic defect and the root bound. Evaluation at any such error is injective on the locator kernel: a linear combination of two locators vanishing there must be zero. The preceding catalecticant is injective as well, since a nonzero lower-degree locator apolar through $h$ multiplied by an error's linear factor contradicts the same conclusion. The [actual-family population and kernel statements](../../../ArkLib/Research/ProximityGap/Frontier/ApolarSuccessorPopulation.lean) passed the pinned Lean kernel with only its standard axioms.
