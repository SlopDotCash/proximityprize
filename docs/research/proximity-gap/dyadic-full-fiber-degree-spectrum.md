# Exact degrees of three full fibers on a complex dyadic grid

Let $N$ be a power of two and $d\ge1$. A degree-$d$ rational function over the complex numbers has three distinct fibers of $d$ distinct points each on $\mu_N$, for some choice of that function, **if and only if $3d\le N$ and the odd part of $d$ is one or three**. The same criterion holds over every characteristic-zero field containing $\mu_N$.

Three disjoint $d$-sets form such fibers precisely when their monic locators $F_i=\prod_{x\in S_i}(X-x)$ are linearly dependent. Every coefficient in their dependence is nonzero. For $d\ge11$, the previously proved dichotomy either halves the ambient grid at fixed degree, or squares three globally antipodal sets to halve both grid and degree. Degrees seven and nine have already been excluded. We address the two remaining excluded base degrees, five and ten. The resulting criterion transfers individually to the two named order-128 subgroups, and excludes a common forbidden layout at both named order-256 subgroups. The available transfers do not extend this classification to either full production subgroup. [Higher-degree dichotomy and transfer conditions](dyadic-three-fiber-descent.md) · [Degree seven](dyadic-seven-fiber-descent.md) · [Degree nine](dyadic-nine-fiber-descent.md)

## Necessary equations at degrees five and ten

Write $M=N/2$, $\theta=\zeta_N^2$. Take the smallest grid permitting a counterexample at the degree under consideration. We can also discard the globally antipodal case at degree ten once degree five has been excluded. The three-center parity lemma then permits simultaneous rotation so that every set has an even majority and its odd sites are either empty or one antipodal pair $x_i,-x_i$. Indeed, three sites of a given parity force both other sets to be antipodal on the opposite parity. Three tests of both parities give global antipodality. Otherwise two sets have the same majority parity and force the third to be antipodal on its minority class if it shares their majority, or force global antipodality if it does not. If every pair is absent the grid halves, contrary to minimality. Set $t_i=x_i^2=\theta^{a_i}$, with $a_i$ odd, or $t_i=0$ for an absent pair. The nonzero labels are distinct. [Three-center parity and the majority argument](dyadic-three-fiber-descent.md#descent-in-grid-and-degree)

The ordinary sites of each color lie on $\mu_M$. Write $H_i,L_i$ for the sums of these sites with even and odd $\theta$-exponents, respectively. For any distinct $i,j,k$ with $t_i\ne0$, reflecting in its odd pair gives
\[
                  H_j-H_k=-t_i(\overline L_j-\overline L_k).                 \tag{1}
\]
If $d$ is odd the signed-norm argument excludes three nonzero $t_i$. We need also the phase of the same reflection. At $x=x_i$, put $g(y)=(x-y)/(-x-y)$. The products of $g(y)$ over the two other ordinary supports agree. Their odd-pair quadratic factors cancel separately. The orbits $y,-y,t_i/y,-t_i/y$ all have four members because $a_i$ is odd. Take $y$ of even $\theta$-exponent. The four values of $g$ are $s,s^{-1},-s,-s^{-1}$. In each orbit the signed exponent of $s$ is zero by the primitive-displacement identity used to prove (1). The remaining sign gives equal parity for the numbers of odd-exponent ordinary sites of $j,k$. [Primitive-displacement and signed-norm identities](dyadic-nine-fiber-descent.md#a-reflection-obstruction-for-three-odd-pairs)

Take the ordinary test sites of $i$ in either parity shell. Write $S_i$ for their sum and $V_j,V_k$ for the opposite-shell sums of the other colors. If $t_j=t_k=0$, three tests force both opposite shells to be antipodally symmetric. Otherwise $t_j\ne t_k$. Five tests force both labels to vanish and are impossible. For three or four tests define
\[
 q_{jk}= (t_j-t_k)/(\bar t_j-\bar t_k)
 =\begin{cases}-t_jt_k &t_jt_k\ne0,\\ t^2 &t\text{ the only nonzero label}.\end{cases}
\]
For four actual tests their product is $q_{jk}$. For three tests append a fourth, virtual root $q_{jk}/\prod_{x\text{ tested}}x$. In both cases write $S_i^*$ for the completed sum. The quartic coefficient identity is
\[
                      \bar V_j-\bar V_k=-(\bar t_j-\bar t_k)S_i^*.           \tag{2}
\]
Reduction modulo $1-\theta$ gives equal parity for the two opposite-shell counts. [Four-test identity and its rotation to either shell](dyadic-seven-fiber-descent.md#shell-equations)

## Degree five

There are one or two nonzero labels. With two, the phase identity at each of their pairs makes the shell counts have the same parity across all three colors. With one, both other colors have five ordinary sites, including three in some shell. Each has at most four there by the five-test obstruction. Applying (2) to each of those two testers again forces common shell-count parity, since every ordinary-site total is odd. Rotate by $\theta$ if necessary so the even-exponent shell has odd size in every color. Call its count $h_i$. Each $h_i$ is one or three. In the one-pair case its color cannot have $h_i=3$: its three ordinary tests make both other light shells antipodal. For the remaining two colors their heavy sums then have positive odd coefficient norm and their light sums have zero norm, contrary to (1) and disjointness. Thus up to color permutation only the nine rows below survive.

Write $P_i$ for the product of all five roots, including a factor $-t_i$ when its pair is present. All ordinary light counts are even, so the exponent parity of $P_i$ specifies pair presence. In particular the $P_i$ are not all equal. If just two were equal, the leading and constant coefficients in a locator dependence would force one of its coefficients to vanish. Hence the three $P_i$ are distinct. Their differences fix the dependence up to scale. Comparing its degree-four coefficients gives the additional identity
\[
             \sum_{i\bmod 3}(P_{i+1}-P_{i+2})(H_i+L_i)=0.                   \tag{3}
\]
The terms with even and odd exponents vanish separately by the dyadic power basis.

The following finite calculation over the **entire** group of dyadic angles excludes all nine rows. The first indexed colors are those with top pairs. The table records visited parametrizations, including endpoints pruned by parity or guaranteed site collisions. The search uses arbitrary-precision integers, and its termination has no grid-order cutoff. [Executable cancellation proof](../../../scripts/probes/probe_dyadic_quintic_descent.py)

| Top pairs | $(h_1,h_2,h_3)$ | Parametrizations |
|---:|:---:|---:|
| 1 | (1,1,1) | 336 |
| 1 | (1,1,3) | 562 |
| 1 | (1,3,3) | 43,744 |
| 2 | (1,1,1) | 200 |
| 2 | (1,1,3) | 22,686 |
| 2 | (1,3,1) | 724 |
| 2 | (1,3,3) | 340 |
| 2 | (3,3,1) | 604 |
| 2 | (3,3,3) | 1,020 |

Here are the calculation and its completeness argument. Each ordinary site and each nonzero $t_i$ has its own angle variable in $G=\mathbb Z[1/2]/\mathbb Z$. An affine form in these variables and $1/2$ represents the exponential of that angle. Products add angles, conjugation negates them, and negating an exponential adds $1/2$. Use an even-exponent rotation to fix the first heavy site at 1, preserving all exponent parities. Impose the four-test product equalities, the required site and label distinctions, and the distinct $P_i$. The remaining equations are signed sums of roots in (1)–(3), with the three-center zero sums when both other top pairs are absent. Each sum is zero exactly when its terms can be partitioned into antipodal pairs. This follows from the rational basis $1,\xi,\ldots,\xi^{m/2-1}$ in any single dyadic group $\langle\xi\rangle$ containing its finitely many roots.

The program splits these possibilities over parametrizations
\[
                   D x=c/S+I y\quad\text{in }G^n.
\]
Here $D$ is a positive odd integer, $S\ge2$ a power of two, $I$ integral, and the independent parameters $y$ are a subset of the original variables $x$. The initial parametrization is the identity. A required antipodal match gives a linear equation $v\cdot y=-b/S$ after multiplying by $D$. If $v=0$, simply test the constant. Otherwise let $g$ be the power of two in the coefficient gcd and $w=v/g$. The right side has exactly $g$ lifts $r/(gS)$ under multiplication by $g$, with $r=(-b\bmod S)+jS$ for $0\le j<g$. Choose an odd coefficient $q=w_k$. The equation $q y_k=r/(gS)-\sum_{j\ne k}w_jy_j$ determines $y_k$ uniquely since multiplication by $q$ is an automorphism of $G$. Substituting into the old parametrization and multiplying it by $q$ gives the new columns $qI_j-w_jI_k$, constant numerator $qg c+I_k r$, scale $gS$, and odd denominator $qD$. Sign and common factors are normalized exactly. This eliminates one free parameter on every nontrivial matching branch.

A parametrization that forces an equality between two sites required to be distinct is discarded. For the parity test, let the true half-grid order be $M$. All free angles are original site angles or labels, so their orders divide $M$. Consequently the orders in the constant vector also divide $M$. Once the common scale is reduced, either $M>S$, giving constant parity vector zero, or $M=S$, giving $c\bmod2$. In either case the prescribed site parity minus that vector must lie in the column space of $I\bmod2$, since $D$ is odd. The half-grid contains at least eleven ordinary sites in these cases. The program discards a branch only when both parity choices are impossible or a required distinction is identically violated.

Within a surviving parametrization, cancel every pair already identically antipodal. For one remaining term the algorithm tries each distinct affine character among possible partners. Equal affine characters can be interchanged. Different constants with the same free coefficients cannot newly become opposite. Each other candidate produces exactly the finite branches above. An empty list of remaining equations would conservatively count as a survivor. The nine searches visit **70,216** parametrizations and give zero survivors. As controls the program compares parametrizations with direct small-group enumeration in 243 cases and recovers candidates in the two largest residual patterns upon deleting (3). This finishes degree five.

## Degree ten

If a color lacks a top pair, its ten ordinary sites give five same-shell tests forcing both other pairs to be absent. Hence in a minimal nonglobally-antipodal counterexample all three top pairs are present. Each color has eight ordinary sites, exactly four in each shell by the same five-test obstruction. Write $T=t_1t_2t_3$. For each color $i$ the product of its heavy quartet, and of its light quartet, equals $-t_jt_k$ by (2).

For either shell write $S_i$ for its sum and $V_i$ for the opposite sum. Two instances of (1), at pairs $j,k$, give
\[
 \bar V_j-\bar V_k=\bar t_j S_k-\bar t_k S_j-(\bar t_j-\bar t_k)S_i.
\]
Comparing with (2) at $i$, for which $S_i^*=S_i$, gives $t_jS_j=t_kS_k$. Thus there are common sums $C_H=t_iH_i, C_L=t_iL_i$ over all colors, and substituting into (1) gives $C_H=T\bar C_L$.

The three quartets obtained by multiplying each color's heavy sites by $t_i$ have products $-Tt_i^3$, all distinct since cubing is injective on dyadic roots. They have the same sum. Its reduced multiset after antipodal cancellation must have size zero or two, since size four would determine the whole quartet and its product. The same holds for the light quartets. If $C_H=0$, then $C_L=0$ and all six quartets are antipodal. All original supports would be globally antipodal and descend to the excluded degree five.

Otherwise let $A,B$ be the two unpaired roots in the common scaled heavy remainder. Put $\lambda=T/(AB)$. The common scaled light remainder is $\{\lambda A,\lambda B\}$ from $C_L=T\bar C_H$. By the quartet products the unscaled heavy pair has the form $\{\pm h_i\}$ with $h_i^2=\lambda t_i$. The unscaled light pair has square $\lambda^{-1}t_i$. Consequently the full locator of color $i$ is
\[
 F_i(X)=(X^2-t_i)(X^2-\lambda t_i)(X^2-\lambda^{-1}t_i)
            \prod_{a\in\{A,B,\lambda A,\lambda B\}}(X-a/t_i),
\]
where the last product counts the listed roots with multiplicity.

Put $u_i=1/t_i$. The product of the ten roots is a fixed nonzero multiple of $u_i$, so in a linear dependence of the monic locators every coefficient of $F_i$ must be affine in $u_i$ at the three indices. In particular the second elementary coefficient is
\[
                 E_2u_i^2-(1+\lambda+\lambda^{-1})/u_i,
\]
where $E_2$ is the second elementary symmetric function of $A,B,\lambda A,\lambda B$. At three distinct nonzero $u_i$, the second divided differences of $u^2$ and $1/u$ are $1$ and $1/(u_1u_2u_3)=T$, respectively. Thus $E_2=(1+\lambda+\lambda^{-1})T$. But $T=\lambda AB$, and expanding gives
\[
                 E_2-(1+\lambda+\lambda^{-1})T
                    =\lambda(A^2+AB+B^2).
\]
This would make $A/B$ a primitive cube root of unity, impossible in the dyadic group. Degree ten is excluded. The executable checks this second-coefficient calculation by specialization and direct three-point determinants. [Arithmetic controls](../../../scripts/probes/probe_dyadic_quintic_descent.py)

## Attainment and the fixed-grid criterion

If the odd part of $d$ exceeds three, the high-degree dichotomy eventually reaches an excluded degree $5,7,9,10$ or runs out of ambient points. In detail both allowed steps strictly decrease $N$, and halving an even degree preserves its odd part. Every degree at most ten with odd part above three appears in that list. This proves necessity, along with the immediate counting bound $3d\le N$.

For $d=2^a$, the counting condition implies $N\ge4d$; $X^d$ supplies at least four distinct full fibers. For $d=3\cdot2^a$ it implies $N\ge16\cdot2^a$. The cubic pencil on $\mu_{16}$ has three full fibers at exponents $\{0,1,8\},\{2,9,10\},\{3,5,7\}$. Composing with $X^{2^a}$ pulls back each of its nine sites to $2^a$ sites of $\mu_N$. The cubic identity holds over the dyadic cyclotomic field, giving the claimed characteristic-zero statement. [Integral cubic and disjoint full fibers](quarter-three-heads-32-fibers.md#attainment)
