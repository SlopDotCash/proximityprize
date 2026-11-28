# Exact lists for centers of bounded interpolation degree at length $2^{30}$

At the first unresolved list radius of each named instance, the worst list over received polynomials of degree at most the required agreement count is exactly **3, 3, 3, 1** in descending rate order. Allowing the shifted rational denominators below gives exact maxima **3, 5, 3, 1**. These numbers hold at every positive interleaving width on both named fields. The polynomial-center upper bounds also allow arbitrary denominators of the degrees in the table.

Write $n=2^{30}$, $q=n/4$, $H=\mu_n\subset\mathbb F_p$, and let $k$ be the message dimension. The bounds apply verbatim to a multiplicative coset by scaling the variable. For an interleaved center, identify its alphabet with the vector space underlying a finite extension of the named field, using any basis. The evaluations, degrees and simultaneous agreements are then exactly those of one polynomial over the extension. The roots of agreement locators still lie in the ground field.

| Rate | Field | Errors | Agreements $t$ | Maximum denominator degree | Exact polynomial-center maximum |
|---:|:---|---:|---:|---:|---:|
| $1/2$ | first | 315,391,701 | 758,350,123 | 87,261,483 | 3 |
| $1/2$ | second | 315,391,701 | 758,350,123 | 87,261,483 | 3 |
| $1/4$ | first | 538,320,915 | 535,420,909 | 132,767,725 | 3 |
| $1/4$ | second | 543,870,915 | 529,870,909 | 127,217,725 | 3 |
| $1/8$ | first | 704,116,764 | 369,625,060 | 101,189,604 | 3 |
| $1/8$ | second | 705,616,764 | 368,125,060 | 99,689,604 | 3 |
| $1/16$ | first | 816,806,372 | 256,935,452 | 55,608,860 | 1 |
| $1/16$ | second | 818,306,369 | 255,435,455 | 54,108,863 | 1 |

The first unresolved errors and the unrestricted failure brackets come from the [prize review](full-prize-review.md). The determinant method below specializes the [integer norm bound](../../../ArkLib/Research/ProximityGap/Frontier/DyadicFoldedNorm.lean) already used for [small quotient locator families](dyadic-locator-degree-caps.md). The additional point at full length is to descend after each lift. The shorter vector still has entries in $\{-1,0,1\}$. Its energy bound decreases at each step.

## A short Fourier interval determines changes of whole quarter cosets

Suppose $n=2^a\ge 8$, $p\equiv1\pmod n$ is prime and $p>(2n)^4$. Take $g$ of order $n$ in $\mathbb F_p$. For a vector $b_0,\ldots,b_{n-1}\in\{-1,0,1\}$, suppose

$$
  \sum_{j=0}^{n-1} b_j g^{uj}=0\quad(1\le u\le n/8).
$$

Then $b_j$ depends only on $j\bmod4$.

At a current length $N\ge16$, write $h=N/2$, $B(Z)=\sum_{j<h}(b_j-b_{j+h})Z^j$, and use the current primitive root. Multiplication by $B$ on $\mathbb Z[Z]/(Z^h+1)$ has a negacyclic matrix. Each row has squared length at most $4h=2N$, so its integer determinant satisfies $|D|\le(2N)^{N/4}$. Modulo $p$, evaluation at the $h$ distinct primitive $N$-th roots diagonalizes the multiplication. The odd exponents through $N/8$ give at least $N/16$ zero entries, hence $p^{N/16}\mid D$ by Smith normal form. Since $p^{N/16}>(2N)^{N/4}$, we have $D=0$. The polynomial $Z^h+1$ is irreducible over $\mathbb Q$, so $B=0$. Thus the two halves of the vector agree over the integers.

Keep the first half, square the primitive root, and use the even tests $u=2v$. The old sum is twice the new sum. The prime is odd, so the shortened vector has all tests through $(N/2)/8$. At $N=8$, the single exponent 1 suffices since $|D|\le16^2<p$. This gives period four. For an interval of $n/8$ consecutive exponents in any position, the same descent gives **period at most eight**. At length $N\ge16$, the multiples of $n/N$ in that original interval include $N/8$ consecutive scaled exponents, at least $N/16$ of them odd. There need not be an odd test left at length eight. The same proof works for a negative initial interval by replacing the generator with its inverse.

## Classifying and realizing the lists

Let $t<n$, $k\ge1$, and $n/8\le t-k<n/4$. Let $W$ be the received word over any extension field and take polynomials $A,B$ with $B\ne0$,

$$
  A(x)=B(x)W(x)\quad(x\in H),\qquad
  \deg A\le t,\qquad \deg B\le t-k-n/8 .
$$

For every candidate $f$ of degree below $k$ the polynomial $A-Bf$ vanishes at its agreement sites. If it vanishes identically, every other residual is $B(f-f')$, of degree below $t$, so there is only one candidate. Otherwise every candidate residual has degree exactly $t$, has exactly $t$ distinct roots on $H$, and is $cL_S$, where $L_S=\prod_{x\in S}(X-x)$. Their common leading coefficient $c$ is the leading coefficient of $A$. Distinct candidates have distinct $S$. This argument allows zeros of $B$ on $H$.

The coefficients of these monic locators agree down through degree $k-1+\deg B+1=k+\deg B$. Newton's identities make the first $t-k-\deg B\ge n/8$ power sums equal. The differences of indicators therefore have period four by the preceding result. Relative to any one candidate $S$, every other candidate agrees exactly on all residue classes of exponents modulo four where $S$ is mixed. Each wholly occupied class can stay occupied or become empty, and each empty class can stay empty or become full. All candidates have the same total number of full classes.

For polynomial centers with $B=1$, the converse holds. Each whole class has vanisher $X^q-c_i$ for the corresponding class constant $c_i$. Exchanging any number of equally many full and empty classes leaves the monic locator coefficients unchanged in degrees $t,t-1,\ldots,t-q+1$. If $A-cL_S=f$ is a candidate, every permitted exchange gives the candidate $f+c(L_S-L_{S'})$, since $t-q<k$. Consequently an individual nonempty degree-$t$ list contains exactly $\binom{F+E}{F}$ words when its reference support has $F$ full classes and $E$ empty ones. If a center of degree below $t$ has a candidate, its residual must vanish identically. These facts give the exact maximum among all centers of degree at most $t$. With $j=\lfloor t/q\rfloor$, it is

$$
  \begin{cases}
     \binom{4}{j},&q\mid t,\\
     \binom{3}{j},&q\nmid t .
  \end{cases}
$$

Indeed any nonintegral number of quarter classes requires at least one mixed class. Both the number of exchangeable full classes and the number of exchangeable empty classes are at most the corresponding floors of $t/q$ and $(n-t)/q$. Binomial monotonicity gives the displayed bound. To attain it, take $S$ with $j$ full classes and any required remainder in one more class, and use the center $A=L_S$. In the integral case choose only full classes. Repeating the construction in each interleaving row realizes the same bound at every width.

This applies throughout the stated interval of $t$, including the agreement counts $t=k+n/8$. Those give respectively 402,653,184, 671,088,640, 805,306,368 and 872,415,232 errors. The corresponding exact polynomial-center maxima are **3, 3, 4 and 1**.

## Shifted rational denominators

More generally take $B=X^sQ$, $Q(0)\ne0$, $b=\deg Q\le t-k-n/8$, $s+b\le t-k+1$, and $\deg A\le t$. Suppose again that $A(x)=B(x)W(x)$ on $H$. If $A=0$, at most one message can agree on $t$ sites since $b+k-1<t$. Cancel common powers of $X$ from $A,B$ when $A\ne0$. If $s=0$ the previous theorem applies. Otherwise $A(0)\ne0$, and for each nonzero degree-$t$ residual $R_f=A-Bf$, the monic reciprocal locator is $X^tR_f(1/X)/A(0)$. Its highest $s-1$ coefficients below the leading term are independent of the candidate. The fixed nonzero value $A(0)$ also makes the agreement support determine the residual even when its leading coefficient varies. The positive power sums agree for $1\le u\le t-k-s-b$ when this interval is nonempty. The negative power sums agree for $-s<u<0$. Together with the common cardinality at zero, these contain $n/8$ consecutive exponents. If $s+b=t-k+1$, the negative interval and zero already suffice. An identically vanishing residual contributes only one candidate, as $B(f-f')$ has at most $b+k-1$ roots on $H$.

Write $v=n/8$ and $j=\lfloor t/v\rfloor$. The interval gives period eight for differences of indicators. If $s>0$ and $s+b\le t-k$, both the leading coefficient and the nonzero constant coefficient of $R_f$ are fixed. The monic locators therefore have the same constant coefficient. A full eighth class labeled $i$ has vanisher $X^v-g^{iv}$. With the mixed classes fixed, exchanging full classes must preserve the sum of their labels modulo 8.

When $v\nmid t$, choose a mixed class to omit. If $F$ of the remaining pure classes are full and $h$ classes are mixed, then $0\le j-F<h$. Pad each of the possible full-label sets with the same $j-F$ mixed labels outside the omitted one. This injects the possible choices into the $j$-subsets of seven labels having one prescribed residue sum. Translating the omitted label to zero subtracts the same constant from every sum. When $v\mid t$, one can instead pad inside all eight labels, with no omission. The exact largest residue populations are as follows.

| Number $j$ of selected labels after padding | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Eight labels, $v\mid t$ | 1 | 1 | 4 | 7 | 10 | 7 | 4 | 1 | 1 |
| Seven labels, $v\nmid t$ | 1 | 1 | 3 | 5 | 5 | 3 | 1 | 1 | |

If $s=0$, the positive interval already gives the four-class bound. If $s+b=t-k+1$, then $s-1=t-k-b\ge v$ gives that bound from the negative interval. In either case the earlier four-class maximum is at most the corresponding entry here. This follows by substituting $q=2v$ in its binomial formula.

Every entry that occurs in the band $v\le t-k<2v$ is attained. Take a fixed partial class of size $t-jv$ if needed, with vanisher $V$, and choose the largest fixed-sum layer of $j$-subsets $I$ of the remaining labels. Write $L_I=V\prod_{i\in I}(X^v-g^{iv})$. The differences $L_I-L_J$ have degree at most $t-v$, and each is divisible by $X^v$ because the two products in $X^v$ have equal constant coefficients. Choose $s=t-k-v+1$, so $1\le s\le v$. The word $W=L_J/X^s$ has distinct codewords $(L_J-L_I)/X^s$ of degree at most $k-1$, with exact agreement sets the roots of $L_I$. This proves the two rows of the census are the exact maxima for this entire class of rational centers. At the named agreement counts they give **3, 5, 3, 1** in descending rate order on each field.

## The unrestricted step

The rational hypothesis gives a family of homogeneous linear tests for any received word. With $W$ its degree-below-$n$ interpolant and $0\le s\le t-k+1$, map $Q$ of degree at most $\min(t-k-v,t-k+1-s)$ to the coefficients in degrees $t+1,\ldots,n-1$ of $X^sQW\bmod(X^n-1)$. Every over-budget center at a tabulated radius must have **every one of these maps injective**. Any extra factor $X$ in $Q$ can be absorbed into $s$. This condition is possible in every row. For example $W=X^{t+1}$ satisfies $(t+1)+(t-k+1)<n$, so multiplication by any allowed nonzero denominator leaves the numerator degree above $t$. Establishing safety for all centers requires a bound on the centers that pass all these injectivity tests.

The [Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/LowDegreeCenterListRigidity.lean) checks the positive-interval period-four theorem, the whole-block counting inequality, the named four-class counts and both exact eight-label residue tables. The passage from locators to moments uses the existing [Newton identities](../../../ArkLib/Research/ProximityGap/Frontier/SplitFiberNewton.lean). The shifted interval, rational-center application and sharp attaining constructions are proved above. The [exact checker](../../../scripts/probes/probe_low_degree_center_list_rigidity.py) verifies both named field hypotheses and every reported census. It compares every subset at orders 8 and 16 over both named primes against its predicted fiber, and evaluates the production witnesses on disjoint dyadic cosets partitioning all $2^{30}$ positions.
