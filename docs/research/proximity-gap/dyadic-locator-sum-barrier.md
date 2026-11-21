# Scalar lists and MCA on the 237-bit large-period domain

Let $p=126205134105047729256068842055334737587878534445324289139206048206460929$, and let $H=\langle g\rangle$ be the specified order-1024 subgroup with a nonprincipal period greater than $2.05\sqrt{1024\log_2(p/1024)}$. Write $B=\lfloor p/2^{128}\rfloor=370883555463132043592346312614163$. The same evaluation domain has a scalar list exceeding $B$ about the monomial center $x^{k+1}$ at all four sponsor rates. At the indicated error count, the canonical MCA probability also exceeds $2^{-128}$. [Spectral witness](../../../ArkLib/Research/ProximityGap/Frontier/DyadicLogWitness237.lean) · [List and MCA construction](../../../ArkLib/Research/ProximityGap/Frontier/DyadicLocatorSumBarrier.lean)

| Dimension $k$ | Error count | Distinct scalar words at $x^{k+1}$ |
|---:|---:|---:|
| 512 | 511 | $\binom{509}{255}>2^{504}$ |
| 256 | 767 | $\binom{509}{127}>2^{407}$ |
| 128 | 895 | $\binom{509}{63}>2^{270}$ |
| 64 | 959 | $\binom{509}{31}>2^{164}$ |

The generator satisfies $g+g^{17}=1$. The three roots $1,-g,-g^{17}$ therefore sum to zero and occupy three distinct antipodal pairs. Complete these three sites with any $(k-2)/2$ of the remaining 509 pairs. The resulting set $T$ has $k+1$ sites and zero sum. Its monic vanishing polynomial $L_T$ has zero coefficient at $X^k$, so $X^{k+1}-L_T$ is a valid message polynomial. Its agreement set with the center is exactly $T$, which distinguishes every candidate. At one fewer error the list about this particular center is empty: every nonzero $X^{k+1}-P$ with $\deg P<k$ has at most $k+1$ roots. Thus the four displayed counts are the exact first failures for the individual monomial centers. The same-domain projective transfer applies because $B^2(k-1)<p+1$. Lean verifies the generator relation and the resulting list and MCA inequalities. Independent `con-leche --verified` accepted all 28,134 transitive declarations of the six exported endpoints, including the subgroup-image equality and the Euclidean counting inequality. The transfer uses the exact relation in the field. A lower bound for the magnitude of a period alone supplies no such relation in this argument.

## Upper bounds for centers of restricted degree

Let $t=k+a$. For every received center represented by a polynomial of degree at most $t$, the maximum number of messages agreeing on at least $t$ sites is bounded as in the first pair of columns. The second pair covers every center $A(X)/X^s$ with $0\le s\le a$ and $\deg A\le t$. All eight bounds lie below $B$.

| $k$ | Polynomial agreement $t$ | List cap | Shifted agreement $t$ | List cap |
|---:|---:|---:|---:|---:|
| 512 | 533 | 59,400,885,600 | 536 | 1,620,288,010,530,347,424 |
| 256 | 275 | 631,098,000 | 276 | 82,762,210,517,011,200 |
| 128 | 145 | 3,020,640 | 146 | 2,506,193,190,592 |
| 64 | 79 | 11,436,768 | 80 | 175,363,776 |

The general upper-bound argument below is a written proof. The arithmetic probe verifies all shifts, the exact finite factors, and the entire moment-fiber bound by enumeration on two smaller fields. These caps apply to the indicated center classes. The first failing error counts over arbitrary received centers remain open. [Exact arithmetic and exhaustive controls](../../../scripts/probes/probe_dyadic_locator_sum_barrier.py)

### From polynomials to indicator moments

Cancel common powers of $X$ from a shifted center first. If the center equals a codeword, no second codeword can agree on $t\ge k$ sites. In every other case $A-X^s P$ is nonzero for each candidate $P$ of degree below $k$. It has at most $t$ roots. Consequently any candidate agrees on exactly $t$ sites, giving a $t$-subset $S\subseteq H$. Its residual is a fixed nonzero leading scalar times $\prod_{x\in S}(X-x)$. The top $a-s$ elementary symmetric coefficients of $S$ are fixed across candidates. For $s>0$, the bottom $s$ residual coefficients are fixed, with nonzero constant coefficient. These determine the first $s-1$ elementary symmetric coefficients of the inverse roots. Newton's identities fix every positive or negative power sum indexed by $j\in[1-s,a-s]\setminus\{0\}$. Distinct candidates give distinct subsets by uniqueness of interpolation. Complementing every support preserves equality of these moments, so start with support size $u=\min(t,1024-t)$.

### Antipodal folding and Euclidean separation

At depth $l$, put $m=1024/2^l$ and $d=m/2$. For a binary indicator vector $x$ in one still-possible class, its folded orientation is $c_i=x_i-x_{i+d}$ for $0\le i<d$. Every such vector satisfies $\sum_i c_i^2\le w=\lfloor u/2^l\rfloor$. For two distinct orientations put $F(Z)=\sum_{i<d}(c_i-c'_i)Z^i$. For each $j$ in the original moment interval with $j/2^l$ an odd integer, the primitive $m$th root $(g^{2^l})^{j/2^l}$ is a zero of $F$ modulo $p$. Let $r$ count these distinct residues modulo $m$.

In $\mathbb Z[Z]/(Z^d+1)$, multiplication by $F$ has nonzero integer determinant because $Z^d+1$ is irreducible over $\mathbb Q$ and $0\ne F$ has degree below $d$. Reduction modulo $p$ diagonalizes at the $d$ distinct odd powers of a primitive $m$th root. At least $r$ diagonal entries vanish. Smith normal form thus gives $p^r\mid\det$. Every row is a signed cyclic shift of the coefficients of $F$. Hadamard's determinant inequality yields
\[
 p^{2r}\le |\det|^2\le \left(\sum_{i<d}(c_i-c'_i)^2\right)^d.
\]
Thus $D=\lceil p^{2r/d}\rceil$ is a lower bound for the squared distance between distinct orientations. If $D>4w$ the squared diameter already rules out two orientations.

For $M$ distinct orientations, summing all ordered pairwise squared distances gives
\[
 M(M-1)D\le 2M\sum_v\|c_v\|_2^2-2\left\|\sum_v c_v\right\|_2^2\le 2M^2w.
\]
Lean checks this Euclidean counting inequality for arbitrary finite families and arbitrary integer vectors. When $D>2w$, each parent class therefore splits into at most $\lfloor D/(D-2w)\rfloor$ orientation classes. Fix an orientation. On its nonzero positions both original bits are fixed. At each zero position the pair is either both occupied or both empty. The number of occupied pairs is fixed within the class and is at most $\lfloor w/2\rfloor$. The class consequently has size at most $\binom{d}{\lfloor w/2\rfloor}$ since $w\le d$.

For two members of this class, the difference of their original indicators is $(1+Z^d)$ times the difference of their occupied-pair indicators. Evaluating at an even frequency turns the prefactor into $2$, a unit in $\mathbb F_p$. Thus those new indicators have equal power sums for the divided even frequencies, on the subgroup of half the previous size. This proves the claimed invariant by induction. Multiply the class-splitting bounds through each successful depth, apply the last binomial bound, and take the minimum with the original subset count. This gives the table, including the worst allowed shift at each rate. At order 128 itself, one fixed sum has at most four folded orientations, since $\lceil p^{1/32}\rceil=167$ and $\lfloor167/(167-128)\rfloor=4$. In particular a fixed-sum construction using full eight-site fibers alone has at most $4\,2^{64}$ supports.
