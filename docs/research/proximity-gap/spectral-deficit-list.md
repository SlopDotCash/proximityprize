# Three larger all-center list-decoding floors at budget twice the length

At length $n=2^{30}$, every closed Reed–Solomon ball at the safe error count below contains at most $2n$ distinct words. The proof applies to every field, every injective evaluation domain and every positive interleaving width. At the second named prime, $2n$ is precisely the sponsor budget. These are lower bounds on its first failing error count.

| Rate | Previous first-failure floor | New safe error count | New first-failure floor | Increase |
|---|---:|---:|---:|---:|
| $1/2$ | 314,491,700 | 314,491,712 | **314,491,713** | 13 |
| $1/8$ | 694,116,764 | 694,116,789 | **694,116,790** | 26 |
| $1/16$ | 805,306,371 | 805,306,402 | **805,306,403** | 32 |

The previous all-center estimates used strict Johnson, puncturing, or Hahn inequalities. The upper bounds on first failure still come from explicit received words at larger error counts. [Previous bounds](cubic-hahn-list-bounds.md) · [Production brackets](full-prize-review.md) · [Exact arithmetic](../../../scripts/probes/probe_spectral_deficit_list.py)

## A necessary fourth-moment inequality

If a ball contains $m=2n+1$ messages, select exactly $t$ agreement sites $S_i$ for each. For distinct indices $i,j$, $|S_i\cap S_j|\le s=k-1$ because at least one row of the two polynomial messages differs. This reduction permits arbitrary choices of the selected sites. Write $a=t-s>0$ and assume $ns\ge t^2$. Define
\[
 \epsilon=\frac{ns-t^2}{na},\qquad L=1+m\epsilon,\qquad
 \kappa=\frac{s-\max(0,2t-n)}a .
\]
When $\kappa\le1$, the following inequality is necessary:
\[
                 m(1-\kappa^2)\ \le\ 2L(L-1)(L+1)^2.                 \tag{1}
\]
The same statement holds after replacing the geometric lower bound $\max(0,2t-n)$ by any larger valid lower bound on the pair intersections. [Lean reduction from interleaved lists to supports](../../../ArkLib/Research/ProximityGap/Frontier/InterleavedListJohnsonRank.lean)

Let $D$ be the real symmetric matrix with zero diagonal and entries $D_{ij}=(s-|S_i\cap S_j|)/a$ off the diagonal. Its entries lie in $[0,\kappa]$. With $J=\mathbf1\mathbf1^{\mathsf T}$, let $G$ be the Gram matrix of the vectors $(1_{S_i}-(t/n)\mathbf1)/\sqrt a$. Then
\[
              D=I+\epsilon J-G,\qquad G\succeq0,\qquad \operatorname{rank}G\le n-1 .
\]
The rank bound follows because each centered vector sums to zero. Set $C=I-D$ and $S=\operatorname{tr}D^2$. Since $\operatorname{rank}C\le n$ and $\operatorname{tr}C=m$, Cauchy–Schwarz on its nonzero eigenvalues gives
\[
             m^2\le n\operatorname{tr}C^2=n(m+S),\qquad S\ge m .
\]
For any real vector $x$, the Gram identity gives $x^{\mathsf T}Dx\le L\|x\|^2$. Entrywise nonnegativity gives $|x^{\mathsf T}Dx|\le |x|^{\mathsf T}D|x|\le L\|x\|^2$, where $|x|$ is taken by coordinates. Every eigenvalue of $D$ is therefore in $[-L,L]$.

Put $Q=\operatorname{tr}((D^2-I)^2)$. The matrix $P=(LI+D)(I+D)^2$ is positive semidefinite, and its eigenvalues are at most $2L(L+1)^2$. Expanding the polynomials and using $I-D=G-\epsilon J$ gives
\[
 Q=(L+1)\operatorname{tr}((I-D)(I+D)^2)-\operatorname{tr}(PG)
                +\epsilon\mathbf1^{\mathsf T}P\mathbf1 .
\]
The first trace is $m-S-\operatorname{tr}D^3\le0$ since $D$ is entrywise nonnegative. The trace of $PG$ is nonnegative since $G$ is a Gram matrix and $P$ is positive semidefinite. The last term is at most $2L(L+1)^2m\epsilon$. This proves the upper bound in (1).

For the lower bound put $r_i=\sum_jD_{ij}^2$, so $\sum_i r_i=S$. For $i\ne j$,
\[
           (D^2)_{ij}^2\ge\sum_k D_{ik}^2D_{jk}^2
\]
because all cross terms are nonnegative. On the diagonal $(D^2)_{ii}=r_i$. Summing and correcting the repeated diagonal contribution yields
\[
 \operatorname{tr}D^4\ge2\sum_i r_i^2-\sum_{ij}D_{ij}^4
              \ge 2S^2/m-\kappa^2 S .
\]
Subtracting $2S$ and adding $m$ gives $Q\ge m(1-\kappa^2)$, since the difference is $(S-m)(2S/m-\kappa^2)\ge0$.

## Exact finite comparisons

The table rounds the necessary lower bound for $Q$ down and the upper bound up. Even after rounding the inequalities are incompatible. One more error makes (1) consistent in each row.

| Rate | Agreements $t$ | Lower bound, rounded down | Upper bound, rounded up |
|---|---:|---:|---:|
| $1/2$ | 759,250,112 | 1,779,033,465 | 1,633,333,134 |
| $1/8$ | 379,625,035 | 1,505,129,339 | 1,399,381,105 |
| $1/16$ | 268,435,422 | 1,908,874,283 | 1,746,955,546 |

At quarter rate and $536{,}870{,}914$ errors, $t=n/2-2$ and $s=a=n/4-1$, so the unrestricted entry cap is one. If all selected pairs met on at least 901 sites, the revised cap $1-901/s$ would violate (1). Hence any over-budget quarter-rate ball must have two messages for which the selected agreement sets meet on at most 900 sites. Together the two messages cover all but at most $900+n-2t=904$ received symbols. The quarter-rate count itself requires a further argument.

The [Lean finite-sum and endpoint results](../../../ArkLib/Research/ProximityGap/Frontier/SupportDeficitFourthMoment.lean) prove the repeated-index fourth-trace lower estimate and all three exact endpoint comparisons. They also check an alternative spectral upper estimate. At most one eigenvalue $r$ can exceed one since $D\preceq I+\epsilon J$. All other eigenvalues $e$ then satisfy $-r\le e\le1$, using nonnegativity of $D$ for the absolute bound. The trace of $(D-I)(D+I)^2$ equals $\operatorname{tr}D^3+S-m\ge0$. Thus $\sum_{e\ne r}(1-e)(e+1)^2\le(r-1)(r+1)^2$, where one copy of the top eigenvalue is set aside. The Lean estimate on this sum gives $Q\le2r(r-1)(r+1)^2\le2L(L-1)(L+1)^2$. The Gram-matrix argument linking the finite sums to arbitrary supports is given above. Running `python3 scripts/probes/probe_spectral_deficit_list.py` also checks the fourth trace directly on three different 31-word support families from the lines of the binary projective space with 15 points.
