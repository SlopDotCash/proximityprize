# A single-cardinality test for Paley discrepancy

Let $\chi$ be the quadratic character of $\mathbb F_p$ for an odd prime $p$, with $\chi(0)=0$. Fix an integer
$2 \le m \le p/4$. The test uses one extremum over sets of size $m$.

$$
D_m=\max_{|T|=m}\left|\sum_{x,y\in T}\chi(x+y)\right|.
$$

For every prescribed pair of sets with $a=|A|\ge m$ and $b=|B|\ge m$,

$$
\frac{1}{ab}\left|\sum_{x\in A,\,y\in B}\chi(x-y)\right|
\le 6\frac{D_m}{m^2}+\frac8m .
$$

The sum kernel is symmetric at every odd prime. Replacing $B$ by $-B$ at the end gives the
difference version, including at primes where the difference kernel is antisymmetric.
Lean proves the converse by taking $A=T$, $B=-T$. At polynomial size
$m=\lceil p^\varepsilon\rceil$, a power saving for the single number $D_m/m^2$ suffices for the arbitrary-placement
conjecture at that scale. The upper bound on this extremum for arbitrary sets remains open.

## Sampling the centered kernel

Let $K$ be a symmetric real kernel on an $N$-point set, with zero diagonal and zero row sums.
Write $Q(T)=\sum_{x,y\in T}K(x,y)$. Suppose $|Q(T)|\le M$ for every $m$-element set and $4m\le N$.
Each ordered distinct pair in $T$ belongs to exactly $\binom{|T|-2}{m-2}$ of its
$m$-element subsets. The triangle inequality and binomial cancellation give

$$
|Q(T)|\binom m2\le M\binom{|T|}2 \qquad (|T|\ge m).
$$

The sum of $K$ over $T\times T^c$ equals $-Q(T)$ by the row sums. By symmetry it also equals
$-Q(T^c)$. Applying the preceding bound on complements gives

$$
|Q(T)|\binom{N-m}2\le M\binom{N-|T|}2 \qquad (|T|\le m).
$$

For $|T|\le m$, the last ratio is at most two since
$3N\le 4(N-m)$ and $2(N-1)\le 3(N-m-1)$. For $m\le |T|\le 2m$, the first ratio is at most
$2(2m-1)/(m-1)\le 6$. [Exact sampling identities and bounds](../../../ArkLib/Research/ProximityGap/Frontier/PaleySliceSampling.lean)

For two $m$-sets $X,Y$, write $C(X,Y)=\sum_{x\in X,y\in Y}K(x,y)$. Direct expansion gives

$$
2C(X,Y)=Q(X\cup Y)-Q(X\setminus Y)-Q(Y\setminus X)+Q(X\cap Y).
$$

The four terms have absolute bounds $6M,2M,2M,2M$, so $|C(X,Y)|\le 6M$. Sample an
$m$-subset from each of $A,B$ independently and uniformly. Each ordered pair from $A\times B$
occurs with probability $m^2/(ab)$, even when the sets overlap. Averaging proves
$m^2|C(A,B)|\le 6Mab$. Lean proves this inequality as `cut_bound_of_one_size` using exact
finite sums. [Generic rectangle theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleySliceSampling.lean)

## Removing the diagonal for the sum character

Set $d_x=\chi(2x)$. Translation gives $\sum_y \chi(x+y)=0$ and multiplication by two gives
$\sum_x d_x=0$. Define

$$
K(x,x)=0,\qquad
K(x,y)=\chi(x+y)+\frac{d_x+d_y}{p-2}\quad(x\ne y).
$$

Its off-diagonal row sum is $-d_x+((p-1)d_x-d_x)/(p-2)=0$. On a set of size $m$, the
exact difference between the centered and original square sums is

$$
Q_K(T)-\sum_{x,y\in T}\chi(x+y)=\frac{2m-p}{p-2}\sum_{x\in T}d_x .
$$

The absolute value is at most $m$, so the rectangle theorem applies with $M=D_m+m$.
On the full rectangle the deletion of diagonal entries costs at most $|A\cap B|$, and the
off-diagonal correction costs at most $2ab/(p-2)$. After division by $ab$ their sum is
at most $2/m$, using $\max(a,b)\ge m$ and $p-2\ge 2m$. Together these estimates give
$6D_m/m^2+8/m$. Lean proves the character sum and edge-count forms over every finite field of odd characteristic. [Character and edge-count theorems](../../../ArkLib/Research/ProximityGap/Frontier/PaleySingleSizeQuadratic.lean)

## Ordered graph edges

Let $e(A,B)$ count ordered pairs whose difference is a nonzero square. At $p\equiv1\pmod4$
these are the ordered edges of the undirected Paley graph. Of the $ab$ ordered pairs,
$|A\cap B|$ have zero difference, and every other pair has character $1$ or $-1$. Consequently
the same bound applies to

$$
\frac{\bigl|2e(A,B)-ab+|A\cap B|\bigr|}{ab}.
$$

The term $|A\cap B|$ accounts for omitted loops. [Formal edge-count corollary](../../../ArkLib/Research/ProximityGap/Frontier/PaleySingleSizeQuadratic.lean)
