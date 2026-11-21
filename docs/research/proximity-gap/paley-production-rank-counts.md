# Exact four-site rank counts on the two production domains

For each production subgroup $H=\langle g\rangle$ of size $n=2^{30}$, let $S_{ij}=\chi(g^i-g^j)$. Write $D(H)$ for the number of unordered four-subsets whose principal matrix is singular over $\mathbb F_3$. The calculation counts these subsets on the full subgroup using exact integer correlations. The two prime fields and the subgroup generators are specified in the [production spectrum note](paley-production-spectrum.md).

There are $55{,}384{,}499{,}514{,}886{,}485{,}411{,}402{,}581{,}463{,}269{,}376$ unordered four-subsets of either domain.

| Exact statistic | First domain | Second domain |
|---|---:|---:|
| Singular four-subsets $D(H)$ | 13846124917414186831211638091153408 | 13846124878717088591847695199502336 |
| Energy $E(H)$ | 3714042168113704797195993088 | 2475735024454058624663158784 |
| $\sum_h R_h^2$ | 3458971314238109437 | 2305707917040268541 |
| $\sum_h R_h$ | 956603041 | 2076481 |
| $\max_{h\ne0}\lvert R_h\rvert$ | 284174 | 267550 |
| $4D(H)-\binom n4$ | 154770261913443970901344256 | −18131044011800665260032 |
| $D(H)/\binom n4-1/4$ (approximate) | $+6.986172272\cdot10^{-10}$ | $-8.184168933\cdot10^{-14}$ |

For a uniformly sampled projective $n$-set $X$ at the same prime, the [rank-design mean and variance](paley-rank-design.md) show how exceptional these named domains are. With $v=p+1$, $B=\binom n4$ and $\theta=(p-5)/(4(p-2))$, the mean is $\mu=\theta B$ and the variance is $V=\theta(1-\theta)B\binom{v-n}4/\binom{v-4}4$. The standardized deviations $(D(H)-\mu)/\sqrt V$ are approximately $+379{,}693{,}158.97$ and $-44{,}480.34$, respectively. Exact rational comparisons and Chebyshev's inequality give
$$
 \Pr\big(|D(X)-\mu|\ge |D(H)-\mu|\big)
 \le V/(D(H)-\mu)^2
 < \begin{cases}7.0\cdot10^{-18} & \text{first prime},\\
                      5.1\cdot10^{-10} & \text{second prime}.\end{cases}
$$
In particular, the energy ratios $E(H)/n^3$ are approximately 3.00017937077 and 1.99988282622. The first subgroup exceeds the $3n^3$ threshold that holds for most uniformly sampled domains. Both energy and the singular count are unchanged under any projective transformation of the whole subgroup.

## From cyclic correlations to the count

Write $c_j=\chi(1-g^j)$, with $c_0=0$, and $R_h=\sum_j c_jc_{j+h}$ cyclically modulo $n$. Because $S_{ij}=\chi(g)^ic_{j-i}$, the diagonal row signs cancel in $S^tS$. Its entries are $R_{j-i}$, giving $E=\operatorname{tr}((S^tS)^2)=n\sum_hR_h^2$. At both primes $\chi(-1)=1$. The [four-site determinant identity](paley-four-site-rank.md) gives the exact count
$$
 D(H)=\frac{E-n(n-1)(2n-3)+8\binom n4}{32}.
$$

## An integer transform with unique reconstruction

Use the auxiliary prime $Q=3\cdot 2^{30}+1=3221225473$. The executable verifies primality by trial division and checks $125^{2^{29}}=-1$ and $125^{2^{30}}=1$ modulo $Q$. Thus $125$ has order $2^{30}$. A number-theoretic transform gives the cyclic correlations modulo $Q$. Since $|R_h|\le n<Q/2$, each residue has exactly one possible integer lift. The modular products fit unsigned 64-bit integers, and the integer moments, counts and numerator above fit signed 128-bit integers even at their trivial upper bounds.

Factor $n=ML$ with $M=1024$ and $L=2^{20}$. The first pass transforms the $M$ length-$L$ rows $c_{r+Mj}$ at a primitive $L$th root. At row frequency $k$ the second pass multiplies by $\omega^{kr}$ and transforms across $r$ at a primitive $M$th root, where $\omega$ is the primitive $n$th root. The resulting column consists of $\widehat c(k+sL)$ for $0\le s<M$. To transform correlations each coefficient at $f$ must be multiplied by $\widehat c(-f)$. The input has $c_{-j}=\chi(g)^j c_j$. The program verifies this reflection on the sign table. At the first prime it therefore squares each coefficient. At the second prime it multiplies by the coefficient at $f+n/2$. Both coefficients are in the same column. After the inverse short transform it removes the twiddle and overwrites the same tile. The last pass inverts the long rows, reconstructs the signed integers and accumulates their squares. Every inverse transform includes its own length normalization. Each worker owns disjoint rows or tiles. The unlinked temporary file occupies exactly $4n$ bytes. [Exact NTT program](../../../scripts/probes/probe_sponsor_paley_rank_counts.cpp)

The calculation checks $R_0=n-1$, $\sum_hR_h=(\sum_jc_j)^2$, even parity and $|R_h|\le n-2$ for every nonzero displacement, and integrality of the final count. All odd displacements must vanish at the second prime, since reflection gives $R_{-h}=(-1)^hR_h$ while every autocorrelation is even under reversal. Eight independent cyclic bit rotations and population counts check displacements $1,2,63,64,65,\lfloor n/7\rfloor,n/2-1,n/2$, with the two terms incident to the zero site removed. The spectral check uses $E\le n(n-1)\Lambda^2$ with the previously certified operator-norm bounds.

The independent signed correlations in the order of the eight displacements above are $(-66650,29798,113066,27550,-11378,4882,62030,-65858)$ and $(0,55318,0,-52042,0,0,0,-2882)$. The production transforms used three workers and took 36.24 and 49.76 seconds with at most 215 MB resident on the verification host. A second pass on each entire input factored the transform as $2048\times524288$ and reproduced both receipts byte for byte. These reruns took 37.68 and 40.49 seconds with at most 250 MB resident.

## Reproduction

Build with C++17, GMP and GMPXX. Generate the two packed sign files as described in the [spectrum reproduction instructions](paley-production-spectrum.md). The independent Python check generates its small rows directly with Euler's criterion, expands all 24 determinant terms on every four-subset and compares every cyclic correlation at three factorizations. It checks 18 transforms, 288 individual coefficients, and 10,920 literal determinants across six boards. Two boards have nonsquare generators. At $p=113$, $g=35$ has order 16 and its $R_2,R_4,R_6$ are $-2,6,-10$, detecting permutations of the even offsets. [Control program](../../../scripts/probes/check_sponsor_paley_rank_counts.py)

```sh
c++ -O3 -std=c++17 scripts/probes/probe_sponsor_paley_rank_counts.cpp -lgmpxx -lgmp -o "$d/rank-counts"
for field in first second; do
  "$d/rank-counts" "$field" "$d/$field.bits" 1024 3 > "$d/$field.ranks"
  "$d/rank-counts" "$field" "$d/$field.bits" 2048 3 > "$d/$field.recheck"
  cmp "$d/$field.ranks" "$d/$field.recheck"
done
python3 -B -O scripts/probes/check_sponsor_paley_rank_counts.py "$d/rank-counts" \
  --receipts "$d/first.ranks" "$d/second.ranks"
```
