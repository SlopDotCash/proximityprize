# The full Paley spectrum on the two production subgroups

Let $H=\langle g\rangle$ be the order-$n$ code domain, $n=2^{30}$, at either named prime. For the quadratic character $\chi(0)=0$, define $S_{ij}=\chi(g^i-g^j)$. Its operator norm $\Lambda$ is the best constant in the bilinear inequality for arbitrary real or complex weights. A full Fourier calculation gives the following certified intervals. The primes and generators used here have Lean certificates. [First field](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30.lean) · [Second field](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30Second.lean)

| Production field | Row sum at 1 | Previous upper bound | Certified interval for $\Lambda$ | Refined frequencies among the sampled representatives | Upper bound for the other sampled frequencies |
|---|---:|---:|---:|---:|---:|
| First | −30,929 | 449,676 | **[197,062, 197,063]** | 1 | 192,366 |
| Second | −1,441 | 448,831 | **[146,017, 146,018]** | 2 | 145,493 |

The field orders in table order are $365375409332725729550921208179070755120141565953$ and $730750818665451459101842416358141509841924915201$. The rounded coarse maxima are 197,063 at frequency 439,526,299 on the first field and 146,018 at frequency 388,143,450 on the second. The lower bounds in the table come from the direct Fourier sums at the refined frequencies. Conjugate frequencies have the same magnitudes. For two sets of size at least $2^{20}$ the respective relative discrepancies are below 0.188 and 0.140.

For arbitrary $A,B$ in one specified affine copy $t+cH$ with $c\ne0$,
$$
 \left|\sum_{a\in A,b\in B}\chi(a-b)\right|\le \Lambda\sqrt{|A||B|}.
$$
Indeed, translation cancels and dilation multiplies the matrix by $\chi(c)$. Applying its operator norm to the two indicator vectors gives the inequality, including for intersecting sets. The exact ordered edge count equals $(|A||B|-|A\cap B|+\sum\chi(a-b))/2$. The graph on the entire prime field and the uniform asymptotic estimate for arbitrary subsets remain separate questions.

## Every projective image, including its pole

Use the lifts $v_x=(x,1)^t$ for finite $x$ and $v_\infty=(1,0)^t$. The signed Paley conference matrix on $\mathbf P^1(\mathbb F_p)$ has entries $C(x,y)=\chi(\det[v_x,v_y])$. It agrees with $\chi(x-y)$ on the affine chart. Both primes have $\chi(-1)=1$, so the entries incident to infinity are $+1$ off the diagonal. In particular $CC^t=pI$. For distinct finite rows $x,z$, the finite inner product is $-1$ because $y\mapsto(x-y)/(z-y)$ runs through $\mathbb F_p\setminus\{1\}$ away from $z$. Infinity contributes $+1$. Each finite row has inner product zero with the infinity row, and each row has squared length $p$.

Let $\gamma\in\mathrm{PGL}_2(\mathbb F_p)$ be represented by $M$. Write $Mv_x=\ell_x v_{\gamma x}$, using the unique nonzero multiplier even at the pole. Taking determinants gives
$$
 C(\gamma x,\gamma y)=\chi(\det M)\,\chi(\ell_x)\chi(\ell_y)C(x,y).
$$
After indexing by preimages, the principal matrix on $\gamma H$ is thus the matrix on $H$ conjugated by a diagonal sign matrix and multiplied by one global sign. **Every projective image has exactly the singular values certified above.** The bilinear bound therefore holds with the same $\Lambda$ for arbitrary complex weights supported on any prescribed image, including one containing infinity. Restricting the weights to finite points gives the ordinary Paley graph estimate. This fixed-chart statement complements the [chart-averaged estimates for arbitrary supports](paley-support-ranks.md).

There is also a bound for sets that meet several images. For arbitrary $A,B\subseteq\mathbf P^1(\mathbb F_p)$ let $D=\sum_{x\in A,y\in B}C(x,y)$. Choose rectangles $A_i\times B_i\subseteq A\times B$ with $A_i,B_i\subseteq\gamma_i H$. Give them weights $t_i\ge0$ so that the weights covering each ordered pair sum to at most one. With $u_i=|A_i||B_i|$,
$$
 |A||B|-|D|\ \ge\ \sum_i t_i\max\{0,u_i-\Lambda\sqrt{u_i}\}.
$$
To see this, choose $\sigma\in\{\pm1\}$ with $\sigma D=|D|$. Each $1-\sigma C(x,y)$ is nonnegative, and its sum on rectangle $i$ is at least $u_i-\Lambda\sqrt{u_i}$. For example, partition $A$ and $B$ into two parts each of size $m$. If each matching pair of parts lies in a projective image, the two images may differ and the cross pairs may be arbitrary. The relative discrepancy is at most $1/2+\Lambda/(2m)$, below $0.594$ and $0.570$ respectively at $m=2^{20}$.

The coverage restriction already matters at square-root size. At either named prime there exists an affine $A$ of size $\lfloor\sqrt p\rfloor$ meeting **every** projective image of $H$ in at most nine points. Choose $A$ uniformly at that size. Each fixed ten-point affine subset is contained in $A$ with probability at most $p^{-5}$. There are fewer than $p^3$ projective maps and at most $n^{10}$ candidate ten-point subsets per image. A union bound gives failure probability less than $n^{10}/p^2<2^{-16}$. For $B=A$ of this form every term of the rectangle bound vanishes. Averaging the norm estimate over all images also yields only $|D|\le\Lambda p\sqrt{|A||B|}/(n-1)$. Indeed a point is covered with probability $n/(p+1)$, and a distinct pair with probability $n(n-1)/(p(p+1))$ by double transitivity. Apply Cauchy–Schwarz to the averaged product of square roots. Its coefficient exceeds the ambient $\sqrt p$ at both primes. A uniform power saving for arbitrary sets still needs an estimate beyond the two induced spectra.

## Degrees and the centered estimate

Write $s=\sum_{j=0}^{n-1}\chi(1-g^j)$. At the first prime the generator is a square, so all vertices have degree $(n-1+s)/2$ and the ordered signed sum on all of $H$ is $ns$. The degree is 536,855,447, the signed sum is −33,209,760,874,496, and the number of undirected edges is 288,222,073,443,057,664. For $A,B\subseteq H$ with sizes $a,b$, removing the constant direction gives
$$
 |S(A,B)-sab/n|\le\Lambda\sqrt{(a-a^2/n)(b-b^2/n)}.
$$
At the second prime, put $\eta(g^i)=(-1)^i$ and $w_A=\sum_{u\in A}\eta(u)$. The rows have sum $s\eta$ and vertex $u$ has degree $(n-1+s\eta(u))/2$. The two degrees are 536,870,191 and 536,871,632. The ordered signed sum on all of $H$ is zero and there are 288,230,375,883,276,288 undirected edges. In this case
$$
 \left|S(A,B)-s(a w_B+b w_A)/n\right|
 \le\Lambda\sqrt{(a-(a^2+w_A^2)/n)(b-(b^2+w_B^2)/n)}.
$$
For the proof, $S$ sends $1$ to $s\eta$ and $\eta$ to $s1$. The first assertion follows by simultaneous scaling, and the second follows by the same scaling and symmetry of $S$. The functions $1,\eta$ are orthogonal with squared norm $n$. Projecting the indicator vectors off their span gives the stated inequality.

## Fourier factorization

Write $c_j=\chi(1-g^j)$. Then $S_{ij}=\chi(g)^i c_{j-i}$. Multiplication by the diagonal sign matrix preserves singular values. The singular values of the resulting circulant are the magnitudes of the discrete Fourier transform of $c$. Reflection gives $c_{-j}=\chi(g)^jc_j$ because $\chi(-1)=1$. The sign-vector generator uses exact GMP Jacobi symbols for $0\le j<n/2$, verifies each modular orbit endpoint, and handles $j=0,n/2$ separately. It reproduces the earlier independent row counts. [Sign generator](../../../scripts/probes/probe_sponsor_paley_signs.cpp) · [Earlier scan](../../../scripts/probes/probe_sponsor_paley_row.cpp)

Take $M=1024$, $L=n/M$, and $e_N(t)=\exp(2\pi i t/N)$. For $0\le r<M$ define
$$
 b_r(k)=\sum_{j=0}^{L-1}c_{r+Mj}e_L(kj),\qquad v_r(k)=e_n(kr)b_r(k).
$$
The length-$M$ Fourier transform of $v_r(k)$ has entries $\widehat c(k+mL)$ for $0\le m<M$. For $0<r<M/2$, reflection gives $v_{M-r}(k)=\chi(g)^r\overline{v_r(k)}$. Conjugating the output covers negative frequencies. Computing $0\le r\le M/2$ and $0\le k\le L/2$ therefore covers every magnitude. The earlier transform retained only block magnitudes. The full transform retains the phases needed for recombination. [Full transform](../../../scripts/probes/probe_sponsor_paley_full_spectrum.cpp) · [Earlier block envelope](../../../scripts/probes/probe_sponsor_paley_spectrum.cpp)

## Integer error certificate

Use root scale $T=2^{40}$, data scale $Q=2^{30}$ and packing scale $P=1024$. The square-root enclosures for each half-angle start at $\cos(\pi/2)=0$ and use integer square roots with denominator $2^{192}$. Each binary anchor coordinate lies within $2/T$ of its exact value. Integer complex rotations truncate each output coordinate with error less than one output unit. At successive binary products the root error is bounded by $7j/T$ after $j\le30$ rotations, since the next error is at most $(1+4/T)7j/T+6/T$. A twiddle formed from a product of two tabulated roots consequently has error below $424/T$. [Shared fixed-point routines](../../../scripts/probes/sponsor_paley_fft.hpp)

In a radix-two butterfly stage with exact input norm at most $B\ge1$ and error at most $Be$, the output error divided by $2B$ is at most $e+210(1+e)/(2T)+1/(BQ)$. Thus each stage adds at most $210/T+1/Q$ while $e\le1$. Packing a first-pass result contributes less than $2/P$ in Euclidean norm. Its magnitude after packing is at most $2L$, so the second-pass twiddle contributes at most $848L/T+2/Q$. Starting the second transform with these errors and propagating through $M$ points gives uniform absolute error at most
$$
 E=\left\lceil n\log_2 n(210/T+1/Q)+2M/P+848n/T+2M/Q\right\rceil=39.
$$
The intermediate normalized errors are below one. All intermediate FFT coefficients fit signed 64-bit words. Scaled rotation products and squared magnitudes fit signed 128-bit words. The integer comparisons in the magnitude calculation certify the rounded square root independently of its floating-point starting guess.

The program retains the sixteen largest approximate magnitudes (rounded up) and bounds every discarded frequency by the smallest retained ceiling plus $E$. It directly recomputes all contenders whose error intervals still intersect a lower bound on the maximum. This final direct sum uses $T'=2^{52}$, splits $j$ into two parts, and sums blocks of $2^{15}$ signs using fine roots before rotating the block by its coarse root. The two individual roots each have error at most $210/T'$; their product has error below $421/T'$. The block truncations add at most $2/T'$ per block. Thus the computed vector scaled by $T'$ has Euclidean error at most $422n$ in integer units. An exact GMP square root, with its final one-unit interval, yields integer bounds on each true magnitude. The temporary per-block products fit signed 128-bit words since their absolute values are at most $2\cdot 2^{15}(2T')^2$. The final magnitude uses GMP integers.

## Reproduction

The program bounds its first transform length by $2^{20}$, its second length by 2048, and its worker count by four. The temporary row file for the production run occupies 2,151,682,056 bytes. It closes automatically after the transform. The complete three-worker transforms took 50.75 and 63.49 seconds on the verification host and peaked below 219 MB resident. Building the two sign files took 97.21 and 218.70 seconds. On little-endian systems the two 128 MiB sign-vector SHA-256 values in field order are `d197a97e55a6a3bdce7a13a0727e6991918aa613fe14258341fcbb7ca30b753d` and `5c869aca0b411bb192525d7484e518beb3fc530610175017923cb282e5422264`.

From the repository root, use C++17, GMP, GMPXX and Python 3. Set the include and library paths for the local GMP installation if needed. The independent control uses Euler's criterion for every entry and direct Fourier sums at every frequency. It checks both character signs for the generator, multiple factorizations for each row, every bit of each sign file, and the final norm intervals. It compares 4,096 individual frequencies across five rows. Over the fields of orders 17 and 97 it also checks every entry of the conference identity and of the signed projective transformation law for a translation, a map with a subgroup pole, and a nonsquare dilation. Each map supplies a test of the rectangle bound. [Control program](../../../scripts/probes/check_sponsor_paley_full_spectrum.py)

```sh
d=$(mktemp -d)
c++ -O3 -std=c++17 scripts/probes/probe_sponsor_paley_signs.cpp -lgmpxx -lgmp -o "$d/signs"
c++ -O3 -std=c++17 scripts/probes/probe_sponsor_paley_full_spectrum.cpp -lgmpxx -lgmp -o "$d/full"
python3 -O scripts/probes/check_sponsor_paley_full_spectrum.py "$d/signs" "$d/full"
for field in first second; do
  "$d/signs" "$field" "$d/$field.bits" 3
  "$d/full" "$field" "$d/$field.bits" 1024 3
done
```
