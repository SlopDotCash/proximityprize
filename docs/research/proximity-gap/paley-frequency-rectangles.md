# Half-size Paley rectangles at the production Fourier peaks

At the two prescribed primes, write $H=\langle g\rangle$, $n=2^{30}$, and $S_{ij}=\chi(g^i-g^j)$. There are explicit sets $A,B\subset H$ of size $2^{29}$ on which the signed sums are respectively **−51,808,432,890,192** and **−32,176,352,715,824**. In both cases the centered sum reaches more than 82% of the certified upper bound $n\Lambda/4$ for halves, where $\Lambda$ is the operator norm of $S$. The results are exact integer calculations on the full domains. [Certified input spectra and centered bounds](paley-production-spectrum.md) · [Rectangle verifier](../../../scripts/probes/probe_sponsor_paley_half_rectangles.cpp)

For the parameters in the table let $g_0=\gcd(k,n)$, $d=n/g_0$, $I=\{0,\ldots,d/2-1\}$, and read both membership tests modulo $d$:
$$
 B=\{g^j:(k/g_0)j\in I\},\qquad
 A_h=\{g^i:(l/g_0)i-h\in I\}.
$$

| Field | $k$ | $l$ | $d$ | $h$ | Centering term | Centered sum |
|---|---:|---:|---:|---:|---:|---:|
| First | 439,526,299 | 439,526,299 | 1,073,741,824 | 0 | −8,302,440,218,624 | −43,505,992,671,568 |
| Second | 388,143,450 | 925,014,362 | 536,870,912 | 8,388,608 | 0 | −32,176,352,715,824 |

## A Fourier frequency gives a rectangle of two halves

Put $c_j=\chi(1-g^j)$, $\omega=\exp(2\pi i/n)$, and $\lambda_k=\sum_j c_j\omega^{kj}$. Write $e=0$ if $\chi(g)=1$ and $e=n/2$ if $\chi(g)=-1$. Since $S_{ij}=\omega^{ei}c_{j-i}$, the input frequency $k$ maps to the output frequency $l=k+e\pmod n$. Suppose $4\mid d$. Both $k/g_0$ and $l/g_0$ are then odd and prime to the power of two $d$. Both halves have exactly $n/2$ points.

For $x=\mathbf1_B-\tfrac12\mathbf1$, $z=Sx$ and $Q_h=\langle\mathbf1_{A_h}-\tfrac12\mathbf1,z\rangle$, the best centered sum among these actual rectangles satisfies
$$
 \max_{0\le h<d}|Q_h|\ \ge\
 \frac{n|\lambda_k|}{2d\sin(\pi/d)}\ \ge\ \frac{n|\lambda_k|}{2\pi}.
$$
Indeed the unnormalized Fourier coefficient of $z$ at $l$ has magnitude $|\lambda_k|$ times the magnitude of the input coefficient of $x$ at $k$. The latter is $(n/d)\csc(\pi/d)$ by summing the geometric series over $I$. Now take the first Fourier coefficient in the **output phase** $h$. With $\zeta=\exp(2\pi i/d)$, summing $Q_h\zeta^{-h}$ first in $h$ gives a product of the Fourier coefficient of $z$ at $l$ and another half-interval sum of magnitude $\csc(\pi/d)$. For any real $q_h$,
$$
 \left|\sum_hq_h\zeta^{-h}\right|
 \le\|q\|_\infty\max_\theta\sum_h|\cos(2\pi h/d-\theta)|
 =2\csc(\pi/d)\|q\|_\infty .
$$
For the equality, the nonnegative cosines occupy a consecutive half of the circle, assigning either endpoint consistently in a tie. The full cosine sum vanishes, and the half-interval geometric sum attains its magnitude by a phase rotation. Combining the two evaluations gives the claimed bound. The proof supplies a finite search over $h$.

In the first field $S\mathbf1=s\mathbf1$ with $s=\sum c_j=-30{,}929$. Thus $S(A_h,B)=Q_h+ns/4$. The complementary half at $h+d/2$ changes the sign of $Q_h$, so the maximum raw magnitude is $|ns/4|+\max_h|Q_h|$. In the second field $S\mathbf1=s\eta$ with $s=-1{,}441$ and $\eta(g^i)=(-1)^i$. Both halves have as many even as odd indices because $d/2$ is even and the reduced phase multipliers are odd. Thus their parity sums vanish, as does the centering term $s(|A_h|\sum_B\eta+|B|\sum_{A_h}\eta)/n$. Here $S(A_h,B)=Q_h$.

The listed $k$ is the certified peak in each field. In the second field reflection gives $\lambda_{k+n/2}=\overline{\lambda_k}$. The two frequencies have the same residue in the first transform pass and are both sampled. Their common magnitude exceeds the certified upper bound 145,493 for all other sampled representatives, as the coarse estimate 146,018 has error at most 40 including rounding. [Fourier factorization and verification](paley-production-spectrum.md)

## Exact arithmetic for the prescribed sets

For $v\bmod d$ write $D(v)=\min(v,d-v)$ on representatives $0\le v<d$. At displacement $j$ the centered signs of the two half intervals have autocorrelation $d-4D((k/g_0)j+h)$ on one phase period. When $\chi(g)=-1$, a flip of index parity shifts the output phase by $d/2$ and flips its centered sign. This cancels the extra factor $(-1)^i$ in $S_{i,i+j}$. In both fields,
$$
 Q_h=\frac{n}{4d}\sum_{j=0}^{n-1} c_j\left[d-4D((k/g_0)j+h)\right].
$$

The program examines 256 evenly spaced phases. It accumulates the signed count and signed phase offsets in each bin in one pass through the sign file. The triangular weight is affine on each bin at every tested phase. It chooses the largest raw magnitude on this grid and verifies the selected value with a second scan of the raw overlaps. On the first field the weight for displacement $j$ is $(n/d)(d/2-D)$. On the second field, the $d/4$ odd phases in the input half subtract from the overlap, giving weight $(n/d)(d/4-D)$. On five small control domains, every phase at every frequency of order divisible by four was also checked by summing the entries $\chi(g^i-g^j)$ directly. The displayed production phases certify individual rectangles. A search for an optimum over all subsets is unnecessary.

After generating the sign files with the production spectrum recipe, run the following commands with GMP available to the compiler. [Sign-file reproduction](paley-production-spectrum.md#reproduction)

```sh
c++ -O3 -std=c++17 scripts/probes/probe_sponsor_paley_half_rectangles.cpp -lgmpxx -lgmp -o /tmp/half_rectangles
/tmp/half_rectangles first first.bits 439526299
/tmp/half_rectangles second second.bits 388143450
```
