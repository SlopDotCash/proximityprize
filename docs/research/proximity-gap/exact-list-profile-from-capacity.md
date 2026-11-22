# Exact interleaved Reed–Solomon list sizes from $n-k$ errors to radius one

Let $D$ consist of $n$ distinct points of $\mathbb F_q$, let $1\le k\le n$, and let $m\ge1$ be the interleaving width. Write $Q=q^m$. Let $L_t$ be the maximum, over received words, of the number of codewords agreeing in at least $t$ columns. The closed ball at Hamming radius $n-t$ has this list size.

For $t=0$, every center has $L_0=Q^k$. For $1\le t\le k$, put $b=(k-t)\bmod 2$, $\ell=k-b$ and $a_j=(-1)^{j-t}\binom{j-1}{t-1}$. Then
\[
L_t=\sum_{j=t}^{\ell}a_j\binom nj Q^{k-j}
        -b\left(\sum_{j=t}^{\ell}a_j\binom nj-1\right).
\]
In particular, $L_k=\binom nk$, and $L_{k-1}=1+(Q-1)\binom n{k-1}$ for $k\ge2$. When $n>k$, even $k-t$ gives equality precisely at centers whose largest agreement is $k$. Odd $k-t$ gives equality precisely at codeword centers. When $n=k$, every center is a codeword, has largest agreement $k$, and attains the maximum at every radius.

## Counting agreements

Fix a received word $y$. Write $s_c$ for the number of agreements with codeword $c$. Interpolation on $j$ coordinates, independently in each row, gives
\[
\sum_c\binom{s_c}{j}=\binom nj Q^{k-j}\qquad(0\le j\le k).
\]
Set $P(s)=\sum_{j=t}^{\ell}a_j\binom sj$. This agrees with $\mathbf1_{s\ge t}$ on $0\le s\le\ell$. To see this, take first differences using Pascal's identity. Starting at $s=t-1$ gives difference one. For $t\le s<\ell$ the complete alternating binomial sum gives zero. For $s\ge\ell$, the truncated alternating binomial sum yields
\[
 P(s+1)-P(s)=\binom{s}{t-1}\binom{s-t}{\ell-t},
\]
since $\ell-t$ is even. Thus $P$ majorizes the indicator, with strict inequality at $s>\ell$.

If $b=0$, summing this majorant gives the stated bound. A center whose first row is $X^k$ and whose other rows are zero has $s_c\le k$ for every $c$, by the polynomial root bound. It attains the maximum. Interpolation on any $k$ positions ensures that the largest agreement is always at least $k$.

If $b=1$, let $R(s)=P(s)-1$ for $s\ge\ell=k-1$. Both $R(s)$ and $\binom sk$ start at zero at $s=\ell$. The ratio of their positive first differences at $s\ge\ell$ is
\[
\frac{\binom{s}{t-1}\binom{s-t}{\ell-t}}{\binom{s}{\ell}}
=\frac{(\ell-t+1)\binom{\ell}{t-1}}{s-t+1}.
\]
This decreases strictly with $s$. The ratio $R(s)/\binom sk$, for $s\ge k$, is a running weighted average of these first-difference ratios, hence decreases strictly. The total excess of the majorant therefore satisfies
\[
\sum_{c:s_c\ge k} R(s_c)\ \ge\
  \frac{R(n)}{\binom nk}\sum_c\binom{s_c}{k}=R(n).
\]
At a codeword center exactly one word has $s_c=n$, and distinct words agree in at most $k-1$ columns. This attains equality. If $n>k$, strictness forces every $s_c\ge k$ to equal $n$. Interpolation supplies such a word, so the center itself is a codeword.

## Prior bounds and MDS coset weights

For a uniformly random codeword, let $A_i$ mean that it agrees with the center at coordinate $i$. In the notation of Adler, Karp and Ross, the number $X$ of occurring events is the agreement count, and the intersection sum is $S_j=\binom njQ^{-j}$ for $j\le k$. Their Theorem 2 with event threshold $r=t$ and truncation order $k$ gives the even-parity Bonferroni upper bound. For odd $k-t$, their Theorem 3 at truncation order $k-1$ subtracts $R(n)S_k/\binom nk$ from the upper bound. Multiplying by $Q^k$ gives the two bounds above. The authors trace the sharpened coefficient to earlier work by Mărgăritescu and by Galambos and Simonelli. Here the Reed–Solomon extremizers attain these probability bounds, and strictness gives the equality cases. [Adler, Karp and Ross, Theorems 2–3](https://arxiv.org/html/2505.12243#S3) · [Local PDF](https://arxiv.org/abs/2505.12243)

A column alphabet of size $q^m$ can be identified with $\mathbb F_{q^m}$ by a choice of basis over $\mathbb F_q$. In this representation the interleaved code is a scalar Reed–Solomon code over the extension. Agreements with a center correspond to weights in its coset. Davydov, Marcugini and Pambianco present Bonneau's formula for the weight distribution of each MDS coset in Theorem 2.4. Their Theorem 4.2 gives the deep-hole shell size $\binom nk$ at radius $n-k$. The argument above compares cumulative weights across all centers. [MDS coset weight distributions](https://arxiv.org/abs/2101.12722) · [Local PDF](https://arxiv.org/abs/2101.12722)

The executable check enumerates every coset of each tested code, counts agreements directly, and compares both maximum values and all equality cases. It also checks every applicable weight shell against Bonneau's original formula, equations (2.2)–(2.4), and tests the finite-difference identities with integer arithmetic. Run it with Python's optimization flag to retain the explicit verification checks. [Exact coset enumeration](../../../scripts/probes/probe_mds_capacity_list_profile.py)

The formula covers the real radii $\delta\in[1-k/n,1]$ by taking $t=n-\lfloor n\delta\rfloor$. Agreement thresholds $t>k$ constitute the remaining interior list-decoding problem. The general profile here has a written proof and executable checks.
