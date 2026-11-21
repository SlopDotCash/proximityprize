# Arbitrary-center list bounds from doubly constant-weight codes

Write $B=\lfloor p/2^{128}\rfloor=370883555463132043592346312614163$ for the budget of the [237-bit large-period field](dyadic-locator-sum-barrier.md). A selected set of $t$ agreement coordinates for each list member gives distinct $t$-sets whose pair intersections have size at most $s=k-1$. This applies to every center, every evaluation domain and every interleaving width.

Fix a sample $R$ of $w$ coordinates and put $z=n-w$. Consider the $M$ selected blocks having exactly $a$ sites in $R$, and put $b=t-a$. If $d_x$ counts these blocks at site $x$, summing intersections of ordered pairs gives
$$
\sum_x d_x^2\le M(t+(M-1)s).
$$
Cauchy–Schwarz on $R$ and its complement gives
$$
M(a^2 z + b^2w)\le wz(t+(M-1)s).
$$
Thus when $h=a^2 z+b^2 w-wzs>0$, a sample accommodates at most $L=\lfloor wz(t-s)/h\rfloor$ blocks. Each block meets the sampling condition for exactly $\binom{t}{a}\binom{n-t}{w-a}$ samples. Double counting gives the upper bound
$$
\left\lfloor\frac{L\binom nw}{\binom ta\binom{n-t}{w-a}}\right\rfloor.
$$
The argument uses the standard doubly constant-weight method. Agrell, Vardy and Zeger survey this class of bounds. [Paper](https://publications.lib.chalmers.se/records/fulltext/local_14986.pdf)

| Length | Dimension | Agreements ensuring budget | Sample $w,a,L$ | List upper bound |
|---:|---:|---:|---|---:|
| 128 | 64 | 67 | 61, 2, 31 | 159598306393419780652533884799913 |
| 1024 | 512 | 702 | 131, 31, 363 | 71764836271731011775138363199827 |
| 1024 | 256 | 479 | 389, 269, 479 | 66858415015215185528470727407374 |
| 1024 | 128 | 315 | 128, 98, 320 | 204297278419959661436514180494206 |
| 1024 | 64 | 191 | 58, 50, 187 | 341180555263439633607425896932496 |

These length-1024 agreement counts improve strict Johnson by 22, 32, 46 and 63 sites. They apply to the actual subgroup with exceptionally large Fourier period. The guarantee holds throughout each real-radius interval forcing the indicated agreement. [Lean upper bounds](../../../ArkLib/Research/ProximityGap/Frontier/AgreementSlicePacking.lean)

## A single remaining Hamming step at length 128

On the order-128 subgroup in the same prime field, the prescribed-product construction at dimension 64 exceeds budget at 65 agreements since $128B<\binom{128}{65}$. The upper bound at 67 agreements leaves the exact decision at 66 agreements, or 62 errors. [Prescribed-product lower bound](../../../ArkLib/Research/ProximityGap/Frontier/PrescribedProductList.lean)

Every bound that uses only block sizes and pairwise intersection sizes faces an obstruction at this endpoint. Label the 128 coordinates by distinct elements of the auxiliary field of order 131. Color a 66-set by the coefficients of degrees 64 and 65 of its monic locator. Equal-colored distinct locators have a nonzero difference of degree below 64. Thus equally colored blocks intersect in at most 63 sites. Some color has more than $B$ members since $131^2 B<\binom{128}{66}$. The construction produces abstract supports. Realizing these supports at one received word in the 237-bit field requires additional algebraic conditions. [Lean obstruction](../../../ArkLib/Research/ProximityGap/Frontier/AgreementSupportBarrier.lean)

At length 1024, the same Lean theorem with 1031 auxiliary labels gives over-budget support families at 600, 338, 186 and 99 agreements at the four rates. A stronger elementary greedy calculation gives 658, 409, 238 and 123. Select a $t$-set and discard every remaining set meeting it in at least $k$ sites. Each selection discards at most $V=\sum_{j=0}^{\min(t-k,n-t)}\binom tj\binom{n-t}j$ sets, including itself. The integer inequality $BV<\binom nt$ proves that more than $B$ selections are necessary. The probe checks this separate greedy calculation and the neighboring parameter values with exact integers. [Arithmetic replay](../../../scripts/probes/probe_agreement_slice_packing.py)
