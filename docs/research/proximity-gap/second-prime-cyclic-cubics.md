# Six Cyclic Lagrange Cubics Lower the Second-Prime Half-Rate MCA Upper Bound to `380,283,564`

## Status and Honesty Scope

- **100% kernel-checked Lean theorem (`ArkLib/Research/ProximityGap/Frontier/SecondPrimeCyclicCubics.lean`):**
  Proves unconditionally — with zero `sorry` and strictly standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) — that on the second named production prime `PrizeShapePrimeP30Second` (`N = 2^30 = 1,073,741,824`, `k = 2^29 = 536,870,912`, `B_2 = P / 2^128 = 2,147,483,648`), for every positive interleaving width:
  $$\frac{1}{2^{128}} < \frac{2{,}281{,}701{,}386}{P} \le \operatorname{epsMCA}\!\left(\mathrm{RS}(\mathrm{dom}, 2^{29})^{\bowtie w},\; \frac{380{,}283{,}564}{2^{30}}\right),$$
  and consequently
  $$\operatorname{mcaDeltaStar}\!\left(\mathrm{RS}(\mathrm{dom}, 2^{29})^{\bowtie w},\; \frac{1}{2^{128}}\right) \le \frac{380{,}283{,}564}{2^{30}}.$$
- **Bracket impact (second-prime half-rate MCA):**
  Lowers the proven operational upper bound from `387,740,104` (`SecondPrimeTetrahedron.lean`, $13/36\,n$) down to **`380,283,564`** ($17/48\,n + 1$) — a **`-7,456,540`-error improvement** (cutting `10.0%` off the remaining `[313,215,001, 387,740,104]` bracket).
- **Discovery attribution:**
  The zero-face-collinearity threshold (`D = 3, V = 6, H = 6`) and exact Lagrange cubic parameters were discovered by Engine 2's global secant-hypergraph optimizer (swarm `@prize-mapper`, board `#156`) and independently verified and formalized here.

---

## Geometric Mechanism: Escaping Face Collinearity

For any family of $H$ degree-$D$ Lagrange heads interpolating $(D+1)$-vertex blocks on $V$ vertex fibers of a quotient $\mu_M$ ($M \mid N$), any $(D+2)$-vertex subset spans a $1$-dimensional space modulo polynomials of degree $\le D$. Therefore **any three blocks lying inside a single $(D+2)$-vertex face are collinear at every non-vertex quotient fiber**:

| Construction | Parameters $(M, D, V, H)$ | Max blocks per $(D+2)$-face | Non-vertex foreign directions | Half-rate upper bound |
|---|---|---|---|---:|
| `SecondPrimeTetrahedron` | $(8, 1, 4, 6)$ | $\binom{3}{2} = 3$ (collinear!) | $3/5$ (forces off-head sites) | `387,740,104` |
| Degree-2 attempt | $(8, 2, 5, 6)$ | Pigeonhole $12 > 2\cdot 5$ (collinear!) | $[4,4,5,4,4,3]/5$ | no beat |
| **`SecondPrimeCyclicCubics`** | **$(8, 3, 6, 6)$** | **$6(6-4)=12 \le 2\cdot 6$ (max $2$!)** | **ALL $5/5$ distinct (zero off-head!)** | **`380,283,564`** |

Specifically, on the $8$-element quotient $t = X^{D_8}$ ($D_8 = 2^{27} = 134{,}217{,}728$, $z_8 = g^{D_8}$ primitive $8$th root of unity), we choose the $6$ vertex quotient classes $t_v = z_8^v$ ($v = 0, \dots, 5$) with planar coordinates $(U_v, V_v) = (v + 1, (v + 1)^2)$ and the $6$ cyclic $4$-vertex blocks
$$B_i = \{i,\; i+1,\; i+2,\; i+3\} \pmod 6 \qquad (i \in \mathrm{Fin}\ 6).$$
For each $i$, $(U_i(t), V_i(t))$ is the unique degree-$3$ Lagrange interpolant through $(t_v, U_v, V_v)$ for $v \in B_i$, lifted to degree $d = 3 D_8 = 402{,}653{,}184$ via $t = X^{D_8}$.

Theorem `zero_face_collinearity` in `SecondPrimeCyclicCubics.lean` certifies directly over $\mathbb{F}_P$:
1. At each vertex class $t_v$ ($v = 0, \dots, 5$), the $4$ incident heads agree identically, and the $2$ non-incident foreign heads have distinct slopes and $V_i(t_v) \ne V_v(t_v)$.
2. At both non-vertex classes $t_6 = z_8^6$ and $t_7 = z_8^7$, for **every** choice of owner $o \in \mathrm{Fin}\ 6$, all $5$ foreign heads $i \ne o$ satisfy $V_i(t_q) \ne V_o(t_q)$ and have pairwise distinct slopes against $(U_o(t_q), V_o(t_q))$.

---

## Exact 32 Quarter-Fiber Allocation and Integer Optimality

Decomposing $\mathrm{Fin}(2^{30})$ into $32$ quarter-fibers of size $S_{32} = 2^{25} = 33{,}554{,}432$ (four quarter-fibers per $\mu_8$ class):

- **$24$ vertex quarter-fibers ($r \bmod 8 \in \{0, \dots, 5\}$):** `cut r = 0`, `group r = {i : r % 8 ∈ B_i}` (size $4$), `own r = r % 8`. Total vertex sites: $a = 6 D_8 = 805{,}306{,}368$.
- **$6$ owned non-vertex quarter-fibers:**
  - `r = 6` (`cut = 11,184,811`, owner `0`, `22,369,621` owned sites),
  - `r = 14` (`cut = 11,184,811`, owner `1`, `22,369,621` owned sites),
  - `r = 22, 30, 7, 15` (`cut = 11,184,810`, owners `2, 3, 4, 5`, `22,369,622` owned sites each).
- **$2$ pure common-root quarter-fibers:** `r = 23, 31` (`cut = 33,554,432`, all sites in `roots`).

This yields:
- **Common roots:** $|\mathrm{roots}| = 134{,}217{,}726$, satisfying $|\mathrm{roots}| + 3 D_8 + 1 = 536{,}870{,}911 < k = 536{,}870{,}912$.
- **Defining cores:**
  $$|\mathrm{core}_i| = [693{,}458{,}259,\; 693{,}458{,}259,\; 693{,}458{,}260,\; 693{,}458{,}260,\; 693{,}458{,}260,\; 693{,}458{,}260].$$
  The label-mass theorem `label_mass` therefore holds for every dimension $536{,}870{,}912 \le k \le 693{,}458{,}259$ and every positive width, at error count $e = 2^{30} - (693{,}458{,}259 + 1) = 380{,}283{,}564$.
- **Bad-scalar mass:**
  $$\sum_{i=0}^{5} |(\mathrm{core}_i)^c| = 2{,}281{,}701{,}386 > \lfloor P / 2^{128} \rfloor = 2{,}147{,}483{,}648 \quad (\text{surplus } +134{,}217{,}738),$$
  with $\binom{2{,}281{,}701{,}386}{2} = 2{,}603{,}080{,}606{,}296{,}309{,}805 \le P$.
- **Exact optimality (`allocation_limit`):** Because $r \le 134{,}217{,}726$, $a \le 805{,}306{,}368$, $r + a + o \le 2^{30}$, and $6 c \le 6 r + 4 a + o$, any allocation on this 6-cubic cyclic arrangement satisfies $c \le 693{,}458{,}259$, so `380,283,564` is its exact integer optimum.

---

## Verification and Reproduction

- **Lean kernel verification:**
  ```bash
  scripts/pg-iterate.sh ArkLib/Research/ProximityGap/Frontier/SecondPrimeCyclicCubics.lean
  ```
- **Independent Python verification (Lagrange reconstruction + small-scale literal `n=64, k=32` brute-force check):**
  ```bash
  python3 scripts/probes/probe_second_prime_cyclic_cubics.py
  ```
