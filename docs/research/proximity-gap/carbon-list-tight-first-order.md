# Derivative-Capped Tight First-Order List Bounds and Smooth Production Rank Brackets

## Overview

In the existing first-order hidden-derivative formalizations
([`ScaledFirstOrderSecurity.lean`](../../../ArkLib/Research/ProximityGap/Frontier/ScaledFirstOrderSecurity.lean),
[`FineGridFirstOrderSecurity.lean`](../../../ArkLib/Research/ProximityGap/Frontier/FineGridFirstOrderSecurity.lean),
and [`FineGridWideLists.lean`](../../../ArkLib/Research/ProximityGap/Frontier/FineGridWideLists.lean)),
linear worst-center list bounds were extracted from shifted coefficient-slot certificates via
`finite_firstOrder_list_bound_of_heightSlotCount_sharp`. That theorem charges every order-one
separant stage $(j, r)$ by the uncapped product $j(1 + 2K(j - 1)) \cdot \frac{n}{A - k + 1}$.

In [`CarbonListTightFirstOrder.lean`](../../../ArkLib/Research/ProximityGap/Frontier/CarbonListTightFirstOrder.lean)
(companion arithmetic verifier:
[`probe_carbon_list_tight_first_order.py`](../../../scripts/probes/probe_carbon_list_tight_first_order.py)),
we prove a uniform-in-$b$ scaling theorem for the dimension-sensitive derivative-capped bound
`finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight` ([DKT26],
[`ListBound.lean`](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/ListBound.lean))
at exponent $\tau = 2K - 3$, and transport it across arbitrary finite domain index types $I$ and
arbitrary finite interleaving widths over **every** field $F$ with
$\operatorname{char}(F) = 0$ or $n \le \operatorname{char}(F)$.

## Key Mathematical Ingredients

1. **Derivative-capped mixed-volume scaling (`stageOne_le_scaled`)**:
   At ambient dimension $K = b k$ ($b \ge 1, k \ge 2$) and standard exponent $\tau = 2(bk) - 3$,
   every order-one separant stage $(j, r)$ with $1 \le r \le j$ has total Taylor cap
   $b_{\mathrm{cap}} = 1 + (2bk - 3)(j - 1)$ and first-derivative cap
   $c_{\mathrm{cap}} = \min(b_{\mathrm{cap}}, (2bk - 3)(r - 1) + (bk - 1))$.
   Rewriting `firstOrderCurveFiberStageOne` via `cappedDegreeMixedVolume_eq` into the
   subtraction-free form $(j - r) c_{\mathrm{cap}} + r b_{\mathrm{cap}}$ yields:
   - for $j = 1$ ($r = 1$), exact stage charge $1 \le b$;
   - for $j \ge 2$, $b_{\mathrm{cap}} \le b \cdot 2k(j - 1)$ and
     $c_{\mathrm{cap}} \le b \cdot \min\bigl(2k(j - 1),\, k(2r - 1)\bigr)$.
2. **Dimension-sensitive agreement ratio (`ratio_le_scaled`)**:
   Whenever $k < A \le N$,
   $$\frac{bN - bk + 1}{bA - bk + 1} \;\le\; \frac{N - k}{A - k},$$
   because $(b(N - k) + 1)(A - k) \le (N - k)(b(A - k) + 1) \iff A - k \le N - k$.
3. **Field-uniform rational-function packing (`tight_interleaved_list_of_slots`)**:
   Using `ringChar (RatFunc F) = ringChar F` from injectivity of `algebraMap F (RatFunc F)` and
   coordinate reindexing $I \simeq \operatorname{Fin}(bN)$, a single finite integer inequality
   `tightCostHolds N k A μ M C` together with `rowSlots N m M μ h < columnSlots k A m M μ h`
   certifies $\Lambda(\operatorname{RS}(D, bk)^{\bowtie \text{width}}, 1 - A/N) \le C(bN)$ over
   every eligible field (not merely prime fields $\mathbb{F}_p$).

## Concrete Improvements and New Regimes

### 1. Slashing All 12 Published Linear List-Size Constants (`4.94×`–`8.88×`)

| Family | Rate | Closed radius | Old linear bound | New tight bound | Factor |
| :--- | :---: | :---: | ---: | ---: | :---: |
| `128b` | $1/2$ | $39/128$ | $173{,}373\,n$ | **$19{,}522\,n$** | $8.88\times$ |
| `128b` | $1/4$ | $67/128$ | $113{,}975\,n$ | **$21{,}491\,n$** | $5.30\times$ |
| `128b` | $1/8$ | $86/128$ | $58{,}872\,n$ | **$11{,}002\,n$** | $5.35\times$ |
| `128b` | $1/16$ | $99/128$ | $52{,}349\,n$ | **$8{,}811\,n$** | $5.94\times$ |
| `4096b` | $1/2$ | $1262/4096$ | $3{,}722{,}270\,n$ | **$441{,}892\,n$** | $8.42\times$ |
| `4096b` | $1/4$ | $2166/4096$ | $3{,}891{,}790\,n$ | **$755{,}543\,n$** | $5.15\times$ |
| `4096b` | $1/8$ | $2780/4096$ | $4{,}624{,}878\,n$ | **$929{,}137\,n$** | $4.98\times$ |
| `4096b` | $1/16$ | $3195/4096$ | $5{,}864{,}546\,n$ | **$1{,}077{,}546\,n$** | $5.44\times$ |
| `4096b` wide | $1/2$ | $1269/4096$ | $1{,}369{,}562{,}863\,n$ | **$164{,}423{,}839\,n$** | $8.33\times$ |
| `4096b` wide | $1/4$ | $2174/4096$ | $649{,}560{,}740\,n$ | **$127{,}463{,}408\,n$** | $5.10\times$ |
| `4096b` wide | $1/8$ | $2788/4096$ | $2{,}486{,}297{,}660\,n$ | **$503{,}349{,}611\,n$** | $4.94\times$ |
| `4096b` wide | $1/16$ | $3201/4096$ | $615{,}760{,}719\,n$ | **$115{,}572{,}934\,n$** | $5.33\times$ |

### 2. New Low-Budget ($C \le 407$) and Ultra-Fine ($N = 65536$) Families

Because challenge-height degree $h$ enters shifted row/column slot counts linearly and is absent
from `firstOrderTightListWeight`, constant received curves enjoy unrestricted height slack:

- **Low-budget $M = 3$ family (`low_budget_4096_interleaved_bounds`)**: certifies closed radii
  $1215/4096$, $2089/4096$, $2695/4096$, and $3116/4096$ with tiny linear constants
  $(407, 341, 263, 222) \cdot n$ (requiring only $|F| \ge 2^{167}$ at $n = 2^{30}$).
- **Ultra-fine $N = 65536$ family (`ultra_fine_65536_interleaved_bounds`)**: certifies closed radii
  $20314/65536$, $34801/65536$, $44611/65536$, and $51226/65536$ — strictly exceeding all four
  radii of `FineGridWideLists` — with linear constants
  $(1{,}254{,}436{,}992,\, 944{,}087{,}037,\, 455{,}358{,}934,\, 266{,}313{,}397) \cdot n < 2^{31} n$.

### 3. Upgraded Two-Sided Smooth List Rank Brackets at $n = 2^{30}$

Previously, [`SmoothListRankBracket.lean`](../../../ArkLib/Research/ProximityGap/SmoothListRankBracket.lean)
bracketed `RankReview.listAnswer` from below only at the single-step Johnson threshold
$n - \operatorname{agreements}(n, k) + 1$. Since list decoding incurs a linear $O(n)$ (rather than
quadratic $O(n^2)$) field-budget cost, `prime_production_rank_brackets` upgrades the exact
128-bit list threshold $e$ on **every** smooth length-$2^{30}$ domain in $\mathbb{F}_p$ for
$2^{189} \le p < 2^{256}$ (including `FourRateListPrime246.K`, the BLS12-381 scalar field, and the
Pasta Pallas/Vesta fields; meanwhile `ultra_fine_65536_interleaved_bounds` covers arbitrary
non-smooth length-$2^{30}$ injective domains over BN254, Ed25519, and Secp256k1, and
`first_failure_fine_grid` covers BN254's smooth subgroup up to $2^{28}$) at every positive
interleaving width:

- **Rate $1/2$**: $332{,}824{,}577 \le e \le 528{,}482{,}305$ ($+18{,}332{,}876$ above Johnson)
- **Rate $1/4$**: $570{,}179{,}585 \le e \le 796{,}917{,}761$ ($+33{,}308{,}670$ above Johnson)
- **Rate $1/8$**: $730{,}906{,}625 \le e \le 931{,}135{,}489$ ($+36{,}789{,}861$ above Johnson)
- **Rate $1/16$**: $839{,}286{,}785 \le e \le 1{,}002{,}438{,}657$ ($+33{,}980{,}413$ above Johnson)
