# Sharp Kopparty–Sha Appendix A / Core-Weighted Mixed-Hasse Obstruction at Both Second-Prime Johnson Pivots

`SecondPrimeJohnsonPivot` reduces the strict Johnson comparison for the second benchmark prime
($n = 2^{30}$, tolerance $2^{-128}$, budget $B_2 = 2^{31}$) to the single closed MCA error counts:

- **Half-rate pivot ($1/2$):** $d = 2^{29} - 1 = 536{,}870{,}911$, $e = 314{,}491{,}699$,
  $t = 759{,}250{,}125$, Johnson excess $\delta = t^2 - n d = 1{,}082{,}833{,}961$.
- **Quarter-rate pivot ($1/4$):** $d = 2^{28} - 1 = 268{,}435{,}455$, $e = 536{,}870{,}913$,
  $t = 536{,}870{,}911$, Johnson excess $\delta = t^2 - n d = 1$.

A natural attempt to recover ordinary mixed-Hasse interpolation room near Johnson is
Kopparty–Sha's Appendix A factored-surface / core-weighted interpolation
($P = (Y - h)^K Q$), lowering site jet multiplicity from $r$ to $r - K$ on a heavy affine
head's joint core $U$ while reducing the weighted-degree cap from $r t$ to $r t - d K$.

[`PivotFactoredObstruction.lean`](../../../ArkLib/Research/ProximityGap/Frontier/PivotFactoredObstruction.lean)
(independently checked by [`pivot_factored_obstruction.py`](../../../scripts/probes/pivot_factored_obstruction.py))
proves **exact, unconditional obstruction theorems** showing that no Kopparty–Sha Appendix A /
core-weighted ordinary mixed-Hasse surface with core size $|U| \le t$ can avoid overflowing the
$2^{31}$ budget at either pivot.

## Verified Theorems (Zero `sorry`, Zero Custom Axioms)

1. **MCA Fresh-Agreement Head Cap (`mcaEvent_fresh_site_of_head`, `mcaEvent_head_budget_le`):**
   Every MCA-bad scalar $\gamma$ witnessed by an affine head $v_0 + \gamma v_1$ with joint core
   $U = \{i : v_0(i) = u_0(i) \land v_1(i) = u_1(i)\}$ must agree at a fresh site $i \notin U$,
   pinning $\gamma = -(v_0(i) - u_0(i)) / (v_1(i) - u_1(i))$. Hence that head carries at most
   $n - |U|$ MCA-bad scalars. In particular, super-threshold heads ($|U| > t$) strictly shrink
   their own MCA budget below $e = n - t$, whereas all canonical below-threshold / no-CA cores
   satisfy $|U| \le t - 1 < t$.

2. **Universal Multi-Core Continuous Obstruction (`kopparty_sha_multicore_continuous_obstruction`,
   `kopparty_sha_multicore_strict_loss`):**
   For any $n, d, t, r, K, H \in \mathbb{Z}$ with $d, t, r > 0$, $t^2 \ge n d$, $0 \le H \le t$,
   and $0 \le d K \le r t$, the exact sum-of-squares identity
   $$
   t\bigl(t H^2 - 2 n d H + n d t\bigr) = (t H - n d)^2 + n d (t^2 - n d) \ge 0
   $$
   proves
   $$
   n(r t - d K)^2 - d(n r - K H)^2 \le n r^2 (t^2 - n d),
   $$
   with **strict loss** whenever $K > 0$ and ($t^2 > n d$ or $H < t$). Lowering multiplicities on
   any number of cores of size $\le t$ strictly degrades asymptotic quadratic interpolation room.

3. **Exact Discrete Single-Core Factored-Surface Obstruction (`factored_pivot_no_room`):**
   For any baseline multiplicity $r$, any drop $0 \le K \le r$ on a core $U \subseteq I$ of size
   $|U| \le t$, and **any** cutoffs $s, v \in \mathbb{N}$, completing the square directly in the
   prefix length $l$ yields the exact identity
   $$
   4 d\Bigl((n - t) r(r + 1) + t(r - K)(r - K + 1) - l\bigl(2(r t - d K) - d(l - 1)\bigr)\Bigr)
   = \bigl(2 d l - 2(r t - d K) - d\bigr)^2 + \bigl(4 r^2 (n d - t^2) + 4 r d (n - t) - d^2\bigr)
   + 4 d(t - d) K(K - 1),
   $$
   and a positive-definite quadratic identity on the middle prefix $r - K < l < r$
   (requiring only $2t \le n + d$ and $d^2 \le t(n + 3d - 3t)$). Hence whenever
   $4 r^2 \delta + d^2 \le 4 r d (n - t)$, the `HalfSuccessorJetInterpolation.exists_order_surface`
   rank test fails for every $0 \le K \le r$ and every $s, v$.

   Specializing directly to both second-prime pivots (and simultaneously sharpening the uniform
   $K = 0$ no-room threshold by $\sqrt{2}\times$ at half rate and $2\times$ at quarter rate):

   | Pivot | Error $e$ | Agreement $t$ | $\delta = t^2 - n d$ | Exact sharp no-room radius $R_{\mathrm{sharp}}$ | Crossing at $R_{\mathrm{sharp}} + 1$ |
   |---|---:|---:|---:|---:|---:|
   | Half ($1/2$) | `314,491,699` | `759,250,125` | `1,082,833,961` | **`155,925,516`** | `155,925,517` |
   | Quarter ($1/4$) | `536,870,913` | `536,870,911` | `1` | **`144,115,187,807,420,414`** | `144,115,187,807,420,415` |

4. **Budget-Overflow Corollaries (`quarter_factored_scalar_overflow`,
   `half_factored_two_surface_overflow`):**
   Any constructible ($r \le s + 1$) single-core Kopparty–Sha Appendix A ordinary mixed-Hasse
   surface with $|U| \le t$ already satisfies $s > 2^{31}$ at the quarter pivot, and any two such
   surfaces satisfy $s_1 s_2 > 2^{31}$ (in fact $> 2.4 \times 10^{16}$) at the half pivot.

## Scope & Consequences

- All theorems in `PivotFactoredObstruction.lean` are 100% kernel-checked with zero `sorry` and
  standard axioms only (`{propext, Classical.choice, Quot.sound}`).
- Note the exact boundary condition: the obstruction applies to every core with $|U| \le t$.
  A hypothetical super-threshold head with $|U| = t + \Delta$ ($\Delta > 0$) CAN provide
  positive Kopparty–Sha gain on residual sections, while simultaneously capping its own MCA
  contribution at $n - |U| = e - \Delta$.
- To decide either pivot unconditionally (without assuming a super-threshold head), one must go
  beyond ordinary mixed-Hasse surfaces to **higher-order differential / hidden-derivative
  interpolation** (`CurveHeightCounting` + differential resultant descent + Veronese polar
  counting).
