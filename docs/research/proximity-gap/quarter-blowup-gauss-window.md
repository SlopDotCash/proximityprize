# Nef-Safe Blown-Up Gauss-Graph Excess Intersection and Quarter-Rate Safety Through 534,295,000 Errors

This note advances the second-prime quarter-rate MCA safety lower bound from `533,150,000`
(`quarter-common-factor-degrees.md`) to **`534,295,000` errors** (first failure $\ge 534{,}295{,}001$,
a gain of **`+1,145,000` errors**, cutting nearly one-third of the remaining `3,720,912`-error gap
to the quarter-rate Johnson pivot `536,870,913`) using only two ordinary mixed-Hasse surfaces on any
injective domain of length $n = 2^{30}$ over any field of characteristic $> 2^{100}$ (in particular,
$p_2 = 2^{30}(2^{129} + 13) + 1$).

The geometric engine is identical to `half-blowup-gauss-window.md` (Section 1):

1. **Nef-safe blown-up Gauss-graph excess intersection** on
   $\hat{X} = \operatorname{Bl}_{\bigcup C_x}\operatorname{Bl}_\Sigma \mathbf{P}_{\mathbf{P}^1_X}(\mathcal{O} \oplus \mathcal{O} \oplus \mathcal{O}(-d))$,
   splitting on the companion cofactor $Q_2 / \prod_{a=1}^j (Y - h_a) = F^{k_2} G_2$ into Case 1
   (`coprime_companion_fallback`) and Case 2 (`factor_order_sum_ge` + `nef_weight_cauchy_schwarz` +
   `volume_excess_cancel` + `blowupH_mono`), yielding per-unit-$m$ pole-degree height bound
   $$
   \operatorname{maxBlowupH}(j, b)
   = \operatorname{blowupH}\!\bigl(b,\, \min(53 t - 1 - j d,\, b t - 1),\, t,\, d\bigr).
   $$
2. **Dual-constraint $(\alpha, \beta)$ Veronese allocation** for $j \in \{0, 1, 2, 3\}$ using the four
   Veronese levels $(s, a) \in \{(4, 3), (8, 6), (16, 11), (24, 17)\}$ (with $p = \min(j, 3)$ fixed
   rich heads, which are automatically independent in every Veronese degree $s \ge 4$), and pure
   transverse/triangle tangent bounds ($\beta(j) = 0$) for all $j \ge 4$.

## Verification Scope

- **Lean-checked (`ArkLib/Research/ProximityGap/Frontier/QuarterBlowupGaussWindow.lean`)**:
  zero `sorry`, zero custom axioms (`#print axioms` $\subseteq$ `{propext, Classical.choice, Quot.sound}`):
  - `factor_order_sum_ge` and `blowupH_mono` (with `volume_excess_cancel`, `nef_weight_cauchy_schwarz`,
    `blowupH_ge_rat`, and `coprime_companion_fallback` proved in `HalfBlowupGaussWindow.lean` for
    general parameters $b, W, t_0, d_0, m$).
  - `ranks` and `surfaces`: exact rank surpluses (`374,155,779` and `24,285,466,484`) and existence
    of both mixed-Hasse surfaces `(53, 106, 71987)` and `(103, 206, 7378)` at $e = 534{,}295{,}000$
    on any injective length-$2^{30}$ domain.
  - `parameters`, `dual_prices`, and `allocation`: exact verification of all denominators,
    tame-characteristic guards, Veronese gaps with $p = \min(j, 3)$ fixed rich heads, Case-1
    companion-cofactor fallback floors, dual-constraint $(\alpha, \beta)$ prices for all
    $j \in \{0, \dots, 106\}$ and $2 \le b \le 106 - j$, and the total bad-scalar cap
    **`2,146,832,205 < 2^31`** (slack **`651,443`**).
- **Written mathematical steps**:
  - The nef-safe blow-up intersection theorem and Case 1 / Case 2 split on $Q_2 = F^{k_2} G_2$ are
    proved in full in `half-blowup-gauss-window.md` (Section 1); projective plane-curve duality,
    Veronese determinants with $p \le 3$ independent fixed heads, and transverse tangent windows
    follow `quarter-common-factor-degrees.md`, `quarter-transverse-tangents.md`, and
    `tangent-polar-windows.md`.
- **Independent Python verification (`scripts/probes/probe_quarter_blowup_gauss_window.py`)**:
  reproduces the exact integer surpluses, resultant and linear caps, and all `44,314` $(j, b, m)$
  pricing checks (max `2,146,832,205` at $j = 3$, slack `651,443`).

---

## 1. Production Parameters at `e = 534,295,000`

At $n = 2^{30} = 1{,}073{,}741{,}824$, $d = 2^{28} - 1 = 268{,}435{,}455$, $e = 534{,}295{,}000$,
$t = n - e = 539{,}446{,}824$, $\mathrm{miss} = 8192$, $\mathrm{core} = t - \mathrm{miss} = 539{,}438{,}632$:

| Surface | Order $r$ | Ordinate deg $b$ | Total deg $s$ | Columns | Constraints | Rank Surplus |
|---|---:|---:|---:|---:|---:|---:|
| Primary $P_1$ | `53` | `106` | `71,987` | `110,938,493,654,193,152` | `110,938,493,280,037,373` | **`374,155,779`** |
| Companion $Q_2$ | `103` | `206` | `7,378` | `42,000,137,932,960,768` | `42,000,137,908,675,284` | **`24,285,466,484`** |

Non-nonlinear fixed overhead (`otherLabels(j)`):
- Scalar-only primary factors: $\le 71{,}987$.
- Single resultant (noncommon sections): $\le 71{,}987 \cdot 206 + 106 \cdot 7{,}378 = 15{,}611{,}390$.
- Small polynomial affine heads: $\le (106 - j) \cdot 71{,}987$.
- Common nonaffine linear factors: $\le (7{,}378 - j) \cdot 17$ (since $4n \le 16(t - d)$).
- Rich polynomial affine heads: `headMass(j)` using $\max(\mathrm{discreteUnion}(j), \lceil j \cdot \mathrm{core}^2 / (\mathrm{core} + (j - 1)d) \rceil)$
  with $a \in \{\lfloor j/2 \rfloor, \lfloor (j+1)/2 \rfloor\}$.

---

## 2. Veronese Ladder and Dual Pricing

For $j \in \{0, 1, 2, 3\}$, we use four Veronese determinant levels $(s, a, h, C_a, E_s)$ with
$p = \min(j, 3)$ independent fixed rich heads:

| Veronese $(s, a)$ | $h = \binom{s+2}{2}$ | $C_a = \binom{a+2}{3}$ | $E_s = \frac{s(s+1)(s+2)}{3}$ | Reflexivity guard $m > s(s-1)$ |
|---|---:|---:|---:|---:|
| `(4, 3)` | `15` | `10` | `40` | `m > 12` |
| `(8, 6)` | `45` | `56` | `240` | `m > 56` |
| `(16, 11)` | `153` | `286` | `1,632` | `m > 240` |
| `(24, 17)` | `325` | `969` | `5,200` | `m > 552` |

Because $3$ distinct points in $\mathbf{P}^2$ impose $3$ independent linear conditions on every
Veronese system of degree $s \ge 4$ (even if collinear, since any line meets a quartic in at most
$4 > 3$ points), fixing $p = \min(j, 3)$ rich heads subtracts $p$ rows from the $h \times h$ Veronese
determinant and adds $a p \cdot \mathrm{miss}$ to the denominator penalty, leaving
$$
\operatorname{gap} = a h t - (C_a n + E_s d + a p \cdot \mathrm{miss}) > 0,
\qquad
\operatorname{veronesePrice} = 4b - 2 + 2sb + \left\lceil \frac{(h - p)(a R + s H)}{\operatorname{gap}} \right\rceil.
$$

For $j \ge 4$, $\beta(j) = 0$ and the transverse tangent window (`t + discreteUnion(j) - (n + d)`)
already keeps $\operatorname{basePrice}(j, b) \le \alpha(j)$ for every $2 \le b \le 106 - j$.

Summing over all common nonlinear factors $(b_i, m_i)$ with $\sum m_i \le 7{,}378 - j$ and
$\sum b_i \le 106 - j$ proves (`QuarterBlowupGaussWindow.allocation`):
$$
\text{total bad scalars} \le \mathbf{2{,}146{,}832{,}205} < 2^{31} = 2{,}147{,}483{,}648
$$
with maximum attained at $j = 3$ and **`651,443`** bad scalars to spare.

### Selected $j$-Profile

| $j$ | Regime | `otherLabels(j)` | $\alpha(j)$ | $\beta(j)$ | Total Cap | Slack below $2^{31}$ |
|---:|---|---:|---:|---:|---:|---:|
| `0` | Blow-up + Veronese `(4,8,16,24)` dual | `23,439,425` | `76,050` | `23,143` | `586,989,483` | `1,560,494,165` |
| `1` | Blow-up + 1-head Veronese dual | `557,662,421` | `74,511` | `19,134` | `1,109,319,128` | `1,038,164,520` |
| `2` | Blow-up + 2-head Veronese dual | `1,091,885,417` | `72,990` | `15,213` | `1,631,858,009` | `515,625,639` |
| `3` | Blow-up + 3-head Veronese dual (**peak**) | `1,618,679,138` | `71,489` | `11,369` | **`2,146,832,205`** | **`651,443`** |
| `4` | Blow-up + transverse | `1,610,601,455` | `72,718` | `0` | `2,146,823,987` | `659,661` |
| `5` | Blow-up + transverse | `1,610,664,884` | `72,719` | `0` | `2,146,822,671` | `660,977` |
