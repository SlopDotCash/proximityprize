# Odd-Cardinality $K$-Fiber Folded-Norm Ramification & Odd-Degree Split-Pencil Obstructions

## Overview

This note accompanies [`SplitPencilOddFiberObstructions.lean`](../../../ArkLib/Research/ProximityGap/Frontier/SplitPencilOddFiberObstructions.lean) and [`probe_split_pencil_odd_fiber_obstructions.py`](../../../scripts/probes/probe_split_pencil_odd_fiber_obstructions.py), sharpening the ramification, deck-symmetry, inner-degree, and orbifold-excess obstructions across **all** surviving odd-degree split-pencil stages:

1. **Quarter-rate successor (`447,392,428` on $p_1$, `536,870,913` on $p_2$, $D = 2^{28} - 2$):**
   - **Case 1 ($s = 2, h = 1$):** $R = V \circ W$ where $W$ has **6 disjoint complete fibers** of odd degree $m = 134{,}217{,}727$ in $\mu_{2^{30}}$.
   - **Case 2a ($s = 1, h = 2, T(x) = x^2$):** $R(x) = U(x^2)$ where $U$ has **3 disjoint complete fibers** of odd degree $m = 134{,}217{,}727$ in $\mu_{2^{29}}$.
2. **Odd-degree split pencil ($D_{\mathrm{odd}} = 2^{28} - 1 = 268{,}435{,}455 = 3 \cdot 5 \cdot 29 \cdot 43 \cdot 113 \cdot 127$):** governing `HasPuncturedList` at $p_1$ half-rate `268,435,457` and the $p_2$ quarter-rate pivot `536,870,913`, plus Pattern-3's simultaneous degree-$2^{28}$ pencil.

## 1. Universal $K$-Fiber Folded-Norm Energy & 1-Level Odd-Cardinality Exclusion

For $K \ge 2$ disjoint fibers $F_0, \dots, F_{K-1} \subset \mu_{2^{k+1}}$ of odd size $m$ (total mass $M = K m$), define the antipodal imbalance $\operatorname{imb}_i(j) = \mathbf{1}_{x_j \in F_i} - \mathbf{1}_{y_j \in F_i}$ on matched antipodal pairs $(x_j, y_j)$ ($j \in \operatorname{Fin}(2^k)$). Summing the squared pairwise energy $(\operatorname{imb}_i - \operatorname{imb}_l)^2$ over all $K^2$ ordered pairs satisfies the exact algebraic identity (`pointwise_k_fiber_energy`):
$$\sum_{i, l \in \operatorname{Fin} K} (\operatorname{imb}_i - \operatorname{imb}_l)^2 = 2 K \sum_i \operatorname{imb}_i^2 - 2\Big(\sum_i \operatorname{imb}_i\Big)^2 \le 2 K \cdot (\operatorname{occ}(x) + \operatorname{occ}(y)).$$
Averaging over the $K(K - 1)$ off-diagonal pairs yields a distinct pair $(i, l)$ with folded energy (`small_pair_k_fibers`):
$$E_{i, l} \le \left\lfloor \frac{2 K m}{K - 1} \right\rfloor.$$
Whenever $E_{i, l}^{2^k} < p^{2 |S|}$ at a set $S$ of odd-order test nodes where modular moments agree, `DyadicFoldedNorm.zero_of_moments` forces $\operatorname{imb}_i \equiv \operatorname{imb}_l$, hence $\mathbf{1}_{x_j \in F_i} = \mathbf{1}_{y_j \in F_i}$ for every $j$. That forces $|F_i| = 2 \sum_j \mathbf{1}_{x_j \in F_i}$ to be **even**, contradicting odd $m$ at a **single dyadic level** (`no_odd_k_fiber_moments`).

### Exact Production Ramification Ceilings (Axiom-Clean Lean)

Certified by `production_odd_fiber_thresholds_p1` ($p \ge 2^{158}$) and `production_odd_fiber_thresholds_p2` ($p \ge 2^{159}$):

| Surviving stage | $K$ | Odd $m$ | Energy ceiling $E_{\min}$ | $p_1$ odd tests $S$ ($e_0 + e_\infty \le 2S$) | $p_2$ odd tests $S$ ($e_0 + e_\infty \le 2S$) |
| :--- | :---: | :---: | :---: | :---: | :---: |
| Quarter Case 1 ($s = 2$) | $6$ | `134,217,727` | `322,122,544` | `48,017,725` ($\le 96{,}035{,}450$) | `47,715,727` ($\le 95{,}431{,}454$) |
| Quarter Case 2a ($T = x^2$, $\mu_{2^{29}}$) | $3$ | `134,217,727` | `402,653,181` | `24,282,334` ($\le 48{,}564{,}668$) | `24,129,615` ($\le 48{,}259{,}230$) |
| Odd-$D$ full ($s = 1$) | $3$ | `268,435,455` | `805,306,365` | `50,263,626` ($\le 100{,}527{,}252$) | `49,947,503` ($\le 99{,}895{,}006$) |
| Odd-$D$ ($s = 3$) | $9$ | `89,478,485` | `201,326,591` | `46,865,709` ($\le 93{,}731{,}418$) | `46,570,956` ($\le 93{,}141{,}912$) |
| Odd-$D$ ($s = 5$) | $15$ | `53,687,091` | `115,043,766` | `45,494,047` ($\le 90{,}988{,}094$) | `45,207,921` ($\le 90{,}415{,}842$) |

## 2. Complete Zero-Symmetry & Wronskian Classification for $D_{\mathrm{odd}} = 2^{28} - 1$

For any odd-degree $D_{\mathrm{odd}} = 268{,}435{,}455$ split pencil on $\mu_{2^{30}}$ over prime characteristic $p > 2^{40}$ (formalized unconditionally in Part 2 of `SplitPencilOddFiberObstructions.lean`):

1. **Zero nontrivial source symmetries (`odd_split_no_nontrivial_source_symmetry`, `h = 1`):**
   - Rotations $x \mapsto u x$ satisfy $u^{\gcd(2^{30}, 268435455)} = u^1 = 1$, forcing $u = 1$.
   - Reciprocals $x \mapsto u / x$ cannot stabilize three disjoint odd-size subsets of $\mu_{2^{30}}$, since each odd subset would contain a fixed point solving $x^2 = u$ (at most 2 roots in a field).
   - Non-monomial Möbius maps are excluded by `MobiusSubgroupBound.production_graph`.
2. **Suborbit floor & permutation rank (`odd_split_suborbit_floor_and_rank`):**
   Applying the large-characteristic `(1, 1), M = 3` Wronskian (`QuarterSplitWronskianSuborbits.lean`, $2 n D_{\mathrm{odd}} < 2^{59} \ll p_1 < p_2$) yields $a \ge 44{,}739{,}242$, at most `6` nontrivial suborbits, and permutation rank $\le 7$.
3. **Elimination of 60 of 62 proper divisors (`odd_split_inner_degree_classification`):**
   Of the 62 nontrivial proper divisors of $268{,}435{,}455 = 3 \cdot 5 \cdot 29 \cdot 43 \cdot 113 \cdot 127$, all 60 divisors $\le 17{,}895{,}697$ are eliminated, leaving only:
   - **`s = 5, m = 53,687,091`**: $E(W) \ge \frac{107{,}374{,}174}{10{,}737{,}421} > 9.9999966$ ($\implies$ **at least 12 branch points**), $E(R) > 1.9999993$.
   - **`s = 3, m = 89,478,485`**: $E(W) \ge \frac{536{,}870{,}870}{268{,}435{,}469} > 1.9999997$ ($\implies$ **at least 4 branch points**, and if $r = 4$ all four orders $\ge 3{,}947{,}581$), $E(R) > 0.6666665$.
   - **`s = 1, m = 268,435,455` (primitive)**: $E(R) \ge \frac{536{,}870{,}870}{1{,}342{,}177{,}289} > 0.399999967$.
4. **Excluded whole-pencil signatures (`odd_split_excluded_signatures`):**
   Unconditional $E(R) \ge \frac{536{,}870{,}870}{1{,}342{,}177{,}289}$ excludes every `(2, 3..9, c)`, every `(3, 3, c)`, `(2, 10, c ≤ 29,433,712)`, `(3, 4, c ≤ 59)`, `(3, 5, c ≤ 14)`, `(4, 4, c ≤ 9)`, and `(2, 2, 2, c ≤ 9)`.
5. **Pattern-3 simultaneous degree-$2^{28}$ pencil (`pattern3_deg_2_28_classification`):**
   Eliminates all 25 proper dyadic inner degrees $2^r \le 2^{25}$, leaving only $2^{26}, 2^{27}, 2^{28}$.

## Honesty Boundary

- **100% axiom-clean Lean (`SplitPencilOddFiberObstructions.lean`):** All 16 theorems (the universal $K$-fiber energy identity, 1-level odd-cardinality exclusion, all 10 exact production power comparisons on $p_1$ and $p_2$, zero Möbius deck symmetry for $D_{\mathrm{odd}}$, suborbit floor, 60/62 proper-divisor elimination, orbifold excess floors, signature exclusions, and Pattern-3 dyadic inner-degree classification) compile with 0 `sorry`, 0 warnings, and `#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.
- **Written bridge:** Connecting the rational map $R$ / $W$ to the fiber-product curve inequality `wronskian` and weighted variance bound `genus` uses the same large-characteristic Wronskian GCD theorem (`QuarterSplitWronskianSuborbits.lean`) and Riemann–Hurwitz curve setup as [`quarter-split-wronskian-suborbits.md`](quarter-split-wronskian-suborbits.md).
