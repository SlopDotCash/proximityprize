# Quarter-rate witnesses with fewer locator modes

On each named field at length $n=2^{30}$ and rate $1/4$, one scalar received word has a closed list exceeding the designated budget at the error count below. Repeating the scalar row gives the same witness at any positive interleaving width. These are upper bounds on first failure. [Earlier four-fiber construction](rotated-locator-union.md) · [Certificate verifier](../../../scripts/probes/probe_quarter_reweighted_locators.py)

| Field | Errors | Distinct words at least | Budget | Earlier ceiling |
|---|---:|---:|---:|---:|
| First prime | **771,728,657** | 1,073,978,526 | 1,073,741,824 | 771,728,668 |
| Second prime | **771,741,384** | 2,147,640,054 | 2,147,483,648 | 771,741,388 |

Use the four reserved fibers of the order-64 quotient, with $h=n/64$. For every selected ordinary 17-subset $T$, its fixed root product determines the same constant $c=L_T(0)$ of the monic locator $L_T$. Each signed mode at a reserved fiber specifies one value of that locator. For a selection $S$ of modes, let $w_i$ be a mode's number of subsets, and let $w_{ij}$ be the intersection of two modes at different anchors. Then
\[
\left|\bigcup_{i\in S} C_i\right|\ \ge\
\sum_{i\in S}w_i-\sum_{\{i,j\}\subset S}w_{ij}.
\]
The selection in the verifier exchanges some modes near the single-count cutoff for modes with fewer repeated subsets. The fixed rank masks specify every retained mode. Verifying the bound requires only the earlier signed single and pair recurrences. The search used the change in the displayed lower bound under a swap.

| Product exponent | Modes | Single incidences | Pair repeats | Sites per mode |
|---:|---:|---:|---:|---:|
| 12 | 2,162 | 1,088,872,068 | 14,893,542 | 23,280 |
| 15 | 4,769 | 2,166,222,587 | 18,582,533 | 10,553 |

For each palette of $K$ modes allocate $g=\lfloor(3h+1)/K\rfloor$ disjoint sites per mode at the corresponding anchor. The per-fiber counts fit into $h$ sites, and the remaining reserved sites contain $h-1$ distinct common roots. Let $H$ vanish there. The polynomial $H(X)(Y^{17}+c-L_T(Y))/Y$ with $Y=X^h$ has degree at most $16h-1$. Its center is $H(x)(y^{17}+c-v)/y$ with the assigned locator value $v$ at a selected site and $v=0$ elsewhere. The $17h$ ordinary sites of $T$, the $h-1$ common roots and the $g$ assigned sites are disjoint agreement sets. Distinct locators yield distinct codewords, so the single-minus-pair counts give the claimed closed lists. [Polynomial and signed-mode proof](rotated-locator-union.md#one-center-for-the-selected-sets)

The finite certificate uses Python 3 and a C++20 compiler.

```sh
python3 scripts/probes/probe_quarter_reweighted_locators.py
```
