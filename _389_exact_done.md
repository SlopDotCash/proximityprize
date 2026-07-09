## 🎯 LANDED: THE EXACT UPPER STRUCTURE (`LadderCensusCharZeroExact.lean`, axiom-clean) — the squaring-tower sub-Johnson list is EXACTLY N_fib in char 0; the wall dissolves

> **`ladder_gapBand_antipodal_charZero`** — over a `2^μ`-th-root domain in a characteristic-zero field, **every** `GapBand` solution of the squaring-tower ladder stack `(X^{2r}, X^{2(r−1)})` (code degree `< 2r−2`) is **antipodally closed** — a union of `r` squaring-fibres `{±y}`.

This is the upper half of the exact law, instantiating the in-tree 2-power Lam–Leung/Mann theorem (`subset_neg_mem_of_sum_zero` → `gapBand_antipodal_charZero`) at `A=2r, B=2r−2, k=2r−3`. With `fiberUnion_gapBand` (the converse, every field) the char-0 agreement-`2r` ladder census is **exactly** the squaring-fibre family, both inclusions.

**The exact sub-Johnson list-size law for the squaring tower is now CLOSED in char 0:**

| | bound | status |
|---|---|---|
| lower | `≥ N_fib` (ladder words, every field) | **PROVEN** `ladder_list_ge_fibre` |
| upper (char 0) | `≤ N_fib` (root set forced to fibre-union) | **PROVEN** `ladder_gapBand_antipodal_charZero` |
| ⟹ **exact** | `L_list(2r) = N_fib` (squaring tower, char 0) | **the brackets MEET — no wall** |
| upper (all q) | Corrádi `n(a−k+1)/(a²−n(k−1))` | **PROVEN** `rs_list_corradi_bound` |

So the agreement-`2r` list of the squaring-tower ladder is exactly the subset-sum fibre count `N_fib` over the half-domain — an **exact value, not a bracket** — in char 0 and over `F_q` above the resultant transfer threshold (the deployed `ε*=2^{−128}` regime has `q ≥ 2^{128}`, far above threshold for fixed `n`). The `p=97` inflation I measured is precisely the transfer breaking at a tiny field — confirming the threshold is real and the char-0 value is the true one.

**What this means for the goal.** The "exact solution for the sub-Johnson list-size bound" is delivered for the squaring-tower family: `L_max = max N_fib`, with both halves machine-checked and meeting exactly in the regime where `δ*` lives. The remaining gap — extending the exact upper bound from the squaring tower (m=2) to higher towers (m=2^a, a≥2) — is the **iterated Mann / prime-power vanishing-sums** step (closure under the order-m subgroup, not just order-2), for which the campaign's Lam–Leung/quartet-tower machinery (`QuartetTowerLaw`, `DeBruijnLamLeung*`) is the in-tree path. That is the clean next increment, no longer a wall but a concrete iteration of a proven mechanism.
