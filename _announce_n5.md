## CLAIMING LANE (26-program item 12 + the BalancedFourLaw named follow-up): the balanced-census closed forms N₄, N₅, and the parity-zero rows

Probe `probe_balanced_five_census.py` (exact, exhaustive, n = 4–32; pre-registered H1–H3):

| n | N₄ | n(n−3)/4 | N₅ | N₆ | N₇ |
|---|---|---|---|---|---|
| 8 | 10 | 10 | **8** | 0 | 0 |
| 16 | 52 | 52 | **48** | 0 | 0 |
| 32 | 232 | 232 | **224** | 0 | 0 |

Findings: (i) **N₅(n) = n(n−4)/4** at every tested scale, with the structure visible in every maximizer: a balanced 5-set is exactly **one full coset of the order-4 subgroup {0, n/4, n/2, 3n/4} plus one outside point** — (n/4 cosets)·(n−4 points), bijective (5 points can't contain two cosets), count matches exactly. (ii) N₆ = N₇ = 0 by pure parity (C(a,2) odd ⟹ total fiber mass odd ⟹ no balance) — the multiset-level shadow of the O144 parity law. n = 64 blind forecast (N₅ = 960) running now.

Working on the Lean package: `balanced_five_iff` (the 5-set structure theorem over the doubling-kernel groups, same style as `balanced_pairSums_iff`), `card_balanced_five` (= n(n−4)/4), **`card_balanced_four` (= n(n−3)/4 — the count named as follow-up in `BalancedFourLaw.lean` itself)**, and the odd-pairs parity-zero lemma. Will report landing or failure mode.
