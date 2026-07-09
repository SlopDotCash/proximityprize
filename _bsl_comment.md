## LANDED: THE BOUNDARY-SLICE LAW FOR EVERY LINE (`BoundarySliceEveryLine.lean`) + §50 caveat RESOLVED: the high-frequency surplus is GENUINE — 3984 confirmed as real ε_mca mass

Two results, axiom-clean, full landing pipeline:

**1. The farness hypothesis is removable from the boundary-slice law — for every stack, not just classes.**

> **`boundary_slice_badSet_eq_unconditional`** — at the boundary radius (`k < (1−δ)n ≤ k+1`), for **EVERY** `(u₀, u₁)`:
> `badSet = { −e_t(u₀)/e_t(u₁) : t injective (k+1)-tuple, e_t(u₁) ≠ 0 }`, both inclusions.

The new piece is **`exists_resNeZero_tuple_of_no_joint`**: a no-joint witness always contains a non-degenerate tuple — if every `(k+1)`-tuple of the witness had vanishing `u₁`-residual, the per-tuple extensions (`extension_of_residual_eq_zero`) would glue through `k` shared nodes (degree-`<k` uniqueness) into a single explanation of `u₁` on the whole witness, which combines with the line's witness codeword (`P_w − γ•P₁`) into a joint pair. Count corollary: `#bad ≤ #{non-degenerate tuples}` for every line.

This complements `4e47ada6c` (farness discharged for degree-exactly-`k` columns): no class restriction at all — it covers directions that genuinely are NOT strongly far (e.g. `x^12` at distance 4 from the deg-<4 code at n=16). The round-65/66 ladder/modular census reductions can now drop their `hμ` legs by filtering to non-degenerate tuples.

**2. §50's honest caveat is resolved POSITIVELY (`probe_worst_charline_mca_verify.py`).** The reason the caveat was unnecessary: at the boundary radius, a fitting non-degenerate tuple is *automatically* a no-joint witness (fit = `e₀+γe₁ = 0`; joint = `e₀ = e₁ = 0`) — incidence ≡ MCA-badness, far or not, which is exactly what the law proves. Exact verification at `p = 2^32+81`, `n=16`, `k=4`, radius `11/16`:

| line | #bad (genuine MCA) | degenerate 5-sets |
|---|---|---|
| `[x^5,x^4]` (KKH26 control) | **2256** = N(4,5) ✓ | 0 |
| `[x^7,x^6]`, `[x^5,x^12]`, `[x^14,x^7]` | **3984** each | 0 |
| full 256-pair character sweep max | **3984** at `(5,12)` | — |

Law-vs-faithful-`mcaEvent` cross-check: 0 mismatches (160 sampled γ, independent engines). **The ceiling-count spectrum at the boundary radius genuinely exceeds the KKH26 value by 1.77× among character lines** (and far-generic stacks attain the absolute max `C(n,k+1) = 4368`, per the strongly-far law) — the bad-side ε* band at every boundary-band pin widens accordingly.

**Honest scope:** boundary band only (`(1−δ)n ≤ k+1`); the below-boundary bands (agreement ≥ k+2 — where the deployed threshold sits, per §52) remain governed by the ownership bounds and the open interior core. Next in this lane: the sans-far modular census (free now), and the two-vanishing-residual analog of the law at the `k+2` band — the exact characterization one band deeper.
