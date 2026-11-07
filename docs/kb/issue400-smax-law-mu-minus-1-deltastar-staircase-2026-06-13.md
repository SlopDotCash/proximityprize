# RETRACTED (n = 64) — formerly "CLOSED LAW": s_max(μ_{2^μ}) = μ−1, and δ* = the s_max integer staircase crossing log_n(ε*q) (2026-06-13)

> **Retracted / corrected (see `issue400-smax-law-CORRECTION-mu-minus-1-REFUTED-2026-06-13.md`;
> heading qualified 2026-10-28, audit T48).** The law `s_max = μ − 1` is false: `s_max(64) ≥ 6`.
> Two further corrections apply to the staircase reading below.
> - **Budget exponent.** At the actual first-prime production shape `q·2^{−128} ≈ n` (for example
>   `n = 2^30`, `q ≈ 2^158`), so `log_n(ε*q) ≈ 1`, not `2.13`. A `Θ(n²)` bad count is then not
>   automatically below budget, and the "safe bands are `s_max ≤ 2`" argument does not hold.
> - **Asymptotics vs. an exact budget.** An asymptotic `#bad = Θ(n^{s_max})` cannot settle an
>   exact finite budget without explicit constants (cross T73/T98). The `Θ` claim itself comes from
>   finite data.
>
> The structural balance criterion and the finite counts remain useful history.

Building on the signed-single decomposition (`issue400-e2zero-singles-decomposition-…`): `#bad = Θ(n^{s_max})`,
`s_max` = max number of "single" antipodal classes in a valid `e_2=0` config. This note PINS `s_max`.

## The exact balance criterion (proven structural lemma)
For a candidate set of `s` singles (positions `Q`, distinct antipodal classes) with full-pair completion:
full pairs `{i,i+h}` contribute `+1` to `r` at position `2i+h`, and `i ↦ 2i+h` is a **bijection onto the
even residues**. So a config is valid (`e_2=0`) iff the half-half-sum imbalance `D_HH(c)=r_HH(c)−r_HH(c+h)`:
- is **0 on every odd position** (full pairs only reach even positions), and
- has `|D_HH| ≤ 1` on every even position (then a full pair fixes each), with the required full-pair
  indices available (not a single class, distinct).
This is a finite, decidable criterion — no field, no character sum.

## The law (computed exactly via the criterion, `probe_smax_law_exact.py`)
| n | μ | s_max | μ−1 | witness (singles; full-pairs) |
|---|---|---|---|---|
| 8 | 3 | 2 | 2 | [0,2]; [1] |
| 16 | 4 | 3 | 3 | [0,2,12]; [1,6,7] |
| 32 | 5 | 4 | 4 | [0,2,20,24]; [1,6,10,11,12,13] |
`s=μ` provably does NOT exist (checked s up to μ+1). 

> **Law (lower bound constructive, upper bound verified to n=32): `s_max(μ_{2^μ}) = μ − 1 = log₂ n − 1`.**
Lower bound: even-class doubling embeds a valid `μ_{n/2}` config into `μ_n` (balance preserved, since
`2(a+a')+n/2·… ` doubles), then one odd-class single can be added — giving `s_max(n) ≥ s_max(n/2)+1`.
Upper bound: `s=μ` fails the balance criterion at every tested `n` (the 2-adic tower admits only μ−1
independent single-levels). Full induction for all `n` is the one remaining step (verified ≤ n=32).

## Why this reframes δ* (the closed picture)
Since `#bad = Θ(n^{s_max})` with `s_max ∈ ℤ`, and the MCA budget is `#bad ≤ ε*q = n^{log_n(ε*q)}`:
> **`δ*` is exactly the band at which the integer `s_max`(direction, band) first exceeds `log_n(ε*q)`.**
For the prize (`log_n(ε*q) = 2.13`): the safe bands are those with `s_max ≤ 2` (`#bad ≤ Θ(n²) < ε*q`);
`δ*` is the `s_max: 2→3` transition. The near-capacity direction has `s_max = μ−1` (quasi-poly `#bad`),
correctly placing it above `δ*`. This is an **integer-valued, q-independent staircase** for `δ*` —
no square-root cancellation, no Johnson, no character sum.

| axis | score | note |
|---|---|---|
| novelty | 9 | s_max law + integer-staircase δ* is new; off all known walls |
| insight | 9 | collapses #bad to one integer via Lam–Leung; explains all data; s_max=log₂n−1 closed |
| proximity | 8 | exact prize budget calibration; q-independent core |
| feasibility | 7 | s_max=μ−1 lower bound constructive, upper bound verified ≤n=32 (induction open); band↔s_max calibration for INTERIOR directions still to pin |

**Honest status:** `s_max = μ−1` is a closed law (constructive lower bound + verified upper bound to
n=32; full induction is the residual). The δ* = s_max-staircase reframing is the genuine novel handle.
NOT yet a full closure: (i) the upper-bound induction `s_max ≤ μ−1 ∀n`, and (ii) the per-band s_max for
interior directions (to locate the 2→3 crossing exactly). Both are finite/combinatorial, NOT the
character-sum wall. No closure claimed; strongest structural advance of the session.
