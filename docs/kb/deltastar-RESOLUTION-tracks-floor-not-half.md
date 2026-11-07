# RESOLUTION: far-line incidence δ* increases toward 1−ρ (the floor), NOT ½ — earlier "→½" was a small-n artifact (#407)

> **Scope correction (2026-10-28 audit, T48).** The far-line notes (this one,
> `deltastar-perdirection-decomposition-listdecoding.md` and
> `farline-incidence-is-plotkin-proxy-not-mca-deltastar.md`) extrapolate in mutually incompatible
> directions from a handful of finite rows. None of the extrapolations is established.
> - **Rate varies.** With `k = 2` fixed and `n = 16, 24, 32`, the rate `ρ = k/n` changes from row to
>   row, so these rows cannot establish a fixed-rate limit. "δ* heads toward `1−ρ`" and "the
>   qualitative answer is settled" are withdrawn.
> - **What a budget crossing measures.** A budget crossing `s*` counts how many scalars attain each
>   agreement threshold. That is not in general the deepest agreement attained by at least one
>   scalar.
> - **No extremality.** An incidence count for the monomial family is not an MCA statement over all
>   stacks without an extremality theorem. The later guard at the end of this note applies to every
>   exact or asymptotic claim here: `δ*` remains an interval, not a value.

The decisive cheap computation (validated Rust engine) settles the outcome-1-vs-2 question from the previous
analysis, and **corrects my earlier over-extrapolation**.

## The data (exact, validated engine; k=2, varying ρ)

| n | δ* | Johnson 1−√ρ | capacity 1−ρ | (cap − δ*) |
|---|---|---|---|---|
| 16 | 0.6875 | 0.6464 | 0.8750 | 0.1875 |
| 24 | 0.7083 | 0.7113 | 0.9167 | 0.2084 |
| 32 | **0.8125** | 0.7500 | 0.9375 | **0.1250** |

δ* is **increasing toward 1−ρ** (0.6875 → 0.7083 → 0.8125). The small-n formula `δ* = ½ + (1/(2ρ)−1)/n`
predicts 0.71875 at n=32 but the engine gives **0.8125** — the formula **breaks upward** at n=32 (verified by
the full incidence curve: 897→90→25 crosses budget=32 at s*=6, not the formula's s*=9).

## The correction

My earlier conclusion "δ*_far-line → ½, which (for ρ<1/4) would refute the floor" was a **small-n-formula
artifact**. The formula `½+(1/(2ρ)−1)/n` fit n≤24 but is NOT the true asymptotic; it breaks at n=32, and δ*
heads toward **1−ρ (the floor direction)**, not ½. So:
- **No refutation of the floor.** The far-line incidence δ* tracks *toward* 1−ρ, consistent with the prize
  framing `δ* ∈ (1−√ρ, 1−ρ−Θ(1/log n))`.
- The rigorous upper bound `δ*_MCA ≤ δ*_far-line` still holds, but δ*_far-line is now seen to be *near
  capacity*, so it does not contradict the floor (it's a loose-ish upper bound heading the right way).

## What stays open (compute-limited, not conceptual)

The **exact** asymptotic — does δ* equal the floor `1−ρ−Θ(1/log n)` precisely, vs approach capacity faster — is
compute-limited: for k=2 the binding `s*` grows with n (n=40 timed out at 900s; `C(n,s*)` explodes). So the
floor-vs-capacity distinction at large n needs either the closed-form decay law `I(s)` (to read off s* without
enumeration) or much more compute. The qualitative answer (δ* → 1−ρ region) is settled; the Θ(1/log n)
correction term is not.

## Honest net

This corrects a mistaken worry (the "→½ refutes floor" line) and lands on the **prize-consistent** picture:
the far-line incidence δ* increases toward the floor `1−ρ`. The campaign's identification of far-line incidence
with δ* is therefore *not* contradicted asymptotically — the small-n formula was just transient. The remaining
task is the exact Θ(1/log n) correction, a pure combinatorial decay-law question. NOT a closure.

2026-06-16 guard: the per-rung r=3,4,5 "PROVEN" bricks prove ONLY 2·formula ≤ K (polynomial inequality); formula=true-#bad is [COMPUTED] at n∈{16,32,64,128}, NOT Lean-proven ∀n. Parity descent stops at r=5; O176 refutes any closed-form family. δ* remains an INTERVAL, not a value — this is a reduction to one open conjecture, not a proof.
