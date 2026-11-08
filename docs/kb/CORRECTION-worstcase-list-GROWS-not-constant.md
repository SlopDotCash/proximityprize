# CORRECTION: the worst-case window list GROWS (~n²), it is NOT the constant dilation orbit (#444)

> **Scope note (2026-10-28 audit, T48).** The retraction of the global constant-list claim stands.
> The replacement wording needs the same care. The scan covers monomial and 2-term lacunary words
> only, so its maxima are **sampled lower bounds** on the worst case over all received words. They
> are not the worst case itself. Read "worst-case" below as "worst among the scanned words".
> Likewise "`~n²`" and "GROWS" summarize five finite rows. Neither a universal upper bound nor any
> asymptotic growth rate follows from them.

Honest retraction of the "explicit-smooth-RS list = constant 2 (dilation orbit)" claim (comment 4705186359,
`listdecoding-dilation-orbit-law-CONFIRMED.md`). A BROAD worst-case scan (all monomial + all 2-term lacunary
words, `scripts/rust-pg/src/bin/listscan.rs`) shows the worst-case list is NOT constant.

## The corrected measurement (broad scan, window MIDPOINT t = ½(ρ+√ρ)n, genuinely past Johnson)

| n (ρ=1/4) | worst-case window list | worst word |
|---|---|---|
| 16 | 7 | x^15+x^5 |
| 20 | 22 | x^18+x^6 |
| 24 | 34 | x^22+x^7 |
| 16 (ρ=1/8) | 4 | x^13+x^12 |
| 24 (ρ=1/8) | 21 | x^22+x^4 |

The worst-case list **GROWS** (7→22→34 at ρ=1/4), `~n²`-ish (L/n² ≈ 0.027, 0.055, 0.059). The worst word is a
**non-dilation-invariant lacunary word** (`x^a+x^b`), NOT `x^{n/2}`.

## Why the earlier "constant=2" was wrong

The dilation-orbit law (list = orbit = O(1)) applies ONLY to **dilation-invariant words** like `x^{n/2}` (whose
list is exactly the stabilizer orbit, =2). But the **worst case over all words is a non-invariant lacunary word**,
whose list is larger and grows. My earlier confirmation (and the army's orbit-list-law) measured `x^{n/2}` and a
narrow far-line pencil, missing the larger non-invariant lists. So:
- "worst-case list = dilation orbit = O(1)": **RETRACTED** — true only for invariant words.
- The true worst-case window list **grows** (~n² at feasible n).

## What this means for the floor

- **If the growth is poly (~n²):** the floor HOLDS (poly lists past Johnson) — just with a larger list than the
  orbit. The L/n² ≈ const trend (0.055, 0.059 at n=20,24) is consistent with poly.
- **If superpoly:** the floor FAILS.
- **UNDECIDED at feasible n** — the same scale-confounding (poly vs superpoly indistinguishable at n≤24). The
  `~n²` trend WEAKLY favors poly (floor), but is not conclusive. This is the BGK wall again, now as the worst-case
  list-size growth rate.

## Net (honest)

The worst-case explicit-smooth-RS list in the window is NOT a constant — it GROWS (`~n²` at n≤24). The dilation
orbit is only the invariant-word list. Whether the worst-case growth is poly (floor) or superpoly (no floor) is
undecided at feasible n = the open core. My "constant=2 ⟹ floor" overclaim is corrected: the data is consistent
with the floor (poly ~n²) but does not establish it. Tool: `scripts/rust-pg/src/bin/listscan.rs` (broad scan).
