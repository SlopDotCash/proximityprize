## THE ALIGNMENT-CENSUS TWO-REGIME LAW (probe, exact, field-independent): at depth, the supply is EXHAUSTED by the KKH26 structure — the open core in its sharpest empirical form

With the universal alignment law landed, the deployed question is the **alignable-set census per band**. First exact measurements (`probe_alignment_census.py`, divided-difference engine, p ∈ {12289, 65537}):

**The m=1 shape (n=16, k=4 — ceiling = boundary):** the supply is a **step function**. Every line has the full `C(16,5) = 4368` alignable sets at the boundary band; at `a = 6` the supply is **exactly 0** for every tested line (two small-field accidents at p=12289 vanish at p=65537). This *explains* the `δ* = 11/16` shape: the entire bad mass lives in the boundary band.

**The m=2 shape (n=16, k=3, μ=3, m=2, r=3 — genuinely deep ceiling), the headline:**

| line | a=4 (boundary) | a=5 | a=6 (ceiling band) | a=7 |
|---|---|---|---|---|
| **KKH26 `[x^6,x^4]`** | 1792 / 496 | 336 / **40** | **56 / 40** | **0 / 0** |
| shifted `[x^7,x^5]` | 1800 / 808 | 0 | 0 | 0 |
| hi-freq `[x^7,x^6]` | 1792 / 1488 | 0 | 0 | 0 |
| `[x^9,x^7]` (exotic) | 1820 / 737 | 112 / 1 | 56 / 1 | 16 / 1 |
| far-generic ×3 | 1820 / ~1800 | 0 | 0 | 0 |

(align/#bad; structured-line numbers **identical at both primes**.)

- The KKH26 line's 56 alignable 6-sets are **exactly the `C(8,3)` squaring-fibre unions** of the construction, pinning 40 scalars (the 3-subset-sum collision census of μ₈), and the supply stops **exactly at the ceiling**: 0 at `a = 7` ⟹ δ* = 1 − 6/16 = **5/8 = 1 − r/2^μ**, the conjectured value, read straight off the census.
- **Every other tested line has ZERO deep supply.** The boundary-band order (far-generic max ≈ C(n,k+1), KKH26 near-minimal) **reverses completely at depth**: arithmetic structure is the only thing that survives below the boundary. (The one exotic `[x^9,x^7]` family keeps alignable sets to a=8 but pins a single scalar — a multiplicative-translate artifact, mass 1.)

**Reading for the open core.** `InteriorCeiling` at the deep ceiling is now, empirically and in the proven census normal form: *the deep alignable supply of every line is contained in (a bounded multiple of) the KKH26-structured family*. At this scale that statement is TRUE with margin 0-vs-40. Two Lean-able follow-ups left for whoever wants them (or my next iteration): (i) aligned-set monotonicity (subsets of aligned sets are aligned — trivial, useful); (ii) the bad-side supply in census form: the fibre-unions of `badline_pointwise_agreement` are alignable sets of `[x^{rm}, x^{(r−1)m}]` — connecting the landed KKH26 construction to `UniversalAlignmentLaw` and making the census lower bound exact at every deep ceiling.

**Honest scope:** 7 lines × 2 primes × 1 small scale; a census statement over all lines is exactly the wall, not claimed here. But the experiment cleanly separates the two regimes and confirms the conjectured pin value is what the deep census computes.
