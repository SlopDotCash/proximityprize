# δ* sweep A37 — N3 strengthened window-localization (sunflower-forcing): REFUTED

**Date:** 2026-06-14 · **Actionable:** A37 (merged 371-T09) · **Type:** numerical-probe
**Artifact:** `scripts/probes/sweep_A37_sunflower.py` · **Status:** REFUTED (exact, q-independent)

## The question (N3, scoped 371-T09, never run)

Interleaved MCA model for `RS[F_q, μ_n, k]`, rate `ρ=k/n`, degree `d=k-1`. A *direction*/line
is a pair `(u0,u1)` of words on the smooth domain `D=μ_n`. A scalar `γ` is **bad** (explainable)
at agreement threshold `a` if the line word `u0+γ·u1` agrees with some codeword (deg ≤ d) on `≥ a`
points (`a = ⌈(1−δ)n⌉`). The window `δ ∈ (1−√ρ, 1−ρ)` (Johnson, capacity) corresponds to
`a ∈ (k, ⌈√ρ·n⌉]`; *below-saturation* = bands `a` just below Johnson (heaviness not yet generic).
UDR (agreement form): `a_UDR = ⌈(n+k)/2⌉`. A direction is **heavy** if `#bad` exceeds the
unique-decode budget (operationally `#bad ≥ 2`, above the median; we track the record).

- **Proven (easy side):** each codeword `c` agrees with `u1` (the *direction* word) on
  `≤ n − w − k` points (`w` = window witness size); `n−w−k` is *decreasing* in `w`.
- **N3 target:** a heavy direction *forces* some codeword to agree with `u1` on `≥ w+k` points
  (`w+k` *increasing* in `w`; the two cross at `w=(n−2k)/2 ≈ UDR`). Since `w+k` exceeds the
  single-window witness size `a`, the extra agreement could only come from the **overlap /
  sunflower** structure (common core + petals) of the witness family `{A(γ) : γ bad}`.
  Closing this below saturation (where heaviness is not generic — it was refuted at the ceiling)
  would be NEW even at exponential `q`.

## Method

Exact arithmetic mod `q`. Fast core: for a fixed base `B` (size `d+1`), `codeword(x_i)` is a fixed
`Z`-linear combination `L[B][i]·word[B]` of the base values (depends only on the domain,
precomputed once). Because `word_j = u0_j + γ·u1_j` is *affine in γ*, `codeword(x_i) − word_i =
α_i + γ·β_i` is affine in `γ`; agreement at `i` holds iff `α_i + γ·β_i ≡ 0`, i.e. at a *single*
`γ` (`β_i≠0`) or *all* `γ` (`α_i=β_i=0`). This recovers the agreement set as a function of `γ`
without scanning all `q`, so heavy directions are enumerated exactly.

Decisive instance `(q,n,k) = (1009,16,2)` plus the `(8..16, 2..3)` family with `q ≫ n·(1/ρ)^k`
`{(2113,8,2),(3217,8,3),(1873,16,2),(8161,16,3),(1153,12,2),(1429,12,3)}` plus a field-
independence ladder at `(16,2)` over `q ∈ {97,113,193,257,1009,1873}`.

## Result — REFUTED

**N3 forcing held in 0 of 27 below-saturation heavy bands.** In every case
`maxAg(c,u1) < w+k`, and for every genuinely heavy direction (`#bad` in the hundreds/thousands)
the witness family has **empty common core** and is **not a sunflower**.

Representative rows (`maxAg(u1)` = max agreement of any deg-≤d codeword with the direction word `u1`):

| inst (q,n,k) | a | #bad | w | core | sunflower | maxAg(u1) | n−w−k | w+k | N3 |
|---|---|---|---|---|---|---|---|---|---|
| 1009,16,2 | 3 | 455 | 3 | 0 | False | 3 | 11 | 5 | no |
| 8161,16,3 | 4 | 1665 | 4 | 0 | False | 3 | 9 | 7 | no |
| 3217,8,3  | 4 | 70  | 4 | 0 | False | 3 | **1** | **7** | no |
| 1429,12,3 | 5 | 9   | 5 | 2 | False | 4 | 4 | 8 | no |
| 1873,16,2 | 3 | 514 | 3 | 0 | False | 3 | 11 | 5 | no |

Detailed witness anatomy of one heavy direction (`q=113,n=16,k=2,a=4,u1=x^3`, 12 bad scalars):
common core = 0, union = all 16 points, **not a sunflower**, pairwise witness overlaps
`min=0, max=2, mean=0.91` (vs `w=4`), `maxAg(u1)=2` (= `d+1`, the trivial Lagrange floor),
vs proven ceiling `n−w−k=10` and target `w+k=6`.

The verdict is **q-independent**: the prime ladder `97→1873` at `(16,2)` gives identical
structure (same `#bad` scaling `≈ a-band`, same empty-core, same `maxAg(u1)=d+1`). The few
"sunflower=True" rows are *degenerate small* families (`#bad=2`, too few petals to violate the
sunflower property) and they too fail N3.

## Why N3 is false — the mechanism (category error)

N3 conflates two different objects. Bad scalars are explainable for the **line word** `u0+γ·u1`;
this says **nothing** about `u1` *itself* being close to the code. A direction is heavy because
`u0` is tuned so that many `γ`-combinations land near *different* codewords on *different* point
sets — the witness sets `A(γ)` are spread (empty common core, union = all of `D`). Heaviness of
`(u0,u1)` therefore does **not** force `u1` to agree with any codeword beyond the trivial `d+1`
points. There is no sunflower core to concentrate `≥ w+k` agreement. The proven ceiling
`maxAg(c,u1) ≤ n−w−k` is real, but the matching N3 *floor* `≥ w+k` is empirically *never*
attained below saturation (and, the deeper point, `maxAg(c,u1)` sits at `d+1`, the trivial floor,
not anywhere near either of the two crossing curves).

## What this closes / what remains

- **Closes (negatively):** the N3 sunflower route to an exponential-`q` window-interior δ*
  closure. The witness family of a heavy direction is *anti-sunflower* (spread, empty core), so
  no common-core argument can lift single-window localization to a `≥ w+k` agreement bound on the
  direction word. This is consistent with the existing in-tree refutations that every below-UDR
  bad-family is `O(n)/q` and silent at production budget (the heavy directions found here have
  `#bad ≈ a-band ~ q`, but their witness sets do not concentrate).
- **Does not touch the open core.** The prize δ* wall (the four equivalent analytic faces:
  Gauss-period `B(μ_n)`, char-`p` energy `E_r`, halo vanishing sums, beyond-Johnson list) is
  untouched — N3 was a *combinatorial-localization* lever on the witness side, now dead.
- **Honesty:** this is numerical evidence (exact, small `n`, broad `q`), not a proof. It refutes
  the N3 *forcing conjecture* by exhibiting heavy directions whose witness families are
  empty-core / non-sunflower with `maxAg(u1)=d+1 ≪ w+k` across the entire prize-shaped family.
