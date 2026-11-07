# MDS average is a dead end; δ* is purely worst-case, located in the window (2026-06-13)

> **Scope correction (2026-10-28 audit, T48).**
> - **Not specific to MDS.** The average-ball formula `avg(a) = q^k·Vol_q(n−a)/q^n` is correct for
>   **any** code with `q^k` codewords; it does not use the MDS property.
> - **Sampled lists are lower bounds.** The "worst-case list" row comes from sampled words, so it is
>   a lower bound on the worst case. It cannot give a universal worst-case upper bound.
> - **No `δ*` interval follows.** `δ* ∈ (0.625, 0.688)` is not established as the exact MCA `δ*`
>   interval: that needs the missing list-to-MCA bridge and an extremality input.
> - **Averages are not useless.** An exponentially small average shows that this particular average
>   does not determine the threshold. It does not exclude every use of average information.

Executed computation (not asserted). Closes off the "use the explicit MDS weight enumerator" avenue
as a **negative result**, and pins concretely where δ* sits.

## 1. The average list is exponentially negligible in the window (closed, MDS)
RS[n,k] is MDS; the average # codewords within radius `n−a` of a random word is the closed form
`avg(a) = q^k·Vol_q(n−a)/q^n`. Computed exactly:

| n=16,k=4, q=65537 | a=5 (δ=.69) | a=6 | a=7 | a=10 |
|---|---|---|---|---|
| worst-case list | 273 | 7 | 2 | 1 |
| **avg (MDS, closed)** | 6.7e−2 | 1.9e−6 | 4.1e−11 | 1.0e−25 |
| worst/avg | 4.1e3 | 3.8e6 | 4.9e10 | 9.9e24 |

Throughout the window `avg(a) ≪ 1` (a good code: random words are far from it). **The closed MDS
enumerator therefore contributes nothing to δ*** — every bit of the threshold is the worst/avg gap.

## 2. δ* is set by the worst-case list crossing the budget — and it lands strictly in the window
δ* = `1 − a*/n`, `a*` = band where worst-case `L(a)` crosses `ε*q`. For the deployed budget
`ε*q ≈ n` (e.g. `n=16`): at `n=16,k=4`, `L(5)=273 > 16` (bad) but `L(6)=7 < 16` (good), so
`δ* ∈ (0.625, 0.688)` — **strictly between Johnson (0.5) and capacity (0.75)**, near capacity. So:
- δ* is **not** Johnson (the worst-case list stays below budget for a band *above* Johnson), and
- δ* is **not** capacity (it crosses the budget strictly inside the window).

This is the in-window δ* the prize asks for, and it is governed entirely by the **worst-case
deep-hole list curve `L(a)`**, which has no closed form (candidate-limited computations;
§prior notes) and is the genuine open object.

## 3. Consolidated map of the reduction (what every avenue terminates at)
Across this session every face was pushed and each terminates at the **worst-case beyond-Johnson
list of smooth RS**, `L(a)`:
- LD challenge = `Λ` = `L(a)` directly.
- MCA challenge = `L(a)` via the ABF26 Thm 5.1 bridge (√-loss caps the bridge at Johnson; the window
  needs `L(a)` itself).
- Energy/Fisher = pairwise bound = exactly Johnson; beyond needs triple+ coincidences = `L(a)`.
- Moment hierarchy: quadratic energy CLEAN in prize regime (not the n^{22/9} exponent), but the
  propagation to `L(a)` is **refuted** (list is p-independent at shallow bands).
- Average/MDS: negligible; `L(a)` is purely worst-case (this note).
- Field size: enters δ* ONLY via the budget `ε*q` (proven: `censusDomination_pin_largeField`).

**Net:** δ* = `L^{-1}(ε*q)` with `L` the field-independent worst-case deep-hole list curve of smooth
RS. `L(a)` is the irreducible open object; no closed form found, and the known constructions
(CS25/BCHKS, gated on subgroup-sumset Conj 1.12) only pin its near-capacity tail to
`1−ρ−Θ(1/log n)`. **No closed δ* conjecture with ≥9/10 feasibility is established; the open core is
this single worst-case list curve.** Recorded honestly — not fabricated as solved.
