# I_∞ campaign — iinf-qindep workflow verdict (wf_84b1d071-195, 2026-06-15)

> **CORRECTION (see doc 06):** the "floor HOLDS at the window edge with margin" headline below was
> TOO OPTIMISTIC. It rested on a worst-direction `exp(c·n)` extrapolation that never measured the exact
> n=32 edge cell. The fuller core-stratified decay-rate workflow (06) shows the PURE window-edge
> multiplier GROWS 1→13, the "3504 spike" was char-p polluted, and all 10 decay angles reduce to the
> open Gauss-period bound. The PROVEN bricks below (support law, recursion) stand. The p-independence
> brick does not (see the audit-T163 correction in brick 1), and the floor-holds conclusion does NOT. Read doc 06 for the reconciled verdict.

9-thread workflow on the q-independent finite incidence. Synthesis of 8 completed threads
(+ 9th, a √2-orbit plateau lower-bound for n=64, consistent). **Originally headlined as "the prize
FLOOR HOLDS at the window edge, empirically n≤32 + 3 proven bricks". That headline is withdrawn. The
floor-holds conclusion falls to the CORRECTION above, and the "3 proven bricks" count to the brick-1
correction below.**

## Object disambiguation (resolves all cross-thread "contradictions")
Three distinct invariants of `e₁(S)` over `e₂(S)=0` w-subsets were measured:
| invariant | w=4 plateau value | source |
|---|---|---|
| `#distinct e₁` (raw — the **prize** object) | `n²/4 − n = n·(n/4−1)` | csp, my round-4 data ✓ |
| `#orbits` of e₁ under μ_n rotation | `n/4 − 1` | csp |
| `#distinct |e₁|²` (real-subfield degree) | `n/4` | symfunc, vanishing-sums |
| worst-dir k=2 raw-γ (DIFFERENT object) | `(n/2−1)²` | a9a63bf4 (flagged as conflation) |
All consistent once disambiguated; orbits free of size n ⇒ raw = n·orbits.

## Three claimed bricks (two proven; brick 1 corrected)
1. **p-independence — NOT established as stated (corrected, audit T163).** The original claim was
   `I(δ) = deg(Z_{n,δ})` for `q > q₀(n)`, with `Z_{n,δ}` the per-S root set of one univariate
   resultant `R_S(γ)=∏_{z∈S}(Q₀(z)+γQ₁(z)−W(z))` of q-independent degree ≤ s.
   **That product encodes the wrong event.** `R_S(γ)=0` iff *some* factor vanishes, i.e. the line
   point at `γ` matches at **at least one** `z∈S`. Agreement on `S` needs the residual to vanish at
   **every** `z∈S`, so the per-S bad set is the **common** root set of the `s` factors (the roots of
   their gcd), not the union of their roots.
   Each factor is linear in `γ`. So when some `Q₁(z)≠0`, the per-S bad set has at most one element:
   it is nonempty iff all per-point roots `γ_z = (W(z)−Q₀(z))/Q₁(z)` coincide (and `Q₀(z)=W(z)`
   wherever `Q₁(z)=0`). Counting how often they coincide mod `p` is a coincidence/discriminant question
   about the `γ_z`. The root count of `R_S` does not compute it: `deg R_S = #{z: Q₁(z)≠0}` counts
   per-point roots, not bad scalars.
   What stands: the Lean file `Frontier/_PIndependenceLangWeil.lean` proves generic root-count = degree
   facts for split separable polynomials, and their transfer under good reduction, axiom-clean. Its
   identification of those counts with the incidence `I(δ)` rests on the product formula above, so it
   is **not** a proof that the prize-scale incidence equals the char-0 count. The measured bad-prime
   thresholds (n=16→17, n=32→2113, n=64→2753) remain empirical data about the probe's own computation.
2. **Support/vanishing law — PROVEN via Lam-Leung.** `I(n,w)=0` for `w ≡ 2,3 (mod 4)`: a vanishing
   sum of 2^a-th roots needs an even # of terms, `C(w,2)` even ⟺ `w ≡ 0,1 (mod 4)`.
3. **Tower descent recursion — VERIFIED exact.** `I(2N,k,2m') = I(N,k/2,m')` (imprimitive descent);
   primitive vanishing `I=0` for odd m≥3; seed `I₁(n,w)=Σ_{s≡w(2)} C(n/2,s)·2^s − [w even]`.

## THE FLOOR VERDICT (decisive thread: empirical-growth-law-and-crossing)
Worst-direction incidence indexed by **offset `j = w − k`** (depth below code dim; δ = cap − j/n):
- Near-capacity **exponential** `I(j=1) ~ exp(c·n)`, c≈0.5 — explosion confined to a **constant-width
  band j = 1,2,3**.
- Measured char-0 profiles (ρ=1/4): n=8 `[40,8,8,1,1]`, n=16 `[3984,88,8,16,16,8,1]`,
  n=32 `[≫,11440,88,88,…O(1) tail]`.
- Window edge `w* = k + Θ(n/log n)` ⇒ offset `j* = n/log n ≈ 3.8, 5.8, 9.2` (n=8,16,32), **strictly
  deeper than the crossing offset `j_cross ≈ 2, 2.5, ≥4–5`; the gap `j* − j_cross` WIDENS with n.**
- Directly measured window-edge values: **n=8→I=1, n=16→I=8, n=32→O(1) — all ≪ n budget.**
- **⇒ PRIZE FLOOR HOLDS WITH MARGIN at the window edge** (the I=n crossing pins a thinner
  near-capacity threshold, NOT δ*).

## Correction to my round-4 pessimism
Round-4 ("multiplier stays n/4−1 → quadratic at the window edge") used ρ=1/2 and **mis-located the
window edge at the near-capacity plateau**. Correctly indexed by offset j, the n/4−1 plateau is the
*near-capacity* regime (small j); the true window edge (j*=n/log n) is **deeper**, where incidence is
O(1)–O(n). Floor holds. My round-4 quadratic was the explosion band, not the edge.

## Honest gap (why this is not yet a closure)
Empirical (n ≤ 32) + a *fitted* `exp(c·n)` near-capacity law + the 2 proven bricks (brick 1, p-independence,
is not established; see its correction). The remaining
step is the **asymptotic decay-rate proof**: that the near-capacity explosion stays confined below
`j* = n/log n` for ALL n. That is where the open Gauss-period/Paley core may re-enter — BUT the
needed statement is potentially **weaker** than full `B ≤ 2√n`: only that the explosion is confined
shallower than the log-backoff window. **This is a genuinely new, possibly-provable handle** that the
72-sweep's blanket "= open Gauss-period" did not isolate. Fed directly into the decay-rate workflow.

Tools: /tmp/c32*, /tmp/prize_attack/. Threads' Lean brick: the p-independence resultant scheme (generic root-count law only; its link to the
incidence is the flawed product formula corrected in brick 1).
Related: [[arklib-407-multiplier-decay]], [[arklib-407-72-conjecture-sweep]], [[arklib-407-r4-char0-correction]].
