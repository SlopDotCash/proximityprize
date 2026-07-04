# #466 Round 10 — Lane C: 2024–2026 literature freshness sweep (thin 2-power √-cancellation)

**Date:** 2026-07-04. **Agent:** Lane C (Opus). **Verdict:** WALL STANDS — untouched by 2024–2026.

## Object being defended
`M(n,p) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)|`, thin dyadic subgroup `μ_n ⊂ F_p^×`, `n = 2^μ ≈ 2^30`,
`p ≈ n^4` (β≈4), index `m = (p−1)/n ≈ 2^128`. Target `√(n log m)` (≈ Paley Graph Conjecture ~√n).
Proven SOTA at β=4: BGK `n^{1−o(1)}` only, `o(1)` ineffective. (Dossier §2, §3.)

## Foreclosure ledger (what a hit must beat) — dossier §3
- BGK `n^{1−o(1)}`: the ONLY survivor at β=4. `o(1)` non-constructive (BKT+BSG).
- Heath-Brown–Konyagin (Stepanov): needs `n ≫ p^{1/3}` — **vacuous at n=p^{1/4}**.
- Shkredov additive-energy: needs `n ≫ p^{1/3}` — vacuous + √-lossy.
- di Benedetto–Garaev–Garcia–Shparlinski–Trujillo (JNT 215, 2020, arXiv 2003.06165):
  `H^{1−31/2880+o(1)}` for `H > p^{1/4}` — saving → 0 at `n ↓ p^{1/4}`; worse-than-trivial for β>4.775.
- Paley Graph Conjecture (~√n eigenvalue / polylog clique): **OPEN everywhere.**

## The sweep — strongest 2024–2026 hits and why each MISSES

| Paper (arXiv / venue, date) | What it proves | Exact reason it misses the prize regime |
|---|---|---|
| **Kunisky**, *Spectral pseudorandomness & the road to improved clique bounds for Paley graphs* (2303.16475; Exp. Math. 34(4), 2024) | For the **full** Paley graph (QRs, index 2): ESD of random subgraphs → Kesten–McKay; proves the a=1 character-sum estimate (reproves Xi 2022 equidistribution). **Conjectures** min-eigenvalue → KM left edge (numerics only). | Closest to the eigenvalue object but (i) index-2 `μ_{(p−1)/2}`, NOT thin `μ_n` at index `2^128`; (ii) the eigenvalue-edge claim is a **conjecture**, not proven; (iii) needs the Paley subgraph structure absent for a thin subgroup. No proven sup-norm eigenvalue bound at conductor `2^128`. |
| **Yip**, *Exact values & improved bounds on clique number of cyclotomic graphs* (2304.13213 v5, rev. Aug 2025; DCC 2025) | `ω(Cay(F_q^+,S)) ≤ √|S/S| + √(q/p)`; first nontrivial clique bound for generalized Paley graphs of non-square order. | Bounds the **clique number ω**, NOT the eigenvalues `η_b`. Clique bounds are DOWNSTREAM of eigenvalue bounds (Hoffman), not a source of them. Gives nothing on `max_b|η_b|`. b-blind. |
| **Ma**, *Optimal homological vanishing: character sums & Patterson's conjecture over F_q[t]* (2606.26440, Jun 2026) | Square-root cancellation for a character-sum family over the **function field** `F_q[t]`. | **Function-field only** — exactly the D0/EVW "function-field side untouched" note (dossier §3, §4.2). D0 was **airtight-killed for `F_p`** (Jacobi self-braiding non-torsion). The prize object is the prime field `F_p`; this result does not transfer. |
| **Chattopadhyay**, *A short character sum in F_{p^3}* (2505.19654, May 2025) | Burgess-type cancellation for `Σ χ(x+ωy)` over 2-D grids/**intervals** in `F_{p^3}` for boxes of size `p^{3/8+ε}`. | (i) Extension-field grid sums, not prime-field subgroup sums; (ii) **interval/box** structure — Burgess needs an interval; multiplicative subgroups are excluded verbatim (dossier §3, Sawin–Shusterman note). Not thin `μ_n ⊂ F_p`. |
| **Kalmynin**, *Additive irreducibility of multiplicative subgroups* (2504.10202, Apr 2025) | Via Stepanov (Hanson–Petridis): `μ_d` with `A−A=μ_d∪{0}` ⟹ d∈{2,6}; resolves Sárközy (QRs ≠ A+B). | Pure **additive-decomposition** structure. NO magnitude bound. b-blind / structural. Off the wall. |
| **Kim–Yip–Yoo**, *Multiplicative irreducibility of shifted multiplicative subgroups* (2602.20919, Feb 2026) | `(G−1)\{0}` is not a nontrivial product set; no shifted coset is a ratio set A/A. | Pure **multiplicative structure**. NO character-sum bound. Off the wall. |
| **Hegyvári**, *On the distribution of additive energy revisited* (2602.01781, Feb 2026) | Fourier analysis of multiplicative-energy distribution; smallest k with `A^k = F` under small doubling. | Sum-product / product-covering axis. NO magnitude bound at `p^{1/4}`. Multiplicative energy enters only via sum-product → additive, already exhausted at `n^{1−o(1)}` (dossier §19 W2). |
| **Mangerel–You**, *Large sums of high order characters II* (2405.00544, May 2024) | Level-set / **interval** cancellation for high-order primitive characters (`o(x)` for `x>q^δ`). | Interval partial sums + level sets, not subgroup magnitude. Not the `η_b` object. |
| **Kowalski**, *Exponential sums over small subgroups, revisited* (2401.04756, Jan 2024) | **Expository** account of the BGK theorem. | Survey of BGK — the incumbent. No new bound. |
| di Benedetto et al. (arXiv 2003.06165) — checked for any 2025–26 successor | `H^{1−31/2880+o(1)}`, `H>p^{1/4}` | **No newer exponent improvement exists** (2020 remains SOTA for the sum-product route). Saving→0 at the boundary `n=p^{1/4}`. |

## Cross-cutting reasons the whole 2024–2026 crop dies (the three structural walls it hits)

1. **The p^{1/3} floor (HBK / Shkredov / Stepanov lineage).** Every energy/incidence-based route
   needs `n ≫ p^{1/3}` for a nonvacuous saving; `n = p^{1/4}` is strictly below. Yip's Stepanov
   clique work, Kalmynin's Stepanov decomposition, and the Shkredov-energy family all sit above this
   floor or produce no magnitude bound at all. (Dossier §3, §4.4.)
2. **The Bourgain–Gamburd machine is non-abelian only.** The 2025 spectral-gap / super-approximation
   literature (searched: nothing new for abelian multiplicative subgroups) requires a **non-abelian
   product theorem**; a cyclic `μ_n` is abelian ⟹ BG does not apply. This is Tetrachotomy door-(ii)
   saturating at `n^{1−o(1)}`. (Dossier §4.2.)
3. **Interval vs subgroup / function-field vs prime-field.** The genuinely new square-root-cancellation
   results of 2024–2026 all live on structures the prize object lacks: Burgess intervals
   (Chattopadhyay, Mangerel–You) or function fields `F_q[t]` (Ma/EVW). The multiplicative subgroup in
   `F_p` is verbatim excluded by the interval hypotheses, and D0 kills the `F_p` transfer of the
   homological route.

## Regime discipline check
No hit was validated on the full group (the #400 trap). Every candidate was tested against the exact
prize point: proper `μ_n ⊊ F_p^×`, `n=p^{1/4}`, index `2^128`. The b-blind / structural hits (Yip
clique, Kalmynin, Kim–Yip–Yoo, Hegyvári) fail the b-sensitivity requirement of the Meta-Theorem
(dossier §4.1: a winning method must be b-sensitive, deterministic-archimedean, genuinely L∞).

## Verdict
**ZERO survivors.** The wall stands **untouched by 2024–2026**. The closest movement is on the
**eigenvalue side of the FULL Paley graph** (Kunisky, index 2) — but it is (a) a conjecture with
numerics, not a proof, and (b) index-2, not thin. No 2024–2026 paper crosses
`n^{0.989…} → n^{1/2}` at β=4 for thin 2-power subgroups. The missing analytic input does not exist
in the literature (consistent with the prior 67-/29-/26-/35-paper sweeps).

**One line:** Does the wall stand untouched by 2024–2026? **YES.**
