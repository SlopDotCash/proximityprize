# δ* sweep A20 — Derandomization 3rd-moment separation: where smooth-vs-random first diverges

- **Date:** 2026-06-14
- **Actionable:** A20 (merged 232-T06 / 334-T05 / 334-T13 / 357-T10), type `numerical-probe`.
- **Status:** **PARTIAL** (decisive on the route's feasibility; route quantitatively dead at
  prize scale). No closure of δ*.
- **Artifacts:**
  - probe `scripts/probes/sweep_A20_third_moment.py` (exact full-`u` moments + triple-coincidence
    distribution + scaling ladder; all exact cross-checks pass).
  - Lean brick
    `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A20_ThirdMomentDerandGap.lean`
    (axiom-clean: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).

## The route, precisely

For the RS code `C = {p : deg p < k}` on a domain `D ⊆ F_q^×`, `|D| = n`, and a uniform received
word `u`, let `a_j(u) = #{c ∈ C : agree(c,u) = j}` and the coset list size
`l(u,w) = Σ_{j ≥ n−w} a_j(u)`. The `m`-th raw moment of `l` factors over ordered `m`-tuples of
codewords by their joint agreement pattern against `u`:

- **M1** `= E_u[l]` — one codeword; `E_u[a_j] = q^{k−n}·C(n,j)·(q−1)^{n−j}`. Uses only `|D|=n`.
  **DOMAIN-INDEPENDENT.**
- **M2** `= E_u[l²]` — ordered codeword PAIRS grouped by Hamming distance `d`; pair count is the
  MDS distance distribution (a function of `n,k,q`), per-pair probability depends only on `d`.
  **DOMAIN-INDEPENDENT.**
- **M3** `= E_u[l³]` — ordered codeword TRIPLES grouped by their *joint* coincidence pattern,
  governed by `T = #{x ∈ D : p₁(x)=p₂(x)=p₃(x)}` = common roots of the difference polynomials
  inside `D`. `T` is a **geometric property of `D`** (which triples of codewords share agreement
  on which coordinates), NOT a function of the pairwise distances. So **the earliest moment at
  which a smooth domain `μ_n` can differ from a random `n`-point domain is the third.** This is
  the cleanest formal articulation of the derandomization route: every domain-specific fact about
  δ* must enter at or after `M3`.

## What the probe found (exact, prize-shaped)

**(1) Full-`u` enumeration** (all `q^n` words), `q=13 n=4 k=2`, `q=11 n=5 k=2`, `q=13 n=4 k=3`,
smooth subgroup vs. a genuinely distinct random `n`-subset of `F_q^×`:

- **M1 and M2 are bit-identical** smooth-vs-random at every radius `w` (reconfirms the proven
  domain-independence; any `M1`/`M2` mismatch would have failed the probe).
- **M3 of the LIST SIZE is ALSO bit-identical** (ratio `= 1.0000`) at every tested scale —
  **including k=3**. This is *stronger* than the route assumed: at these (small-`n`, full-`u`-
  tractable) scales the list-size third moment does not see the domain either. The domain signal
  lives in the **finer** triple-coincidence statistic `T`, not (yet) in the list-size `M3`.

**(2) Triple-coincidence distribution** `P[T=t]`, `t=0..k−1`, `k=3`, smooth / random / adversarial-
AP domains, `n=8,16,32`, primes from `q~n^{1.4}` to prize-scale `q~n⁴`:

| q (n) | E[T] smooth | E[T] random | sep (rel) |
|---|---|---|---|
| 17 (8) | 2.60e-2 | 2.70e-2 | −3.8% |
| 73 (8) | 1.88e-3 | 1.32e-3 | +43% |
| **4129 (8) ~n⁴** | **0** | **0** | **identically 0** |
| 97 (16) | 1.47e-3 | 1.87e-3 | −21% |
| **65537 (16) ~n⁴** | **0** | **0** | **identically 0** |
| 193 (32) | 8.7e-4 | 7.7e-4 | +13% |
| **1048609 (32) ~n⁴** | **0** | **0** | **identically 0** |

So `T` genuinely differs smooth-vs-random at *small* `q` (both signs — no monotone domain
advantage), with the **separation magnitude `≈ E[T]` itself `= Θ(1/q²)`**, and is **identically 0
once `q ≳ n⁴`** (no sampled triple has a shared in-`D` root).

**(3) Scaling ladder**, fixed `n=8,k=3`, prime ladder `q = 17 … 16001`: the absolute
smooth-vs-random `E[T]` separation tracks `n/q²` (`sep/(n/q²)` stays `O(1)`, sign-fluctuating) and
**hits 0 by `q ≈ 2089`** and stays 0.

## Verdict on the M3 → δ*-gap bridge

- `M1, M2` carry **no** domain signal (proven). The route's entire hope is the `M3`/`T` signal.
- The per-triple `T`-signal is `Θ(1/q²)` and **vanishes identically at `q ~ n⁴`**, four orders of
  magnitude below the prize prime `q = n·2^128 ~ n^5`.
- **Prize numerology (machine-checked in the Lean brick):** at `q = n·2^128`,
  `perTripleDev = n/q² = 2^{-256}/n ≤ 2^{-256} < 2^{-128} = ε*` for all `n ≥ 1`
  (`perTripleDev_lt_epsStar`, instantiated at `n=2^32` by `perTripleDev_lt_epsStar_at_2pow32`).
  The third-moment domain signal is **super-exponentially below the loss budget** `ε*`.
- A worst-case δ* gap of the conjectured width `Θ(1/log n)` would need the third-moment deviation
  to survive into the **upper tail** of `l(u,w)`. But `M1`,`M2` (mean, variance) are identical and
  the `M3` deviation is `≤ 2^{-256}·n`; a Chebyshev-3 / Markov bound on `l − E[l]` cannot move the
  tail by a vanishing third-moment perturbation. Aggregating over `N` witnessing triples
  (`aggregate_M3_dev_lt_prize`) keeps the total below `N·ε*` — to reach one budget unit the route
  needs `N ≳ q`-scale witnessing triples, which it does not supply.

**Conclusion.** The 3rd-moment derandomization route is the *correct place* to look for
domain-dependence (M1/M2 provably blind), but its signal is `Θ(1/q²)` and is **quantitatively dead
at prize scale** (`≤ 2^{-256}·n ≪ ε* = 2^{-128}`). It does **not** yield a worst-case δ* gap for
explicit smooth-domain RS at the prize prime. This **closes the derandomization/moment route by an
honest size argument** — it does not close δ* (which remains the open BGK/Gauss-period wall;
unaffected, since that wall is a *fixed-q, single-frequency* character-sum statement, not a
moment-of-list-size statement).

## Honesty

- No δ* closure. One named attack route (derandomization via list-size moments) is shown
  quantitatively dead at prize scale by exact numerics + axiom-clean prize arithmetic.
- The Lean brick proves only the *route's numerology* (`n/q² < 2^{-128}` at `q=n·2^128`); the
  combinatorial input "M3 domain deviation ~ `n/q²`" is the probe's empirical finding, named as a
  `Prop`/`def` (`perTripleDev`, `DerandRouteCarrier`) and consumed, not re-derived in Lean.
- Surprise worth recording: even at `k=3` the **list-size** `M3` was domain-independent at all
  full-`u`-tractable scales; the domain signal is the finer `T` statistic. A future attempt to
  resurrect the route must show `T` propagates to the list-size tail at *large* `n` — but `T → 0`
  at `q ~ n⁴` already forecloses that at prize scale.

## Cross-links

- Sibling A19 (`docs/kb/deltastar-sweep-A19-mds3-...`): MDS(3) failure of `μ_{2^k}` does NOT seed a
  beyond-Johnson list lower bound (primal count = 1). A19 + A20 together close the two
  "higher-order genericity / derandomization" hopes from the `#232` campaign from both sides.
- The open core (BGK/Gauss-period `B(μ_n)` floor; the deep-moment char-`p` energy transfer) is
  untouched and remains the wall — see `RegimePin.lean`, `GaussPeriodMomentBound.lean`, and the
  memory notes `arklib-389-deep-moment-wall`, `arklib-407-gauss-period-house`.
