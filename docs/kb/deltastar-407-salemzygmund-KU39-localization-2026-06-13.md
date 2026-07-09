# δ* (#407) — the Salem–Zygmund chaining route IS Kowalski–Untrau Thm 3.9 (effective, but gated at `o(log q/log log q)`)

**Date:** 2026-06-13. **Author:** δ* lane (#407), route: `salemzygmund` (generic chaining / sub-Gaussian MGF).
**Honesty:** NOT a closure. This is a **decisive localization** of the open core of the Salem–Zygmund
route, plus an axiom-clean Lean kernel for the provable half. The prize floor
`B = max_b ‖η_b‖ ≤ C√(n·log m)` remains open. Verdict: **WALL**, but the wall is now pinned to a
single *proven, quantitative* theorem one regime short of the prize.

## The route and what it reduces to

`B ≈ (√p/m)·‖DFT(a)‖_∞`, `a_j = τ(ψ^j)/√p` unimodular over the `m−1` index-`m` characters. Salem–Zygmund:
random unimodular ⟹ `‖DFT‖_∞ ≍ √(m log m)` ⟹ `B ≍ √(n log m)` = prize. Derandomize via generic
chaining / sub-Gaussian MGF.

**Three empirical preconditions, all CONFIRMED on the real Gauss sequence** (probes
`scripts/probes/_wf407_salemzygmund_{increment,tail,derandomize}.py`):

| precondition | what it says | measured | verdict |
|---|---|---|---|
| **metric flat** | L² increment `d̄(c,c')² = 2n` ∀ distinct pairs ⟹ `γ₂` = union bound | `d2_mean/n = 2.00…` for every `(n,p)` (real AND random) | confirmed → chaining has NO multi-scale gain; route content = per-period MGF |
| **proxy O(n), m-uniform** | sub-Gaussian proxy `σ²/n` bounded as `m→∞` at fixed `n` | `σ²/n ∈ [0.88, 1.21]`; slope of `B/√(n log m)` vs `log m` ≈ 0 (+0.003 n=8, −0.026 n=16, −0.077 n=32) | confirmed → the feared "uniformity over m−1 chars" is benign |
| **tail sub-Gaussian** | `P(‖η‖≥t√n) ≈ exp(−t²/2C)`, `C` bounded in `t` | `C ∈ [0.44, 0.69]`, `t∈[1,3]`, p=40009 (m=5001) & p=160001 (m=10000) | confirmed → thinner than Gaussian, NOT a fat (theta-sum) tail |
| **derandomization** | `ρ = ‖P‖_∞(Gauss)/‖P‖_∞(random)` ≈ 1 (genericity) | `ρ ∈ [0.96, 1.22]`, often `<1`; `R=B/√(n log m) ∈ [1.02,1.31]`, no β-trend | confirmed → real phases at most as aligned as random |

So **all preconditions hold**; the route's entire open content is the *one* statement: prove the
**per-period sub-Gaussian MGF** with proxy `σ² = O(n)` at the prize parameters. (`SubGaussianMGF` in
`Frontier/SalemZygmundChaining.lean`.)

## DECISIVE: the open input is EXACTLY Kowalski–Untrau Theorem 3.9 — proven, quantitative, but gated

The reframed input (CLT/sub-Gaussian tail of the subgroup-period value distribution) is **literally the
conclusion of Kowalski–Untrau, "Wasserstein metrics and quantitative equidistribution of exponential sums
over finite fields", arXiv:2505.22059, Theorem 3.9** (PDF on disk; ETH `wasserstein.pdf`):

> **[KU25, Thm 3.9].** For odd prime `q`, `d=d(q)` a prime divisor of `q−1` with `d→∞` and
> **`d = o(log q / log log q)`**, the normalized subgroup sums `(1/√d)Σ_{x∈H} e_q(ax)` become
> equidistributed in ℂ w.r.t. the **standard complex normal `N(0, ½ Id)`** as `q→∞`.

This is the Salem–Zygmund random model (the limit is a sum of `d−1` iid Steinhaus variables → 2-D CLT,
[KU25] §3.5, lines 1235–1281), proven with a **quantitative `W₁` rate** (not just qualitative): by the
triangle inequality (proof, line 1612)

> `W₁(μ_{q,d}, N(0,Σ)) ≤ W₁(μ_{q,d}, ρ_d) + W₁(ρ_d, N(0,Σ))`,

where **term 1** = effective Gauss-sum independence (Lemma 3.10, via the Bobkov–Ledoux / Borda
concentration on `(S¹)^{d−1}`, the explicit-in-`k` form of [KU25] Thm 1.3(7)) — this is the *effective*
form of Rojas–León independence (2207.12439) the route needed — and **term 2** = the `d−1`-dimensional
CLT deficit. The condition `d = o(log q/log log q)` (equivalently `d = o(log q / W₀(log q))`) is exactly
what makes **term 1 dominate term 2** so the total `→ 0`.

### The exact numeric gap (this is the WALL)

`d = |H| = n` (our subgroup order). KU's CLT is proven for `n ≤ log q / log log q`:

| regime | `log q / log log q` (KU ceiling) | prize `n` | gap factor |
|---|---|---|---|
| `p ~ 2^160` (instance `n=2^32`, `β=log_n p=5`) | **≈ 23.6** | `2^32 ≈ 4.3·10⁹` | **≈ 1.8·10⁸** |
| `p ~ 2^256` | **≈ 34.3** | `2^32` | **≈ 1.3·10⁸** |

The prize needs the sub-Gaussian/CLT at `n = 2^32`, eight orders of magnitude past KU's proven ceiling.
This is **the same `log q/log log q` wall** the in-tree moment method hits (`GaussPeriodMomentBound.lean`:
char-`p` transfer of the char-0 energy bound is proven only for `n < 2 log q/log log q ≈ 40` via the
norm bound `q > (2r)^{n/2}`). The chaining route and the moment route bottom out at the **identical
threshold**, now confirmed from the chaining side via an *independent proven quantitative theorem*.

### Why chaining cannot push past it (precise)

The metric is **flat** (`d̄² = 2n` ∀ pairs, measured), so `γ₂` = union bound — there is no multi-scale
geometry for Talagrand chaining to exploit, and no `√log`-saving over the union bound. The entire gap
lives in KU's **term 1**, `W₁(μ_{q,d}, ρ_d)`: effective Gauss-sum independence stops dominating the
`d−1`-dimensional CLT deficit once `d > log q/log log q`. The Bobkov–Ledoux/Borda concentration constant
in [KU25] Thm 1.3(7) degrades with the dimension `d−1` of the torus `(S¹)^{d−1}` exactly at this rate.
So pushing past the wall requires a **dimension-free** (or `d`-uniform) effective Gauss-sum independence —
which is the Paley-graph/Bourgain–Gamburd–Konyagin barrier in disguise, NOT a chaining deficiency.

## The Lean deliverable (axiom-clean)

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/SalemZygmundChaining.lean`
(`lake env lean` EXIT 0; `#print axioms` = `[propext, Classical.choice, Quot.sound]`, NO `sorryAx`):
- `SubGaussianMGF η σ²` — the **single open input** as a named `Prop` (= KU 3.9's conclusion at prize `n`).
- `chernoff_single` — the Chernoff input `X_c ≤ logM/λ + σ²λ/2`.
- **`chernoff_max_re_le`** — the **sub-Gaussian maximal inequality** (the chaining kernel),
  `max_c X_c ≤ √(2 σ² log M)`, proven by optimizing `λ = √(2 log M/σ²)`. This is the load-bearing,
  genuinely-provable half: it consumes ONE exponential moment, not all integer moments.
- `directional_period_bound` — assembly: `SubGaussianMGF ⟹ Re(ζ̄ η_c) ≤ √(2 σ² log m)` (all unit `ζ`).
- `SupNormFromDirectionalNet` / `prize_floor_of_inputs` — the routine constant-factor net reduction +
  conditional prize floor `B ≤ C√(2 σ² log m)`.

## Negative side-finding (don't chase): the theta-sum value-distribution literature is the WRONG model

Demirci Akarsu–Marklof (arXiv:1207.1607, on disk) prove a value-distribution limit law for *incomplete
quadratic* Gauss sums `Σ e_q(p h²)` over an interval — but that limit is **HEAVY-TAILED** (theta-sum law,
their abstract). Our object (multiplicative-subgroup sum) is empirically **sub-Gaussian** (probe: `C` bounded).
So the right model is **KU 3.9 / Lamzouri character-sum CLT (sub-Gaussian)**, NOT the
Demirci–Marklof/Jurkat–van Horne theta-sum law. Conflating them would import a spurious heavy tail.

## Honest scores (prize protocol)

- **Novelty 7/10** — the explicit identification "Salem–Zygmund route's open input ≡ KU 3.9 conclusion,
  proven with a `W₁` rate, gated at `o(log q/log log q)`" sharpens the prior KB self-refutation
  (`deltastar-salem-zygmund-gausssum-chaining`) from "Lamzouri-at-fixed-power" to the precise KU theorem
  with its proof-internal reason for the wall (term 1 vs term-2 dimension deficit).
- **Insight 9/10** — unifies the chaining route and the moment route at the *identical* `log q/log log q`
  threshold, and pins the wall to the dimension-dependence of Bobkov–Ledoux/Borda concentration (= BGK
  Paley barrier), not to any chaining deficiency.
- **Proximity 9/10** — exact prize object/regime; the gap is quantified (factor ~10⁸).
- **Feasibility 4/10** — same Bourgain barrier as every route; what's genuinely better is that the residual
  is now "make KU's effective Gauss-sum independence (term 1) `d`-uniform / dimension-free," a single named
  quantity with a mature toolkit (optimal transport / concentration on `(S¹)^{d−1}`), not an opaque wall.

**Bottom line.** The Salem–Zygmund / generic-chaining route's open core is **exactly Kowalski–Untrau
Theorem 3.9** — a proven, *quantitative* (`W₁`-rate) complex-Gaussian CLT for subgroup-period sums — which
holds for `|H| = o(log q/log log q)` and falls a factor `~10⁸` short of the prize `n=2^32`. Chaining cannot
extend it (flat metric ⟹ `γ₂` = union bound); the entire deficit is the dimension-dependence of the
effective Gauss-sum independence term, i.e. the BGK/Paley barrier. Axiom-clean Lean kernel delivered for the
provable Chernoff/maximal-inequality half. **No closure — a precise, refutation-surviving WALL.**

Cross-refs: `deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md` (predecessor, this supersedes its
"Lamzouri" localization with the sharper KU 3.9 one), `deltastar-407-dyadic-2adic-gauss-tower-verdict`,
`GaussPeriodMomentBound.lean` (same `log q/log log q` threshold from the moment side),
`Frontier/SalemZygmundChaining.lean`, probes `_wf407_salemzygmund_{increment,tail,derandomize}.py`.
Papers: 2505.22059 [KU25] Thm 3.9 (THE theorem), 2207.12439 [RL22] (qualitative independence; KU's term 1
is the effective form), 1207.1607 [DAM12] (heavy-tail theta-sum law = the WRONG model, recorded to avoid).
