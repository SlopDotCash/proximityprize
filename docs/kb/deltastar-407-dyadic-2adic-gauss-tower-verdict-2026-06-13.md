# δ* (#407) — verdict on the dyadic-2adic-Gauss-tower route to the DGPH house bound

**Date:** 2026-06-13. **Author:** δ* lane (#407), route assault: dyadic-2adic-gauss-tower.
**Honesty:** the core (DGPH: `B ≤ C₀√(n·log(p/n))` for `μ_n = μ_{2^μ}`, prize regime
`n=2^μ ≤ √p`) remains a recognized OPEN problem. This route does NOT close it. Verdict below is a
**negative structural result** with five reproducible probes. No proof of DGPH is claimed.

## The route, and where it walls

The route's bet: the dyadic structure `n=2^μ` (a tower of quadratic extensions; quadratic Gauss
sums have known Gauss/Stickelberger signs; Lam–Leung vanishing-sum theory for 2-power roots) should
constrain the deep p-defects of the additive energy and beat the generic-subgroup wall
(di Benedetto et al 2020, `t^{1−31/2880}=t^{0.989}`, a half-power short, no use of dyadic structure).

**Result: the 2-adic structure is INERT for the house bound, and where it acts at all it is UPWARD
pressure, never a cancellation lever.** Four independent walls, each measured:

### Wall 1 — the 2-power Gauss sums live in the WRONG place (dual block is O(1))
Face (i): `η_b = (1/m) Σ_{χ trivial on μ_n} χ̄(b)τ(χ)`, `m=(p-1)/n`, `|τ|=√p`. The χ trivial on μ_n
have order dividing `m`; their 2-part divides `v₂(m)=v₂(p−1)−μ`. On the prize diagonal with the
Fermat-exclusion (`odd_part(m)>1`), `v₂(p−1)−μ` is generically **0, 1, or 2** — the 2-power-order
dual block has size `2^{v₂(p−1)−μ} ∈ {1,2,4}`, an **absolute constant**. So the quadratic /
2-adic Gauss signs (Stickelberger) govern `O(1)` of the `m≈p/n` phases. The `~m` phases whose
√-cancellation IS the conjecture all belong to **odd-order** characters — exactly what the 2-adic
lever cannot touch. *(probe: 2-adic dual-block size table, μ=3..12, β∈{4,5}: block ∈ {1,2,4,16}.)*

### Wall 2 — the one named Gauss sign (quadratic) is usually absent, always negligible
The quadratic character of `F_p` is trivial on `μ_n` iff `μ_n ⊆ QR` iff `v₂(p−1)>μ` — a coin-flip on
the prize diagonal (12/20 samples). When NOT trivial, the quadratic Gauss sign does not enter `η_b`
at all. When trivial, it is ONE character out of `m`, contributing `O(√p/m)=O(n/√p)=o(1)` to `B`.
Either way the route's named ingredient is inapplicable or negligible. *(probe: quad-char relevance.)*

### Wall 3 — the deep p-defects are FULL-RANK GENERIC, no 2-adic descent (Lam–Leung gives nothing)
Lam–Leung: char-0 vanishing sums of `2^μ`-th roots are trivial (only the prime 2 → antipodal pairs
`ζ^k+ζ^{k+n/2}=0`). The p-defects are the EXTRA mod-p relations. Measured: the shortest genuine
defects (n=16, p=97: `z^0+z^1=z^3+z^5`; n=32) do **NOT** descend to the subring `Z[ζ_{n/2}]`
(0/96 for n=16; 96/1984≈5% for n=32) and do **NOT** have support in an index-2 coset (0/96; 192/1984).
Cyclic-gap signatures are generic (`[1,2,2,11]`, `[3,3,6,4]`, …). The defects are full-rank in `ζ_n`;
there is no 2-adic descent / vanishing-sum structure to exploit. *(probe: dyadic defect structure;
Lam–Leung descent test.)*

### Wall 4 — defect persists ABOVE the norm threshold AND into the prize regime (norm bound not loose)
The only proven defect=0 mechanism is the norm/Mahler bound `T(r)=(2r)^{φ(n)/2}` (vacuous in regime).
A counting-argument rescue would need an effective vanishing threshold `T_eff ≪ T`, `~poly(r)·n^{O(1)}`.
Measured: the largest defect prime **exceeds** `T` by factors 2.5–3.8 and exceeds `n²` (prize
boundary) by up to 17× (n=16, r=3: defect at p=4561≈2^12≈n^3, with clean/defective primes
interleaved non-monotonically). So `T_eff` tracks the exponential-in-n norm threshold, not a small
poly. The norm bound is essentially tight; no loose-bound counting rescue exists. *(probe: defect
persistence window.)*

## The genuine (small) new finding: antipodal closure is UPWARD pressure

The one concrete effect of the dyadic tower is that `μ_{2^μ} ∋ −1` (= `z^{n/2}`), so `μ_n` is closed
under `x↦−x` and `η_b = 2Σcos(2πbx/p)` is real. This **inflates** the house, it does not cancel it:
- Matched-order sweep (β=4): pure-2-power `C₀≈1.21` vs odd-order `C₀≈0.96`. **Dyadic is HIGHER.**
- Matched (n,p) random control: subgroup `C₀≈1.15` tracks the no-negation random baseline `≈1.17`,
  far below the artificial `-1`-closed random `≈1.39–1.57`. Multiplicative structure keeps it
  disciplined at the **generic-subgroup level** — but never below it.

So the dyadic structure confers **no advantage** to either the energy moment `T_m(H)` (the quantity
the di Benedetto/Shkredov bound rests on) or the house. The `−1`-closure (the dyadic signature) is
the lone structural lever and it points the wrong way.

## Precise wall statement (for the schema)

> The dyadic-tower lever fails because the 2-power Gauss-sum / Stickelberger / Lam–Leung structure
> sits in `μ_n` and in the **quadratic/2-power part of `(p−1)`**, whereas the cancellation that DGPH
> demands is among the `m≈p/n` Gauss phases of **odd-order** characters trivial on `μ_n`. The 2-adic
> data governs an `O(1)`-size block of those phases (`2^{v₂(p−1)−μ}`), is generically negligible or
> absent (quadratic char), and the deep p-defects are full-rank-generic with no 2-adic descent;
> meanwhile `−1`-closure only inflates the house to the generic level. No reduction to a tractable
> 2-adic statement exists. This is consistent with di Benedetto et al making zero use of dyadic
> structure and stalling a half-power short.

**Made real progress toward the bound:** NO (the route is refuted, not advanced). **New ground:**
a refutation + the exact mechanism (4 walls) + the antipodal-inflation structural fact.
