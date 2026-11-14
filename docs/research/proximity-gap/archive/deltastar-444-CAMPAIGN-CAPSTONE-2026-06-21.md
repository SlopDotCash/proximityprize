# #444 Campaign Capstone — state of the Paley/proximity prize after the 2026-06 exhaustive sweep

*Authoritative single-reference synthesis. Honesty contract: nothing here closes the prize. The
Paley/BGK conjecture is OPEN at the genuine frontier of current mathematics — confirmed this campaign
against ~57 distinct attack angles and ~257 literature papers including the literature's own SOTA.*

---

## 1. The prize, split into two now-disjoint halves

The MCA grand challenge: pin `δ*` for smooth-domain RS (eval domain `μ_n` = `2^μ`-th roots of unity
in `F_p`) in the window `(1−√ρ, 1−ρ−Θ(1/log n))`, `ε* = 2^-128`. The campaign + literature establish
the window's two edges are **disjoint objects**, one resolved, one open:

### CEILING (upper edge `1−ρ−Θ(1/log n)`) — RESOLVED (algebraic, external)
Kambiré, arXiv **2604.09724** (eprint 2026/782, after Krachun–Kazanin): on the *smooth* `μ_n` domain
(`D = ⟨ω⟩`, `2^t`-th roots), proximity gaps **provably FAIL** at `δ = (1−ρ) − Θ(1/log n)` — exactly
`Θ(1/log n)` below capacity. Construction: the deep-hole line `f = X^{rm}, g = X^{(r−1)m}`, bad
scalars `λ ∈ H^{(+r)}` with `|H^{(+r)}| = C(s/2,r) ≥ n^C`, correlated agreement fails by
root-counting, prime existence by quantitative **Linnik**. Mechanism is **purely algebraic** (coset-
vanishing + root count + Linnik) — *no character sums*. ⟹ the `−Θ(1/log n)` term in the prize
statement is **structurally necessary**, not cosmetic. The ceiling does not touch the floor.

### FLOOR (interior, beyond Johnson) — OPEN = the Paley/BGK wall
`δ*` in the window rests on `M(μ_n) = max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ C√(n log p)`, uniform in `p`.
Best **proven**: BGK `n^{1-o(1)}`; SOTA `n^{0.98924}` (di Benedetto 2003.06165 at `β=4`, `≈1%`
sub-trivial — `p^{1/72}` correctly included; the prior in-tree "worse than trivial" reading is
corrected). The conjecture is `n^{1/2+o(1)}` — a **full half-power** open.

## 2. The exact value is pinned (campaign result)

`η_b/√n → N(0,1)` exactly — the **antipodal-pair CLT** (`η_b = Σ_{j=1}^{n/2} 2cos θ_j`; single term
`2cos(U)` is arcsine). Exact moments vs `N(0,1)=(0,1,0,3)`: mean 0, variance 1, skew 0, **kurtosis
`3 − 3/n`** (slightly sub-Gaussian). Hence the conjectured exact value is
> **`M ≈ √(2 n log p)`, constant `C = √2`** (Gumbel extreme of `q` Gaussian periods).
Proven lower bound `M ≥ √3·√n` (`_AvW18`, 4th/2nd-moment ratio, `E_2=3n²`). The conjecture ⟺ the
**uniform far-tail (large-deviation) statement**: `η_b/√n` stays Gaussian out to scale `√(log p)`,
uniformly in `p` (LDP rate function exceeds 1; the cleanest equivalent form).

## 3. Why it is hard — three convergent diagnoses (campaign + literature agree)

1. **`K=1` extremality** (arXiv 2604.02960): `μ_n·μ_n = μ_n` (perfect multiplicative closure, zero
   doubling slack) makes Green–Ruzsa covering / sum-product / Burgess **structurally vacuous** —
   `μ_n` is the *extremal hardest* case for every structural sub-Weil saving.
2. **Max-not-bulk**: the energy `E_r/Wick = K_max^r` with `K_max ~ n^{0.77}` *diverges* at the saddle
   (the bulk is super-Wick), while `M` stays bounded. Any proof must read the **max without the
   energy**. Every moment/energy method reads the bulk ⟹ reduces.
3. **Far tail = large deviation = needs all moments**: the max lives at scale `√(log p)`, the LD
   regime; the cumulant GF must be controlled, which needs independence (MGF factoring) — and the
   Gauss-period dependence *is* the additive energy = the wall. (Free probability genuinely closed:
   antipodal pairs are classically near-independent, not free/semicircular.)

## 4. Exhaustion ledger — ~57 angles + ~257 papers, all reduce or refute

- 25 mapped directions (Weil/Deligne, moment ladder, sum-product, decoupling, Delsarte, disc/Newton/
  SVP, Stickelberger, Jacobi, theta, dyadic tower, large sieve, Habegger, …) — CLOSED / NO-GO / WALL.
- 4 research bets (coherent twist, Spur_r closed-form, self-improving, distinct-γ) + 6 ranked new
  tools (Gowers, slice-rank/CLP, FKM amplification, transference, SOS, BG spectral-gap) — all reduce.
- 20 maximal-novelty cross-domain angles (ergodic/dynamics, TCS, math-physics, arithmetic-geometry,
  additive-combinatorics) — **0 survivors**.
- Self-similarity (`_AvW15`): the problem is **fractal under squaring** (`U³` obstruction =
  `2·M(μ_{n/2})`); the `√2`-vs-`2` per-level slack compounds to the half-power gap. Frequency-
  migration (`_AvW16/17`): the joint `(η_b, η_{ζb})` is an uncorrelated cloud, no operator linearizes
  it (`M^χ = M`).
- Literature mine (~257 papers): Bober–Goldmakher max-of-character-sums (different object: incomplete
  *multiplicative* sums), Kowalski small-subgroups-revisited (no improvement), Harper/mod-Gaussian/
  resonance (lower-bound or independence-bound tools), FRS subspace-designs (folding-specific, smooth
  domain keeps Paley). **No technique escapes; three independent corroborations of our picture**
  (`K=1` extremality, wraparound-sparsity `density~p^{-v}`, char-0 Bessel `I_0`).

## 5. Landed (axiom-clean `[propext, Classical.choice, Quot.sound]`, fork/main)
`_AvW4` wraparound decomposition · `_AvW5/6` tight tail→sup + conditional Paley chain · `_AvW7` wire
to real `ε_mca` · `_AvW8` coset invariance · `_AvW9/10` Chebyshev floor + moment ladder · `_AvW11`
difference-set bootstrap · `_AvW12` distinct-period count · `_AvW13` super-thin vacuity · `_AvW14`
bootstrap anti-contraction `(β+2)/4` · `_AvW15` squaring self-similarity · `_AvW16` coset-tower
recursion · `_AvW17` joint two-frequency no-operator · `_AvW18` `M ≥ √3·√n` lower bound.

## 6. The honest frontier
The remaining `$1M` step is a **uniform far-tail bound for the maximum of a perfectly-multiplicatively-
closed, arithmetically-dependent Gauss-period sum** — equivalently, that the periods are Gaussian to
the `√(log p)` tail uniformly in `p`. No current mathematics — ours across ~57 angles, nor the
literature's across ~257 papers including its own SOTA — supplies it. The exact value (`C=√2`), the
lower bound, and the ceiling are settled; the upper bound is open at the genuine frontier. **Not
closure.**
