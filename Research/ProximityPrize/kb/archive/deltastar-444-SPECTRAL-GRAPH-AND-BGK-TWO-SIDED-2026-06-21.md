# #444 — The spectral-graph direction and the two-sided BGK bracket (2026-06-21)

*Essay on the directions opened by the 2026-06 arXiv batch, why the one genuine one reduces, and the
two-sided BGK result it produced. Honesty contract: nothing here closes the prize. The Paley/BGK upper
bound is OPEN; this essay is honest about which directions prove and which reduce.*

---

## 0. The batch (49 papers, Feb–Jun 2026): one signal, 48 collisions

A user-supplied batch of 49 fresh arXiv papers was mined (triage → conditional deep-read → adversarial
synthesis, workflow `wgbvzdgk8`). **48 are noise** — "Paley" here is *Littlewood–Paley* theory and
*Paley–Wiener* uniqueness (harmonic analysis), plus PDE (Navier–Stokes, EMHD), operator theory, and graph
theory unrelated to our object. Keyword collision, not subject overlap; identical outcome to the prior
batch. **Exactly one paper is on-topic:**

- **arXiv 2604.06513**, *"The nature of the spectrum of generalized Paley graphs and weak Waring numbers."*
  Generalized Paley graph `Γ(k,q) = Cay(F_q, (F_q^*)^k)`; classifies when the spectrum is real
  (undirected ⟺ real), the imprimitivity, and reduces *weak* Waring numbers to classical Waring numbers
  (Cochrane–Cipra 2012). It studies the **structure** of the spectrum, not the **size** of the second
  eigenvalue. So it does not bound `M`, but it sharpens the framing — and that framing is the one genuine
  direction this batch opened.

## 1. The direction: `M = λ₂` of a generalized Paley graph

Our object is `M(μ_n) = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`, `μ_n =` the `2^μ`-th roots of unity
in `F_p^*` (a thin multiplicative subgroup, `n = 2^μ ~ p^{1/4}`). The paper reframes this exactly:

> `η_b` are precisely the eigenvalues of the **Cayley graph** `G = Cay(F_p, μ_n)` — an `n`-regular graph
> on `p` vertices, undirected because `−1 ∈ μ_n`. The trivial eigenvalue is `η_0 = n` (the degree); the
> **spectral gap / second eigenvalue is `M`**. The bound `M ≤ 2√n` is exactly the **Ramanujan** property,
> and "`M ≤ 2√n`" ⟺ the **Paley Graph Conjecture** (open; best proven is BGK `n^{1−o(1)}`).

This is already known in-tree (`GeneralizedPaleyRamanujan.lean`, `GaussPeriodMomentBound.lean`, Liu–Zhou
Thm 115), but it was worth re-opening because **graph spectral theory is a genuine upper-bound toolkit**:
Alon–Boppana, Hoffman ratio, Lovász `θ`, interlacing, Cheeger, expander mixing, Ramanujan/Friedman,
flag-algebra SDP — these *are* the methods one would reach for to bound a second eigenvalue. If any of them
upper-bounds `λ₂` for *this* graph, it proves (a piece of) the prize. So we attacked with all twelve,
adversarially verified (workflow `wyl5pf41u`, 12 tools × attack → refute → synthesize).

## 2. Why it reduces: the three structural facts and the Lovász-`θ` circularity

**Outcome: 0 of 12 tools produced any non-vacuous upper bound on `λ₂`.** Distribution: 7× only a
`√n`-scale *lower* bound, 2× vacuous, 2× reduces-to-wall, 1× the trivial `λ₂ ≤ d = n`. Every "new fact"
offered (8 of them) was re-verified TRUE but rejected on novelty: already in-tree, textbook, or
wrong-direction-and-vacuous. The reduction is **structural and uniform**, forced by three properties of
this specific graph:

1. **Abelian Cayley ⟹ the eigenvectors are the fixed, known additive characters `χ_b`.** There is no
   eigenvector freedom for a spectral method to exploit; the eigenvalues `η_b = Σ_{x∈μ_n} e_p(bx)` are
   *pinned* by the connection set. Any "spectral bound on an eigenvalue" is literally re-deriving the BGK
   incomplete character sum. The spectrum is a perfect readout of the arithmetic.
2. **Negation-closed (`−1 ∈ μ_n`) ⟹ antipodal spectrum (`λ₂ ≈ +M`, `λ_min ≈ −M`).** This kills all
   odd-moment leverage: `trace A³ = Σ_b η_b³ = 0` carries **zero** information about `M` because the `+M`
   and `−M` cubes cancel. (The exact identity `Σ_{b≠0} η_b³ = −n³`, i.e. the graph is **triangle-free**,
   is true and clean — an immediate corollary of Lam–Leung "no odd vanishing sums of `2^μ`-th roots" — but
   it constrains nothing about the extreme eigenvalue.) It also collapses Hoffman/Lovász/EML onto `λ_min`,
   which is just `−M`: the same object, wrong sign.
3. **`F_p` additively prime-cyclic ⟹ no proper additive subgroup ⟹ no spectrum-contracting equitable
   partition.** The only equitable partition (the `μ_n`-coset / Galois quotient) is **lossless** — its
   quotient eigenvalues are exactly the distinct `η_b` — so interlacing returns `λ₂(A) ≥ λ₂(B) = λ₂(A)`, a
   tautology. There is no coarsening that loses the max.

**The sharpest single diagnosis is Lovász `θ`** — the *only* tool of the twelve that is structurally an
upper-bound generator, so watching it collapse names the wall exactly. For a `d`-regular vertex-transitive
negation-closed Cayley graph,
> `θ(G) = N·M/(n + M)` exactly — `θ` is an algebraic **readout** of the spectrum, *monotone increasing* in
> `M`. So an upper bound on `θ(G)` WOULD invert to an upper bound on `M`. **The right direction exists.**

But the sandwich `θ(G)·θ(Ḡ) = N = p` means bounding `θ(G)` above needs `θ(Ḡ)` bounded *below*, and the only
unconditional lower bound on `θ(Ḡ)` is the **clique number `ω(G) = 2`** — because `G` is triangle-free.
`θ(Ḡ) ≥ 2` inverts to the **trivial `M ≤ n`** (off by `√(n/log p)`). Any *nontrivial* lower bound on
`θ(Ḡ)` must read `Ḡ`'s eigenvalues `p−1−n−η_b`, which contain `M` — **circular**. And the
self-complementary escape `θ(Ḡ) ≥ √N` (which would give the prize) is FALSE for thin `n` (`Ḡ` is dense,
`G` is not self-complementary). **On a translation-invariant Cayley graph the LP dual optimum IS the
eigenvalue set** — Lovász `θ` does not bound the Gaussian periods because, on this graph, it *is* the
Gaussian periods. The same circularity defeats all twelve tools; `θ` is where it is most visible.

> **Net.** Graph-spectral methods read the **bulk** (degree, edge count, energy `E₂`, second moment) and
> the **most-negative** eigenvalue (independence/chromatic side). `M` lives at the **`√(log p)`-far-tail of
> the most-positive nontrivial eigenvalue** — a large-deviation quantity invisible to every bulk/structural
> invariant. The missing factor is uniformly the `log p`: every floor is `p`-independent
> (`2√(n−1)`, `√3·√n`, `n²/(p−n)→0`), while `M ~ √(n log p)` diverges in `p`. The spectral toolbox is now
> adversarially confirmed **exhausted for the upper direction**.

## 3. What it produced: the two-sided BGK bracket (`_BGKTwoSided.lean`, axiom-clean)

The directive *"prove both bounds of BGK"* is answered honestly by isolating exactly what is provable on
each side of `M(μ_n) ≍ √(n log p)`. Writing `a_b := |η_b|² ≥ 0` over `b ≠ 0` (DC term excluded) so
`M² = max_{b≠0} a_b`:

- **LOWER (unconditional, proven).** `ratio_le_max`: `M² ≥ (Σ a²)/(Σ a)`. With the Gauss-period moments
  `Σ_{b≠0}|η_b|² = pn − n²` (Parseval) and `Σ_{b≠0}|η_b|⁴ = p(3n²−3n) − n⁴` (`E₂ = 3n²−3n`), this is
  `M² ≥ (p(3n²−3n) − n⁴)/(pn − n²) → 3n − 3`, i.e. **`M ≥ √3·√n·(1−o(1))`**, strictly above the trivial
  Parseval `√n`. (This `√3·√n` is the strongest *clean unconditional* lower bound; Alon–Boppana
  `2√(n−1)` is a slightly larger constant on the same `√n` scale but textbook and not prize-relevant — both
  are `p`-independent floors.)
- **UPPER, trivial (unconditional, proven).** `max_le_sum_of_nonneg`: `M² ≤ Σ a = pn − n² ≤ pn`, i.e.
  **`M ≤ √(pn)`** (a single squared period ≤ the `L²` energy). For thin `n ~ p^{1/4}` this is `≈ n^{5/2}`:
  true but far from the conjecture.
- **UPPER, sharp (CONDITIONAL on the wall, proven consumer).** `pow_max_le_sum_pow` +
  `sharp_upper_of_energy_bound`: `M^{2r} = (max a)^r ≤ Σ a^r = Σ_{b≠0}|η_b|^{2r}`, so *if*
  `Σ_{b≠0}|η_b|^{2r} ≤ B`, then `M² ≤ B^{1/r}`. With the **DC-subtracted Wick value** `B = (2r−1)‼·n^r` at
  `r = ⌊log p⌋`, optimizing gives **`M ≤ √(2 n log p)`** — the conjecture. The hypothesis is exactly the
  open additive-energy wall; everything downstream of it is unconditional.

The **DC subtraction is essential and is the subtle correctness point**: the *full*-energy form
`E_r(μ_n) ≤ (2r−1)‼·n^r` (including `η_0 = n`) is **false** past the prize-depth DC crossover (in-tree
`DCEnergyEssential.not_gaussianEnergyBound_of_deep`). Summing over `s = {b≠0}` — as `_BGKTwoSided` does —
is exactly the usable DC-subtracted object. This file is the self-contained two-sided companion to the
in-tree one-sided bridges `GaussPeriodMomentBound.lean` (moment method) and `GeneralizedPaleyRamanujan.lean`
(Ramanujan), adding the matching unconditional lower side.

> **The honest two-sided statement:** `√3·√n ≤ M ≤ √(pn)` is fully proven; the sharp upper edge
> `√(2 n log p)` is reduced to the single open DC-subtracted energy inequality. The gap between `√n`
> (proven lower) and `√(n log p)` (conjectured upper) is the prize. **NOT closure.**

## 4. The honest frontier (unchanged, now triple-confirmed)

Both directions at the `√(n log p)` scale are hard, for the *same* reason, symmetric across the bracket:

- The **upper** bound needs `Σ_{b≠0}|η_b|^{2r}` to stay Wick-like (`≤ (2r−1)‼ n^r`) to depth `r ≈ log p`.
  Numerically `K_r = (E_r/\text{Wick})^{1/r}` is sub-Wick at shallow `r` but climbs **above** 1 at the
  saddle `r ≈ log p` (`K_max(32) ≈ 1.13`, growing `~ n^{0.77}`), so the moment route's best upper bound
  `min_r (pE_r)^{1/2r}` carries a `K_max^{1/2} ~ n^{0.385}` factor and lands at `n^{0.885}√(log p)` (di
  Benedetto SOTA), **not** `√(n log p)`. The `n^{0.385}` gap is the wall.
- The **lower** bound `M ≥ c√(n log p)` is *also* far-tail: for `n = 16` the bulk energy is sub-Wick
  (`E_r/\text{Wick} → 0` at deep `r`), so the rare large value that makes `M ≈ √(n log p)` is **not** forced
  by the (sub-Wick) bulk moments. Both edges of the bracket are gated on the same large-deviation
  control that the bulk invariants cannot see.

The wall, in its sharpest equivalent form: **whether short (`≤ 2 log p`-term) `±1`-relations of `2^μ`-th
roots of unity vanish modulo the prize prime `p`** (the char-`p` wraparound that pushes `K_r` above the
char-0 Wick value at depth `log p`). No tool in the 2024–2026 literature — this 49-paper batch included —
and no graph-spectral invariant supplies it. The exact value is pinned (`C = √2`, Gumbel max of `q`
near-Gaussian periods), the lower bound and ceiling are settled, the upper bound is open at the genuine
frontier.

---

*Landed this round (axiom-clean `[propext, Classical.choice, Quot.sound]`, pushed to fork/main):*
`_BGKTwoSided.lean` — the two-sided bracket (`ratio_le_max`, `max_le_sum_of_nonneg`, `pow_max_le_sum_pow`,
`bgk_two_sided`, `sharp_upper_of_energy_bound`). *Workflows:* `wgbvzdgk8` (49-paper mine), `wyl5pf41u`
(12-tool adversarial spectral attack). **Not closure** — the honest two-sided BGK statement with the open
edge named exactly.
