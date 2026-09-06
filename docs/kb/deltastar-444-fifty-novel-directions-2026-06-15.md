# Fifty Novel Directions for the δ\* Prize
### A successor manifesto: closed, non-collapsing conjectures in mathematics the campaign never had

*Successor to `deltastar-444-new-math-manifesto-2026-06-15.md`. That manifesto argued the
cancellation is not on the domain `μ_n` but in a **relocated universe** (parameter / `p`-adic /
entropy) and gave 10 angles. This document raises the bar: **50 directions, each a CLOSED
conjecture** (a self-contained inequality about an explicitly-defined object — no "δ\* follows IF
[some other open problem]"), **each defended against collapse to Johnson (`n^{1/2}`) or BGK
(`max_b|η_b|`, the wall).***

> **Honesty contract.** Everything below is **exploration**, in the bold-conjecture sense the
> programme permits: these are *proposals to attack*, many likely false. None is claimed proven.
> The value is a falsifiable map of mathematics the campaign has **not** touched (verified by
> grep, counts cited). Refutations belong in `Research/ProximityPrize/DISPROOF_LOG.md`; a closed conjecture shown false
> with a countermodel is a *successful* iteration.

---

## 0. The conservation law we must break

The prize object is, exactly and in-tree,
> `M(μ_n) = max_{b≠0} | Σ_{x∈μ_n} e_p(b x) | ≤ C·√(n·log(p/n))`,  `n = 2^μ ≪ √q`,  `M(μ_n) = λ₂(Cay(F_p, μ_n))`.

The route-elimination meta-theorem is a **conservation law**: *any estimate whose only input is the
domain's first- and second-order arithmetic — size, additive energy `E_r`, Sidon-ness, the spectral
radius, the `2`-norm — is blind to the phase that separates the worst `b` from the average `b`, and
therefore caps at Johnson `n^{1/2}` (Cauchy–Schwarz / Parseval) or needs moment depth `r≍log q`
(where char-`p` anomalies kill it).* The `√log` excess is a **rare-event / tail** phenomenon, and
tails are invisible to second moments.

So a direction is **viable** iff it injects information the conservation law forbids second moments
to see. There are exactly four such information sources, and every direction below is tagged by which
one it uses (this tag *is* its non-collapse certificate):

- **[Φ] phase** — uses the argument/sign of partial sums, not `|·|²`.
- **[P] parameter** — relocates to the `q^{k+1}`-point offset family where Deligne/Katz are sharp (`n<√q` irrelevant).
- **[π] non-archimedean** — uses the `2`-adic / `p`-adic structure (`μ_n` is `2`-power; its hardest structure is `2`-adic, not archimedean).
- **[H] entropy/rare-event** — bounds the supremum of the structured process by its metric entropy / information content, absorbing `√log` rather than estimating it.

A direction that uses none of these collapses by the conservation law; a direction that uses one is at least *not pre-refuted*. Each entry states its tag and why that tag evades Johnson/BGK.

---

# PART A — 25 mathematics that do not yet exist

*Each: the new object, the closed conjecture about it, why it has never existed, why it is
nonetheless feasible (the pieces are present; only the synthesis is missing), and the non-collapse tag.*

### Cluster A1 — Phase-aware replacements for energy (defeat "[2nd moment] = phase-blind")

**N1. Signed additive energy `E^Φ_r`.** *New object:* `E^Φ_r(μ_n) = Σ_{x_1±…±x_{2r}=0, x_i∈μ_n} χ_2(Δ)`,
the additive-energy count **re-weighted by an oscillatory quadratic character `χ_2` of the discrepancy
`Δ` of the solution**, so cancellation among solutions is retained. *Conjecture (closed):*
`|E^Φ_r(μ_n)| ≤ r!·n^r / 2^{r}` for `r ≤ log m`. *Why never existed:* additive energy is **by definition**
a non-negative count (`|·|²` of a convolution); no one has put a phase **inside** the energy because the
classical use (Cauchy–Schwarz) needs non-negativity. *Feasible:* the weight `χ_2(Δ)` is explicit and the
char-0 unsigned `E_r` is already proven `≤(2r−1)!!n^r` in-tree — the signed version is a strict refinement
of an existing computation. *[Φ]:* a signed energy is not a second moment; its smallness is a cancellation
statement, exactly what the conservation law says energy cannot see.

**N2. The moment-zeta with analytic continuation.** *New object:* `Z_{μ_n}(s) = Σ_{b≠0} |η_b|^{2s}`
as a function of **complex** `s`, with its meromorphic continuation and functional equation. *Conjecture
(closed):* `Z` satisfies a Phragmén–Lindelöf bound on the strip `Re(s)∈[1, log m]` that forces
`M = lim_{s→∞} Z(s)^{1/2s} ≤ √(2n log m)`. *Why never existed:* moments have only ever been used at
**integer** `r`; a complex-`s` continuation of a finite power sum, with its own functional equation, is a
new analytic object. *Feasible:* `Z` at integer `s` is the proven raw-moment identity `q·E_s − n^{2s}`;
interpolation in `s` is a Mellin transform of an explicit measure. *[Φ]+[H]:* the continuation reads
**inter-moment** correlations (the whole sequence), not any single moment — exactly the structure integer
moments throw away.

**N3. Heat trace of the period spectrum.** *New object:* `Θ(t) = Σ_b e^{−t η_b²}`, the partition function
of the `m` periods as a thermodynamic ensemble. *Conjecture (closed):* `Θ(t) = m·I_0(2t·?)·e^{−tn}(1+o(1))`
with a subleading term that gives `max η_b² ≤ 2n log m` by a saddle-point read-off. *Why never existed:* the
period spectrum has never been treated as a heat kernel / spectral action (Connes–Chamseddine style); the
ensemble viewpoint is new for these arithmetic spectra. *Feasible:* `Θ` is an entire function of `t` whose
Taylor coefficients are the proven moments `q E_r`; the saddle point is elementary. *[H]:* the exponential
weight `e^{−tη²}` emphasizes the **tail** (large `η`), the rare event the second moment averages away.

### Cluster A2 — Locus-transfer made into closed statements

**N4. Subgroup-relative étale cohomology with a thin-set completeness theorem.** *New object:* a cohomology
`H^*_{μ_n}(𝔸^1)` of the pair, whose Lefschetz trace formula **completes the incomplete sum without the
`n<√q` Weil obstruction**, because the "boundary" term is taken relative to `μ_n`. *Conjecture (closed):*
`dim H^1_{μ_n} ≤ C·μ = C·log_2 n`, hence `|Σ_{x∈μ_n} e_p(bx)| ≤ (dim H^1)·√q / m ≤ C√(n log(p/n))`.
*Why never existed:* completeness theorems (Weil, Bombieri) complete to the **full** group; no relative
theory for a **thin** subgroup exists because there was no motive to build one. *Feasible:* the relative
cohomology of `(𝔾_m, μ_n)` is computable (`μ_n` is the kernel of `[n]`); the conjecture is a bounded-`H^1`
statement, the kind Deligne's formalism is built to produce. *[P]:* relocates the count to a sheaf on the
parameter, where Deligne is **sharp** and `n<√q` is irrelevant.

**N5. The transfer isometry.** *New object:* an explicit linear `T: ℂ[μ_n] → ℂ[offsets]`, `q^{k+1}`-dimensional
codomain, with `‖domain sum‖ = ‖T(domain sum)‖` and `cond(T(·)) ≤ C`. *Conjecture (closed):* such a `T`
exists with conductor `≤ C` independent of `p,n`. *Why never existed:* "relocate the cancellation locus by an
explicit isometry" is a new *operation* — transference principles (Green–Tao) relocate **measures**, not the
**conductor** of an `ℓ`-adic family. *Feasible:* the Krawtchouk-weighted dual-code sum already realizes the
candidate `T`; only its conductor is uncomputed. *[P].*

### Cluster A3 — `2`-adic native objects

**N6. The `2`-adic period measure.** *New object:* the period along the dilation tower `b↦ζb`, viewed as a
`p`-adic measure `dμ_∞` on `ℤ_p` via Amice's transform. *Conjecture (closed):* `dμ_∞` has Iwasawa invariants
`μ=0, λ ≤ log_2 n`, so its Amice transform is bounded and `M(μ_n) ≤ C√(n log)`. *Why never existed:*
`Amice:3 / Iwasawa:3` files in-tree, all archimedean-adjacent; **no one has interpolated the period itself
into a `p`-adic measure** because the prize was always read archimedeanly. *Feasible:* the dilation tower is
already formalized as the L²-doubling recursion; Amice's transform of a coherent tower of values is a standard
construction. *[π]:* the bound lives in `ℚ_p`, where the archimedean obstruction `n<√q` has no meaning.

**N7. The `2`-adic Newton-polygon root census.** *New object:* the Newton polygon over `ℚ_2` of the pencil
polynomial `P_b(X)=Π(X−period)`, with slope multiplicities counting roots-of-unity coincidences by `2`-adic
valuation. *Conjecture (closed):* the NP has `≤ n/2` segments of slope `0`, capping the under-determined bad
count at `n/2 < budget`. *Why never existed:* Mann's theorem (the only vanishing-sum tool that works) is the
**archimedean** shadow; the `2`-adic NP of these specific cyclotomic pencils is uncomputed. *Feasible:* Newton
polygons are algorithmic; `Newton:107` files exist but **none** computes the NP **over `ℚ_2`** of the pencil
(checked). *[π]:* a `2`-adic count, sharper than Mann past the boundary precisely where the archimedean count = Johnson.

**N8. House–valuation product duality.** *New object:* a local–global formula `house(η_b)^{[K:ℚ]} = Π_v |η_b|_v^{−1}`
specialized to the cyclotomic integers `η_b ∈ ℤ[ζ_n]`. *Conjecture (closed):* the `2`-adic factor dominates the
product so strongly that `house(η_b) ≤ C√n`. *Why never existed:* the height-gate used the archimedean house and
a generic Mahler bound (KILLED); the **dual** read — bound the house *from the `2`-adic valuations* — was never
tried. *Feasible:* the valuations are Stickelberger-computable; the product formula is exact. *[π].*

**N9. `2`-adic Lehmer gap of the pencil.** *New object:* the Mahler measure `m_2(P_b)` over `ℂ_2`. *Conjecture
(closed):* `m_2(P_b) ≥ log 2` (a `2`-adic Lehmer bound), forcing the largest bad prime `≤ p` for `n` past 32.
*Why never existed:* Lehmer's problem is archimedean; a `2`-adic Lehmer gap for cyclotomic-coefficient polynomials
is a new question. *Feasible:* `2`-adic Mahler measure is a convergent integral; the coefficients are 0/1. *[π].*

### Cluster A4 — Rare-event / information objects

**N10. RS-structured chaining entropy.** *New object:* the metric-entropy integral `∫_0^∞ √(log N(ε)) dε` of
the offset process `u_0 ↦ 𝒮(u_0)` under the RS/dilation metric. *Conjecture (closed):* this integral is `o(log q)`
(strictly: `≤ C·log_2 n`), so generic chaining gives `E[sup] ≤ C√(n log n)` — `√log` **absorbed**. *Why never
existed:* `Talagrand:4, majorizing:2, chaining:56` files exist but **none computes the entropy of the
RS-structured index** (they use generic chaining = reproduces W4). The structured-entropy computation is the
missing piece. *Feasible:* the dilation tower gives an explicit `ε`-net hierarchy; counting it is combinatorial.
*[H]:* directly bounds the supremum by entropy, the one mechanism that absorbs rather than estimates the tail.

**N11. A deterministic large-deviation principle (dLDP).** *New object:* a rate function `I_det(x)` for
DETERMINISTIC pseudorandom families, keyed to `2`-adic lacunarity, governing `#{b: η_b ≥ x√n}`. *Conjecture
(closed):* `#{b: η_b ≥ x√n} ≤ m·e^{−I_det(x)·?}` with `I_det(x) ≥ x²/2`, so the max is `≤ √(2n log m)`. *Why
never existed:* LDPs are for **random** ensembles; a deterministic LDP that derives the rate from arithmetic
lacunarity (not from independence) is new — the campaign found the periods are "exchangeable white noise" but
never built the deterministic rate. *Feasible:* the moments `q E_r` already encode the rate via Legendre
transform. *[H].*

**N12. Algorithmic-incompressibility bound.** *New object:* the Kolmogorov complexity `K(b* | RS-structure)` of
the worst frequency. *Conjecture (closed):* `K(b*) ≤ log_2 n`, and any `b` with `η_b > √(2n log m)` would have
`K(b) ≥ log m` (incompressible) — contradiction, so the max is bounded. *Why never existed:* descriptive
complexity / incompressibility has never been applied to character-sum extrema. *Feasible:* the RS structure is
an explicit short program; the counting (incompressibility) argument is standard once the description length is
pinned. *[H].*

### Cluster A5 — Renormalization native to the `2`-power tower

**N13. A contractive phase-aware transfer operator.** *New object:* the operator `𝒯` on phase-functions of the
half-tower with `(𝒯f)(b) = f(b) + e^{iθ_b} f(ζb)`, retaining the **relative phase** `θ_b` the magnitude recursion
discards. *Conjecture (closed):* `spec(𝒯) < √2` in the RS-restricted sector. *Why never existed:* the magnitude
recursion `M(n)²≤2M(n/2)²` is **FALSE** (refuted in-tree) precisely because it drops `θ_b`; a phase-aware operator
has never been written. *Feasible:* `θ_b` is the exactly-measured alignment angle (cos=1 in-tree is the *trivial*
sector; the RS sector is open). *[Φ]:* the contraction lives in the phase the magnitude version threw away.

**N14. A `2`-adic wavelet (multiresolution) basis for `μ_{2^μ}`.** *New object:* a Haar-like orthonormal basis
adapted to the subgroup tower, in which the period has sparse coefficients. *Conjecture (closed):* the period has
`≤ log_2 n` nonzero wavelet coefficients, giving an `ℓ^1→ℓ^∞` bound `M ≤ √(n)·log_2 n`. *Why never existed:*
`2`-adic wavelet bases exist in abstract harmonic analysis but were never specialized to multiplicative subgroup
sums. *Feasible:* the tower is dyadic — the natural setting for a Haar basis. *[π]+[Φ].*

**N15. Quantum-dilogarithm / modular renormalization of the period generating function.** *New object:* the
`q`-deformed generating function `Φ_q(z) = Π (1 − z η_b)` and its quantum-dilogarithm functional equation under
`z ↦ z/q`. *Conjecture (closed):* the modular transformation has a fixed point pinning `M ≤ √(2n log m)`. *Why
never existed:* quantum dilogarithms appear in TQFT/cluster algebras, never for arithmetic period sums.
*Feasible:* the product is explicit; the `q`-difference equation is mechanical. *[Φ].*

### Cluster A6 — Operator / spectral new objects

**N16. The thin-subgroup noncommutative torus.** *New object:* the C\*-algebra `𝒜_{n,p}` generated by the dilation
`U` and translation `V` with `UV = ζ VU`, restricted to the `μ_n`-sector; `M(μ_n) = ‖V + V^{-1}‖` in a specific
representation. *Conjecture (closed):* `𝒜_{n,p}` is nuclear with a `K`-theoretic trace bounding `‖V+V^{-1}‖ ≤ C√(n log)`.
*Why never existed:* the noncommutative torus is studied for irrational rotation; the **thin arithmetic sector** is a
new object. *Feasible:* the relations are explicit finite-dimensional. *[Φ].*

**N17. The `2`-power-tower tridiagonalization.** *New object:* the Jacobi (tridiagonal) matrix obtained by applying
Lanczos to the dilation operator in the period basis — a genuinely `2`-power-adapted Terwilliger module. *Conjecture
(closed):* the Jacobi parameters `(a_k, b_k)` satisfy `b_k ≤ √2·b_{k-1}` with a defect, capping the top eigenvalue
`= M`. *Why never existed:* `Terwilliger:4` files exist but treat the **Hamming/Krawtchouk** algebra; the dilation-tower
tridiagonalization is new. *Feasible:* Lanczos is algorithmic. *[Φ].*

**N18. The phase-Gram positivity certificate.** *New object:* the circulant Gram matrix `G = (η_{a−b})_{a,b}` and a
**Schoenberg-type** positive-definite function `f` with `f(G) ⪰ 0` ⟺ `M ≤ bound`. *Conjecture (closed):* there is an
explicit completely-monotone `f` certifying `M ≤ √(2n log m)` that does **not** factor through Parseval. *Why never
existed:* Schoenberg positivity has never been applied to the period circulant. *Feasible:* `G` is an explicit
circulant; its eigenvalues are the `η_b` themselves — the certificate is a positivity LP over completely-monotone
`f`, finite-dimensional after truncation. *[Φ].*

### Cluster A7 — Combinatorial-geometric new objects

**N19. The cyclotomic phase polytope and its mixed phase-volume.** *New object:* the Newton polytope of the pencil
equipped with a NEW `phase-valuation` invariant `MV^Φ` (mixed volume with an oscillatory facet weight), counting
**under-determined** solutions with cancellation. *Conjecture (closed):* `MV^Φ ≤ n/2`, capping the under-det bad
count below budget. *Why never existed:* the fewnomial/Khovanskii bound (REFUTED in-tree) counts solutions
**without sign**; a phase-weighted mixed volume is new. *Feasible:* mixed volumes are computable; the phase weight
is the same `χ_2` as N1. *[Φ]+[P].*

**N20. Phased-Sidon set theory.** *New object:* a set `S` is `Φ`-Sidon if its representation function, **weighted by
the phase of the representation**, is bounded; `μ_n` is conjecturally `Φ`-Sidon of order `log m`. *Conjecture
(closed):* `μ_n` is `Φ`-Sidon with constant `≤ 2`, which by a phased-Plancherel gives `M ≤ √(2n log m)`. *Why never
existed:* Sidon/`B_h[g]` theory counts representations as **non-negative** multiplicities; a phase-weighted Sidon
property is new. *Feasible:* the unsigned `B_2` (= additive energy) is exactly known; phasing it is a refinement.
*[Φ].*

### Cluster A8 — Number-theoretic new objects

**N21. A deterministic Salem–Zygmund theorem.** *New object:* sufficient **arithmetic** conditions (keyed to
`2`-adic lacunarity gaps `≥ 2`) under which a *deterministic* exponential sum has random-flat sup `√(n log)` —
the classical SZ requires **random** signs. *Conjecture (closed):* `μ_n`'s discrete logarithms satisfy the
lacunarity condition, so the deterministic SZ bound applies: `M ≤ C√(n log m)`. *Why never existed:* Salem–Zygmund
is a probabilistic theorem; a deterministic version with an arithmetic hypothesis is new. *Feasible:* the dyadic
log-gaps are exactly `2`-power-spaced — the strongest possible lacunarity. *[Φ]+[H].*

**N22. A phase-concentration (Talagrand-for-arguments) inequality.** *New object:* a concentration inequality for
the **argument** `arg(partial sum)` (not the magnitude) as `b` varies, with a convex-distance functional on phase
space. *Conjecture (closed):* the phase has sub-Gaussian fluctuations with variance `≤ n`, so aligned partial sums
are exponentially rare, giving `M ≤ √(2n log m)`. *Why never existed:* concentration of measure is always for
magnitudes/Lipschitz functions; a phase/argument concentration is new. *Feasible:* the phase increments are explicit
`ζ`-powers. *[Φ]+[H].*

**N23. Discrete curvature of `μ_n ⊂ F_p`.** *New object:* a combinatorial "curvature" `κ(μ_n)` (a signed second
difference of the gap sequence) whose positivity forces cancellation, à la Bakry–Émery on graphs. *Conjecture
(closed):* `κ(μ_n) ≥ c > 0` uniformly, and `κ ≥ c ⟹ M ≤ √(n log)/√c` by a curvature-dimension exponential-sum
inequality. *Why never existed:* Bakry–Émery curvature is for diffusions/graphs; a curvature of a multiplicative
subgroup controlling its character sum is new. *Feasible:* the gap sequence is computable; the CD inequality side is
a fresh but elementary functional inequality. *[Φ].*

**N24. The defect-shifted Riemann Hypothesis for `μ_n`.** *New object:* a local `L`-factor `L_{μ_n}(s) = Π_b (1 − η_b p^{−s})^{-1}`
with a conjectured zero-free region. *Conjecture (closed):* all `η_b` satisfy `|η_b| ≤ 2√n + D(n)` with an **explicit
defect** `D(n) = C√(n log(n)/log? )` — a *shifted* RH (the graph is NOT Ramanujan, so the bound is `2√n` **plus** a
controlled defect, not the false exact Ramanujan). *Why never existed:* graph-RH/Ramanujan is binary (`≤2√n` or not);
a **defect-quantified** RH with a closed-form defect is new and is exactly what "near-Ramanujan-up-to-`√log`" needs.
*Feasible:* the `η_b` are real and explicit; the defect is what every probe measures (`C≈1.2–1.5`). *[Φ].*

**N25. A `2`-adic Sato–Tate law.** *New object:* the equidistribution measure of `{η_b/√n}` in the **`2`-adic**
topology (not the archimedean Sato–Tate, which is the wrong limit, ruled out). *Conjecture (closed):* the `η_b`
equidistribute w.r.t. an explicit `2`-adic measure `ν_2` whose support has archimedean radius `≤ √(2 log m)`, pinning
the sup. *Why never existed:* Sato–Tate is archimedean equidistribution; a `2`-adic vertical law is new. *Feasible:*
the periods lie in `ℤ[ζ_n]` with computable `2`-adic reductions. *[π].*

---

# PART B — 25 existing mathematics the campaign never touched

*Each: the area, **proof of absence** (grep count over `ArkLib/Data/CodingTheory`, `docs/kb`,
`scripts/probes`), why it is **relevant**, why it is **feasible**, the **closed conjecture**, and the
**non-collapse** tag. Counts are file-hit counts on 2026-06-15.*

**E1. Graphons / graph limits** *(absence: `graphon` = 0, `graph limit` = 0).* *Relevant:* `Cay(F_p, μ_n)` is a
growing graph family; its limit object carries `λ₂`. *Conjecture (closed):* the family converges to a graphon `W`
whose spectral measure has top non-trivial atom `≤ C√(log m / n)` (normalized), i.e. `M ≤ C√(n log m)`. *Feasible:*
the adjacency is explicit; the cut-norm limit is computable for circulant families. *[H]:* the graphon limit encodes
the **tail** of the spectral measure, not just its second moment.

**E2. Ihara zeta function of the Cayley graph** *(absence: `Ihara` = 1, incidental).* *Relevant:* the Ihara zeta's
poles are exactly the graph eigenvalues; graph-RH ⟺ Ramanujan. *Conjecture (closed):* the Ihara zeta `Z_{Cay}(u)`
satisfies a **shifted** RH — poles in `|u| ≥ p^{−1/2−δ(n)}` with explicit `δ(n)=Θ(log log m / log m)` — equivalent
to `M ≤ √(n) + defect`. *Feasible:* Bass's determinant formula makes `Z` an explicit polynomial in the adjacency.
*[Φ].*

**E3. Lovász `ϑ` function** *(absence: `Lovasz` = 0).* *Relevant:* `ϑ(Cay-complement)` sandwiches independence/clique
numbers and the eigenvalue. *Conjecture (closed):* there is a **combinatorial** (LP-rounding-free) feasible dual
`ϑ`-witness certifying `λ₂ ≤ √(n log m)` from the `2`-power orbit structure. *Feasible:* `ϑ` is an SDP with an
explicit circulant optimum for vertex-transitive graphs (the orbit reduction makes it small). *[Φ]:* the `ϑ` dual
witness is a phase assignment, not a second moment; (the general SDP route was touched, but **`ϑ` specifically and
its orbit-reduced dual was not** — `Lovasz`=0).

**E4. Crystalline / rigid cohomology** *(absence: `crystalline` = 0, `rigid cohomology` = 1, a single incidental lit-sweep mention — no probe or brick).* *Relevant:* `p`-adic
point-counting of the pencil via Monsky–Washnitzer gives the period as a unit-root. *Conjecture (closed):* the
unit-root `F`-crystal of the pencil has Newton slopes all `≥ 1/2` with multiplicity `≤ log_2 n`, bounding the
archimedean period. *Feasible:* Kedlaya's algorithm computes these crystals for explicit curves. *[π]:* a `p`-adic
cohomology, distinct from the étale/Weil route (which is vacuous at `n<√q`).

**E5. Munshi's `δ`-method / GL(3) circle method** *(absence: `Munshi` = 0, `delta-method` = 0, `DFI` = 0).* *Relevant:*
the under-determined (`s−k=1`) sum is a shifted convolution — Munshi's `δ`-method gives subconvex savings the additive
large sieve (touched, collapsed to Parseval) cannot. *Conjecture (closed):* the `δ`-method yields `|under-det sum| ≤
n^{1/2}·m^{−η}` for explicit `η>0`, i.e. strictly below the trivial. *Feasible:* the `δ`-method is a concrete identity
(Duke–Friedlander–Iwaniec / Munshi); applying it to the subgroup sum is mechanical. *[Φ]+[P]:* the `δ`-method
**separates** the oscillation by an auxiliary integration the large sieve averages over.

**E6. A-hypergeometric / GKZ systems** *(absence: `GKZ` = 0; `hypergeometric` = 10 but unrelated contexts — verified
no GKZ system of the pencil).* *Relevant:* the period is a solution of a GKZ holonomic system in the offset
parameters. *Conjecture (closed):* the holonomic rank is `≤ n` and the singular locus avoids the prize fiber, so the
period is bounded by the system's regular-singular monodromy `≤ C√(n log)`. *Feasible:* GKZ systems are algorithmic
(the `A`-matrix is the exponent set of the pencil). *[P]:* a statement about the parameter-family's `D`-module, sharp
where Deligne is.

**E7. Cohen–Lenstra / arithmetic statistics** *(absence: `Cohen-Lenstra` = 0, `arithmetic statistics` = 0).*
*Relevant:* the `p`-part of the class group of `ℚ(ζ_n)` governs the cyclotomic relations behind bad primes.
*Conjecture (closed):* the Cohen–Lenstra heuristic for `Cl(ℚ(ζ_{2^μ}))[p]` predicts `#{bad primes ≤ X} = o(X/√n)`,
so a generic prize prime is good with the bound. *Feasible:* the `2`-power cyclotomic class groups are tabulated;
the heuristic is a concrete density statement. *[π].*

**E8. Nilsequences / Host–Kra structure (as exact structure, not the inverse theorem)** *(absence: `nilsequence` = 0,
`Host-Kra` = 0; Gowers/GTZ were touched only as the no-go that the `μ_n` phase **collapses to linear**).* *Relevant:*
if the dual phase is an honest **1-step** (abelian) nilsequence, there is no higher-order obstruction to flatness.
*Conjecture (closed):* the `μ_n` phase has Host–Kra factor of step exactly 1, and the step-1 (Weyl) flatness gives
`M ≤ √(n log)`. *Feasible:* the gcd-collapse identity (in-tree) already shows the phase is linear — making it a
**theorem about the HK factor** is the new, feasible step. *[Φ].*

**E9. Singularity analysis (Flajolet–Sedgewick)** *(absence: `Flajolet` = 0, `singularity analysis` = 0).* *Relevant:*
the under-determined subset-sum count is the coefficient of a generating function; its growth is set by the dominant
singularity. *Conjecture (closed):* the GF `F(z) = Π_{x∈μ_n}(1+z e_p(x))` has dominant singularity on the
"Johnson side," giving `[z^{s}] ≤ budget` for `s` up to the floor radius. *Feasible:* the GF is explicit; transfer
theorems are mechanical. *[Φ]:* the singularity location is a phase-coherence statement (where the factors align),
not an energy.

**E10. Rough paths / signatures** *(absence: `rough-path` = 0, `signature` = 0 in this sense).* *Relevant:* the period
walk `b ↦ Σ_{x: log x ≤ b} e_p(x)` has a path signature whose shuffle-algebra norm controls the max. *Conjecture
(closed):* the truncated signature of depth `log_2 n` has norm `≤ √(n log m)`, and `M ≤ ‖signature‖`. *Feasible:*
signatures are explicit iterated sums; the shuffle identities are algebraic. *[H]:* the signature is a hierarchical
(multiscale) descriptor — an entropy-like compression of the whole path.

**E11. Pisot/Salem number dynamics** *(absence: `Pisot` = 0, `Salem number` = 0; only an unrelated "√2 house floor"
touched).* *Relevant:* the largest period root is an algebraic integer whose conjugate spread (Pisot/Salem dichotomy)
bounds the house. *Conjecture (closed):* the period polynomial is **not** Pisot (no single dominant root) — its roots
are Salem-balanced — and the Salem property forces `house ≤ √(2n log)`. *Feasible:* the dichotomy is decidable from the
explicit minimal polynomial. *[π]+[Φ].*

**E12. Three-gap (Steinhaus) theorem** *(absence: `three-gap` = 0, `three-distance` = 0).* *Relevant:* the discrete
logarithms of `μ_n` (an arithmetic progression mod `m`) have at most **three** gap lengths in `F_p` — strong rigidity.
*Conjecture (closed):* the 3-gap structure of `μ_n` forces a van-der-Corput cancellation `|Σ e_p(bx)| ≤ √(n log)` via
the bounded gap-complexity. *Feasible:* the three-gap theorem is elementary and exactly applicable to the cyclic
subgroup. *[Φ].*

**E13. Quasicrystals / cut-and-project / model sets** *(absence: `quasicrystal` = 0, `Penrose` = 0, `model set` = 1,
`cut-and-project` = 1, `diffraction` = 1 — all single incidental mentions, no probe or brick).* *Relevant:* `μ_n` is a model set (projection of a lattice in `ℤ[ζ_n]`); model sets have
**pure-point diffraction**. *Conjecture (closed):* the diffraction measure of `μ_n` has Bragg peaks of height `≤ C n`
and continuous background `≤ C√(n log)`, the latter being `M`. *Feasible:* the internal-space projection is explicit
(`ℚ(ζ_n)` embeddings). *[Φ]+[π]:* diffraction sees the **phase-coherent** (Bragg) vs **incoherent** parts separately —
exactly the worst-vs-average split.

**E14. Voronoi summation** *(absence: `Voronoi` = 0).* *Relevant:* Voronoi turns the under-determined sum into a dual
sum over a shorter range. *Conjecture (closed):* the Voronoi dual of `Σ_{x∈μ_n} e_p(bx)` is supported on `≤ √n` terms
with bounded weights, giving `M ≤ √(n log)` directly. *Feasible:* Voronoi formulae for `GL(1)/GL(2)` are explicit; the
subgroup structure gives the dual support. *[P].*

**E15. Minkowski `?`-function / continued-fraction renormalization** *(absence: `Minkowski question` = 0,
`continued fraction` = 0).* *Relevant:* the `2`-adic odometer on `μ_{2^μ}` has the `?`-function as an intertwiner;
its transfer (Gauss–Kuzmin–Wirsing) operator has a spectral gap. *Conjecture (closed):* the GKW-type transfer operator
of the dilation odometer has second eigenvalue `< 1/√2`, giving the contractive recursion the magnitude version lacked.
*Feasible:* transfer operators of self-maps of the dyadic odometer are explicit. *[Φ]+[π].*

**E16. Operads / higher category** *(absence: `operad` = 0, `higher categor` = 0).* *Relevant:* the over-/under-
determined strata compose like an operad (gluing witnesses); an operadic recursion could close the count. *Conjecture
(closed):* the incidence is the value of an explicit cyclic operad on `μ_n` whose generating-series satisfies a
fixed-point equation with solution `≤ budget` in the window. *Feasible:* the composition law is the explicit witness-
gluing already in `FarCosetExplosion`. *[P].* *(Flagged speculative: weakest relevance of the 25; included per the
"completely different math" mandate, honestly labeled.)*

**E17. Motivic integration** *(absence: `motivic` = 1, incidental).* *Relevant:* the bad-`γ` locus is a constructible
set; its **motivic volume** measures the count uniformly in `p`. *Conjecture (closed):* the motivic volume of the bad
locus is a polynomial in `𝕃` of degree `≤ k`, so `#bad ≤ C q^{k}/q^{s−k} ≤ budget` in the window. *Feasible:*
the locus is an explicit incidence variety; motivic volumes of such are computable (Denef–Loeser). *[P].*

**E18. Tropical geometry** *(absence: `tropical` = 2, incidental/unrelated).* *Relevant:* the tropicalization of the
pencil's solution variety has lattice points = the under-determined solutions. *Conjecture (closed):* the tropical
variety `Trop(V)` has `≤ n/2` lattice points in the relevant cell, capping the under-det count. *Feasible:* tropical
varieties of explicit polynomials are algorithmic (Newton-polytope subdivisions). *[P]:* a parameter-space count,
`p`-independent — but applied to the **under**-determined stratum (the p-dependent one), the tropical count is the
char-0 skeleton whose deviation is the open question, so it bounds **from the structured side**.

**E19. Berkovich analytic geometry** *(absence: `Berkovich` = 2, incidental).* *Relevant:* the Berkovich
analytification of the pencil over `ℚ_2` has a skeleton onto which the period retracts. *Conjecture (closed):* the
retraction to the skeleton is `1`-Lipschitz and the skeleton has diameter `≤ log_2 n`, bounding the `2`-adic (hence
archimedean, via N8) period. *Feasible:* Berkovich skeleta of curves are computable. *[π].*

**E20. Schur–Siegel–Smyth absolute trace** *(absence: `Schur-Siegel` = 3, low / docs-only).* *Relevant:* the absolute
trace of the totally-real period polynomial lower-bounds its largest root structure. *Conjecture (closed):* the
absolute trace of `P_b` is `≥ (2−ε)·deg`, which by an SSS-type inequality forces the largest root (= `M`) `≤ √(2n log)`.
*Feasible:* SSS auxiliary-polynomial / LP bounds are explicit and tabulated. *[Φ].*

**E21. High-dimensional expanders / Ramanujan complexes** *(absence: `Ramanujan complex` = 1,
`high-dimensional expander` = 1, `Garland` = 1 — all single incidental mentions; `superstrong` = 2 incidental; no probe/brick).* *Relevant:* the multiplicative dilation action builds
a `2`-power simplicial complex; a higher-order Cheeger/Garland bound controls `λ₂`. *Conjecture (closed):* the dilation
complex is a `λ`-HDX with `λ ≤ √(log m / n)`, giving `M ≤ √(n log m)` via the trickle-down theorem. *Feasible:*
Garland's method is a local-to-global spectral computation on explicit links. *[Φ].*

**E22. Linear forms in logarithms (Baker) / transcendence methods** *(absence: `Baker` low/unrelated,
`transcendence` = 0).* *Relevant:* a bad coincidence is a tiny linear form `A ≡ −gB mod q` in `ζ_n`-logarithms; Baker
gives an **effective lower bound** on its size. *Conjecture (closed):* the Baker bound forces `#{bad coincidences} ≤
n` for `n` past 32, closing the under-det count effectively. *Feasible:* Baker's theorem is effective and the forms
are explicit cyclotomic. *[π]:* a transcendence (archimedean+`p`-adic Baker) bound on relation sizes, orthogonal to
energy.

**E23. NIP / stability theory (VC dimension of the incidence family)** *(absence: `VC-dimension` = 0,
`stability theory` = 0; `NIP` substring = 10 but all false-positives inside ordinary words, no model-theory content;
Pila–Wilkie touched only the o-minimal 0-dim no-go).* *Relevant:* the family of bad-`γ` sets indexed
by direction is a set system; bounded VC dimension caps incidences (Sauer–Shelah). *Conjecture (closed):* the incidence
set system has VC dimension `≤ k+1`, so the max incidence over directions is `≤ C n^{k+1}/q^{s−k}` ≤ budget in the
window. *Feasible:* VC dimension of algebraic set systems of bounded degree is bounded (Milnor–Thom); the conjecture is
the explicit constant. *[P].*

**E24. Free probability (free independence w.r.t. the dilation trace)** *(absence: `free probability` = 2,
`free independence` = 1 — all incidental, tracing to one logged-REFUTED free-prob EVT sub-claim; **free independence
w.r.t. the dilation trace + the free-cumulant computation below were never done**).* *Relevant:* the periods under
the dilation trace may be **freely** (not classically) independent, giving a semicircle-type law. *Conjecture (closed):*
the free cumulants `κ_r` of the period family vanish for `r > 2` up to a defect `δ_r ≤ n^{−1}`, so the spectral
distribution is semicircular with radius `2√n + defect` — the defect-corrected near-Ramanujan. *Feasible:* free
cumulants are computable from the proven moments by the moment–cumulant (non-crossing-partition) formula. *[Φ]:* free
cumulants past 2 are a **higher-order** invariant invisible to the second moment — the conservation law applies only to
classical second moments.

**E25. Theta series / Siegel modular forms of the cyclotomic lattice** *(absence: `Siegel modular` = 1, `genus theory`
= 0 — incidental; ND touched only a scalar theta-transformation, not the lattice theta series).* *Relevant:* the short vectors of the
lattice `ℤ[ζ_n]` (with the trace form) are the vanishing-sum relations = the bad count; the lattice theta series counts
them. *Conjecture (closed):* the theta series `Θ_{ℤ[ζ_n]}(τ)` is a modular form whose `r`-th Fourier coefficient
(short-vector count at norm `r`) is `≤ budget` for `r` up to the floor radius. *Feasible:* cyclotomic lattices and their
theta series are explicit modular forms (Eichler / mass formula). *[π]:* the modularity gives the short-vector count a
**closed-form** growth, distinct from the additive-energy second moment.

---

## C. Falsification discipline (how to kill or keep each of the 50)

Each direction is **closed** in the required sense: it names an explicit object and conjectures a concrete inequality
about it — there is no hidden "and also solve [open problem X]." That makes every one **immediately attackable** by the
in-tree harness:

1. **Numeric pre-screen** (`scripts/probes/`, vectorized): compute the conjectured quantity at `n ∈ {16,32,64}`, multiple
   primes, and check the inequality holds with the claimed constant. A single clean violation → `Research/ProximityPrize/DISPROOF_LOG.md`, done.
2. **Collapse audit** (the non-collapse tag): verify the proposed proof genuinely consumes its `[Φ]/[P]/[π]/[H]`
   information and is not a disguised second moment. If the only working step is Cauchy–Schwarz/Parseval/energy, it
   collapses to Johnson and is refuted-by-meta-theorem — log it.
3. **Survivors → Lean**: any direction that passes (1) and (2) and admits a per-fixed-`n` proof gets an axiom-clean
   brick (the `[propext, Classical.choice, Quot.sound]` standard), with the asymptotic stated as a named `Prop`.

**Honest expectation.** This problem is the 25-year thin-subgroup BGK/Paley wall; the campaign has refuted ~120 routes
and run 50-conjecture sweeps with 0 survivors. The base rate says **most of these 50 will fall**, most likely at step (2)
— the conservation law is strong, and several of the new objects (N1's signed energy, E24's free cumulants, N13's
phase operator) may secretly re-encode the same second moment they claim to evade; that is precisely what the collapse
audit must check first. The wager of this manifesto is narrower and, I think, defensible: **of 50 directions in four
information regimes the campaign never entered, the prior that *all* collapse is lower than the prior that the campaign's
~120 domain-arithmetic routes collapse** — because, by the conservation law, the domain routes were *guaranteed* to
collapse, while these are at least not pre-refuted. The first direction that survives the collapse audit is the first
genuine crack in the wall. If all 50 fall, the precise *reasons* map the second boundary — the boundary of what
relocating the cancellation locus can buy — which is itself the result that tells the next campaign where (not) to look.

<sub>Exploration manifesto (bold-conjecture register; nothing here claimed proven). Absence counts are
`grep -ril <kw> ArkLib/Data/CodingTheory docs/kb scripts/probes` on 2026-06-15. Successor to
`deltastar-444-new-math-manifesto-2026-06-15.md`; grounded in the in-tree route-elimination meta-theorem,
the over-/under-determined stratum split (over-det = Johnson-locked, p-independent; under-det = p-dependent = the wall),
and the four-information-source conservation law.</sub>
