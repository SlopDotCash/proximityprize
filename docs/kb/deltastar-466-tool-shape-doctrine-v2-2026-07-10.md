# The tool-shape doctrine v2 — what the winning proof must look like, why it does not exist yet, and how it could (2026-07-10, Fable round G77–G80D)

Round products: `_G77RelationAnomalyFourierGauge.lean`, `_G78KMSpreadCircularity.lean`,
`_G79PPiAdicDigitClustering.lean` (landed as G79P), `_G80DDecouplingParallelCapCollapse.lean` —
all axiom-clean; DISPROOF_LOG entries `466-G77-*`, `466-G78-*`, `466-G79-*`, `466-G80D-*`.
This note consolidates what those four bricks jointly teach into a revised positive
specification for any future closure of CORE.

## 1. The exact shape any winning proof must have

CORE is `M(μ_n) ≤ C·√(n·log(p/n))` at `p ≈ n⁴`, `n = 2^30`, equivalently the DC-subtracted
Wick tower to depth `r ≈ ln q`. After G77 the off-BGK route list is EMPTY: every recorded
formulation is a gauge of one inequality. A winning proof must therefore supply, somewhere
inside itself, a certificate of one specific analytic fact — in any of its gauges:

> **(THE ATOM)** The coset magnitude field `{|η_b|}` decorrelates: equivalently, μ_n does not
> concentrate in any dilated arc beyond CLT scale; equivalently the DC-subtracted energy is
> Wick to log depth; equivalently the wraparound relation census is within Wick of its mean.

The K^r-tolerance calculation (G78, `km_per_step_loss_is_e`) upgrades the old tool-shape
principle: **constant-base exponential losses are FREE** (`M ≤ √(2eK)·√(n ln q)` absorbs any
`K^r`). The proof does NOT need to be tight; it needs to be non-circular. Both modern
constant-loss engines already convert the atom into the prize at tolerable loss:

- Kelley–Meka sifting: spreadness (= arc anti-concentration) ⟹ convolution flatness ⟹ moment
  bound, all at C^r loss (G78);
- Bourgain–Demeter-style bilinear steps: lag-decorrelation ⟹ decoupling gain ⟹ moment bound
  (G80D, `decoupling_defect_identity` — the gain is *identically* the decorrelation mass).

So the entire remaining difficulty is ONE certificate:

> **(MISSING INGREDIENT)** A NON-FOURIER proof that a geometric progression
> `{g^j mod p : j < n}` does not concentrate in arcs at scale finer than CLT, or that its
> period magnitude field decorrelates at multiplicative lag. Every Fourier-based certificate
> is circular at rank one with two-sided constants in [3.1, 6.9] (G78 probe).

## 2. Why it does not exist (the three walls, final form)

1. **Phase-blindness** (closed classes): any certificate factoring through |·|²/energy/counts
   sees the standardized cumulant scaling `g_r = O(1)` — the wrong side of the
   linear-vs-bounded-standardized dichotomy. All L², spectral, LP, replica, Banach-norm,
   moment-fence methods die here (pre-existing map).
2. **Loss-class** (NOW REFINED): the old reading "methods lose too much per step" is wrong in
   general — C^r-loss engines exist (KM, BD). What actually dies here is only the
   POLYNOMIAL-loss class (BGK/Burgess/Shkredov iterates, n^ε per step: exponent-floored,
   G73/di-Benedetto-closure). The wall is NOT strength.
3. **Certification circularity** (the live wall): every known hypothesis that feeds a
   constant-loss engine — spreadness, decorrelation, sub-Gaussian increments (chaining,
   G69/G70), transversality (OC-PIECEB) — is, for μ_n, exactly the conclusion in another
   gauge. The loop has no contraction anywhere (doubling: spectral radius 2; KM: two-sided
   rank-1 equivalence; decoupling: exact defect identity).

Additional exact separations (this round): the p-adic world is separated from the problem by
a hard depth-n gap — `v_π(η_b − n) = n` uniformly in b, first sensitive digit = coset label
only (G79) — so no valuation-theoretic functional can even SEE the archimedean max below
depth n, and the discriminant is already saturated by clustering (no hidden p-adic rigidity).

## 3. How it could exist — the surviving sources of non-Fourier decorrelation

Ranked by how seriously the campaign's no-go map constrains them:

1. **Galois/ideal transversality across embeddings** (the ON-BGK seam, OC-PIECEB residue):
   a multiplicity invariant forcing relations at distinct prime-ideal embeddings. Naive
   assembly capped; the quantitative boundary (height ceiling ~0.22·n/log n vs requirement
   ~0.25·n/log n) is within constants — the ONLY seam where the numbers are even close.
2. **A new metric for chaining**: sub-Gaussian increments under a non-Euclidean metric
   (Jacobi cocycle was the named candidate; the Euclidean one is BGK-tight, G69/G70). Must
   inject arithmetic input that is not |η|-data.
3. **Deterministic-orbit machinery from dynamics**: the ×g self-similarity converts arc
   concentration into AP concentration at all scales g^s — but mass balance is exact and
   variance-free (the corner obstruction). A survivor would need a SECOND, non-commuting
   symmetry (×2×3-style rigidity needs two independent generators; μ_n has one). If the
   deployed domain ever carries two multiplicatively independent smooth generators, BLMV-type
   measure rigidity becomes available — worth checking against the actual prize parameters.
4. **Construction-side (good-prime + anomaly exclusion)**: the resummed MGF envelope holds
   for positive-density primes (measured); worst-case needs excluding a lower-tail anomaly —
   prize-hard but the only route where the missing step is a TAIL statement, not a sup bound.

## 4. Bottom line

The problem is now provably down to a single non-Fourier decorrelation certificate; the
machine that converts that certificate into the prize is fully built, at tolerable loss, in
two independent ways (KM-shaped and decoupling-shaped). Nobody on Earth currently has a
non-Fourier handle on geometric-progression anti-concentration in the thin regime — that is
the precise sense in which the prize contains the Paley graph conjecture. Attack surface for
the next rounds: seam (1) quantitatively (the constants are close), and any literature
motion on non-Fourier orbit anti-concentration.

## 5. Addendum (same day): reconciliation with the §33 ladder normal form + the queued target

Dossier §33 (2026-07-07, supersedes §0/§6) states the open core in the ANALYTIC gauge: the
Jacobi-coefficient ladder `Σ_{s≠0}‖T(s)‖^{2r} = (q−1)·Σ_c ‖(J^{∗r})(c)‖²` with r=1 proven,
r=2 proven-modulo-textbook-Weil, **r=3 = the calibrated open core** (`TripleConvEnergyBound`,
C = 40 probe-safe, per-tuple Weil provably insufficient at β ∈ (4,6)), r ≈ ln q = the wall.
The two gauges are consistent: transversality (this note §3.1) is the ideal-theoretic face,
the r=3 rung the analytic face, of the same certificate. §33's live route (ii) —
**Hasse–Davenport exact angle relations along subgroup cosets of ℤ/m** — is flagged
"unexplored exact structure ON the ladder object" and is precisely an *exact-identity* (hence
potentially non-circular) input of the kind this doctrine calls for: HD product/lifting
relations impose closed-form multiplicative constraints on coset-averaged Jacobi angle sums,
i.e. on exactly the convolution powers the r=3 rung needs. **QUEUED as the next window's
primary swing:** read the `_R19…_R27` chain, extract the J-sequence definition, and test
whether the HD product relation evaluates (or usefully constrains) any coset-averaged slice of
`(J^{∗3})(c)` — probe first at n = 8/16 against exact Jacobi-sum tables, then formalize
whichever side (identity or refutation) survives.
