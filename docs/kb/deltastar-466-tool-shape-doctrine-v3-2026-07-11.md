# The tool-shape doctrine v3 — post-seam-closure ranking of the surviving sources (2026-07-11, Fable arc G86H–G88V)

Supersedes the RANKING section (§3) of
`deltastar-466-tool-shape-doctrine-v2-2026-07-10.md`; §1 (the atom and the K^r
tolerance) and §2 (the three walls) of v2 stand unchanged and are not repeated here.
Arc products: `_G86HadamardSupportSix.lean`, `_G87CoverageDivisibility.lean`,
`_G88VVanishingRankBound.lean`, probes `probe_466_g87v_census_rank.py` +
Norm-distribution probe; DISPROOF_LOG `466-G86H-*`, `466-G87V-*`, `466-G88V-*` (+ two
addenda). All axiom-clean; locked builds green.

## 1. What changed: source #1 (Galois/ideal transversality) is CLOSED

v2 ranked the transversality seam first, "the ONLY seam where the numbers are even
close". This arc finished it:

1. **Arithmetic, fully theorem-level.** Hadamard's determinant inequality (proven from
   scratch; absent from Mathlib), coverage ⟹ `p^s ∣ det` (elementary
   Vandermonde-annihilator, no Smith normal form), and the rank fence
   (`rank + coverage ≤ d`) close the three certificate faces of the G82/G83 half-height
   fence. The fence now consumes raw census matrices; the CRT forcing direction is capped
   at marginality *by theorem* for support-six full-rank families.
2. **Phenomenology, completely mapped and entirely height-driven.** At every accessible
   cell (complete censuses, n ∈ {16, 32}, 6 primes, all roots): coverage = φ(ord) exactly
   in the no-accident regime `p > 6^{φ(ord)}` and collapses to 1 in the accident regime
   (the probe's p-range brackets the gate `6^{φ(8)} = 1296` / `6^{φ(16)} ≈ 1.7·10⁶`,
   predicting the observed ord-8/16 cutoff on the nose); `rank_p = n − coverage` — the
   rank fence is SATURATED with equality everywhere; full ℚ-rank occurs exactly at
   primitive cells, always with coverage 1.
3. **No hidden anti-coincidence force.** `v_p(Norm) ≡ 1` looked like a 55σ-scale
   anomaly against the naive random model; the Norm-distribution probe shows max census
   `|Norm| < p²` at every accessible primitive cell — the rigidity is arithmetically
   FORCED by height, and the #407 height-gate no-go already proves the protection dies
   by n ≈ 128–256.

Consequence: what remains of r369 anti-coincidence (piece (b)) at n = 2^30 is bare
accident-statistics — the BGK atom itself in another gauge. The seam can no longer be
expected to SUPPLY a non-Fourier certificate; it merely re-expresses the need for one.

## 2. The current ranking

With #1 closed here and #3 (dynamics/measure rigidity) closed by the N3 procyclic kill,
the surviving sources for the missing non-Fourier certificate are:

1. **Chaining under a genuinely new metric** (v2's #2). The Euclidean metric is
   BGK-tight (G69/G70) and flat-Dudley is dead; a winner must inject arithmetic input
   that is not |η|-data (the Jacobi cocycle remains the only named candidate). Nothing
   in this arc touched it.
2. **Construction-side tail exclusion** (v2's #4). The resummed MGF envelope holds for
   positive-density primes (measured); the missing step is excluding a lower-tail
   anomaly — still the only route where the gap is a TAIL statement rather than a sup
   bound.
3. **The atom directly** — non-Fourier anti-concentration of geometric progressions in
   the thin regime, for which the two constant-loss engines (KM-shaped, decoupling-
   shaped) and the fully formal Fourier⟺arc interface (G80Y/G80Z) stand ready.

Everything else on the map is a gauge, a fence, or a closed seam. The height mechanism
identified in this arc is a genuinely useful *small-cell* rigidity tool (it explains all
finite-cell data the campaign has ever collected in this lane), but it is provably not a
prize lever.

## 3. Practical guidance for future rounds

- Do not re-attack the transversality seam expecting certificate output; new work there
  should only be consolidation or Mathlib-upstreaming (the Hadamard inequality and the
  multilinearity divisibility brick are upstream candidates).
- Finite-cell census data can no longer inform the asymptotic question in this lane:
  every observable at accessible cells is height-saturated, and height dies before the
  asymptotics begin. Probes should move to accident-statistics models (random-relation
  ensembles at prize shape) if they want signal.
- The binding open surface is unchanged and unique: the atom, reachable in principle
  through sources 1–2 above or head-on. CORE remains OPEN / ON-BGK.
