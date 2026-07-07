# #466 lane L3 — the D2 Rogers–Siegel DECISION: CONCENTRATION (the ∃-form sliver is dead)

**Date:** 2026-07-01 · **Issue:** #466 (dossier v3 §6 Tier-2, "D2 Rogers–Siegel decision") ·
**Status:** DECIDED — empirical, replicated at n = 16 (full ensemble) and n = 32 (sampled + all
structured primes). Verdict: **CONCENTRATION**, both tails thin, lower tail *thinner than the iid
Gumbel benchmark*. The "prize prime as rare large-deviation lower-tail anomaly" sliver does NOT
reopen. Gate brick: `Frontier/_D2LowerTailConcentrationGate.lean` (axiom-clean).

## 1. The question (from the dossier)

Dossier v3 §6 Tier-2: *"D2 Rogers–Siegel decision: concentration ⟹ final no-go brick; heavy
lower-tail ⟹ the 'prize prime as large-deviation anomaly' sliver genuinely reopens. Gated on a
pointwise prime-to-lattice coupling."* `_D2RogersSiegelVarianceGate.lean` had shown the
Rogers/Siegel random-lattice variance route transfers to primes ONLY through a pointwise coupling
(with a machine countermodel for the uncoupled transfer). The remaining decidable question was
purely empirical: over the ensemble of primes `p ≡ 1 (mod n)` in the dyadic window `[n⁴, 4n⁴]`,
how does `M(n,p) = max_{b≠0} |η_b|` distribute — and in particular, is the LOWER tail (unusually
small `M`, i.e. primes where the core inequality holds with unusual room) heavy or thin?

If some positive fraction of primes had `x = M/√(n log(p/n))` far below the median, the ∃-form of
the core ("SOME prime in the window is good") would be strictly easier than the ∀-form, and the
anomaly class would be a new lever. If `M` concentrates, the ∃-form gains nothing.

## 2. The probe

`scripts/probes/probe_466_rogers_siegel_tail.py` → `scripts/probes/_out_466_rogers_siegel_tail.txt`.

- **Exactness:** full coset scan per prime — `η_b` is constant on the `m = (p−1)/n` cosets of
  `μ_n` and real (`−1 ∈ μ_n`), so scanning one exact n-term cosine sum per coset rep enumerates
  every distinct `|η_b|`; the argmax is exact. Per-prime Parseval check
  `Σ_reps η² = p − n` asserted to 1e-6 relative (all passed).
- **Ensembles:** n = 16: ALL 2038 primes `p ≡ 1 mod 16` in `(16⁴, 4·16⁴]`. n = 32: ~2100 evenly
  sampled of the 13319 primes in `(32⁴, 4·32⁴]`, PLUS all 123 structured primes
  (generalized-Fermat `p = b^{2^s}+1` or `v₂(p−1) ≥ 12`) forced in.
- **Benchmark:** iid model = max of `m` iid real `N(0, σ²)` values, `σ² = (p−n)/m ≈ n`
  (Parseval); Gumbel location/scale with `N = 2m`; predicts `x ≈ √2` with `O(1/log m)`
  Gumbel fluctuations and a doubly-exponentially thin lower tail
  (`P(Gumbel < −1) = e^{−e} = 0.066`, `P(< −2) = 6.2·10⁻⁴`).
- Regime discipline: `μ_n` proper (`m ≥ n³`), `p ≥ n⁴`, GF primes flagged, stats reported with
  and without them.

## 3. The data

| | n = 16 (full, N = 2038) | n = 32 (sampled, N ≈ 2200) |
|---|---|---|
| mean x | 1.1493 | 1.2446 |
| std x | 0.0193 | 0.0449 (Gumbel-predicted 0.0784 — strictly tighter) |
| min … max x | 1.104 … 1.218 | 1.131 … 1.394 |
| P(x < 1.1) | **0.000** | **0.000** |
| P(x < 1.0), P(x < 0.9) | 0, 0 | 0, 0 |
| Gumbel-z: mean, std | −1.86, **0.33** (benchmark: +0.58, 1.28) | (completed 2026-07-02: see _out_466_rogers_siegel_tail.txt) |

Key facts (n = 16, full ensemble — no sampling caveat):

1. **Total band width 0.11.** Every one of 2038 primes has `x ∈ [1.104, 1.218]`. The best prime
   in the entire window beats the median (1.147) by 3.7%; nothing is within a factor even 1.05
   below the median. `P(x < 0.85·median) = 0` exactly.
2. **The lower tail is thinner than iid.** Standardized against the Gumbel benchmark the whole
   ensemble sits ≈1.9 scale units BELOW the iid prediction with std 0.33 vs Gumbel's 1.28: the
   true max is *more concentrated and smaller* than the iid Gaussian model — exactly the strict
   char-0 sub-Gaussianity direction (`bessel_strictly_below_exp` in
   `_D2LargeDeviationRateFunction.lean`), now visible at the ensemble level.
3. **No anomaly class.** The 15 smallest-x primes have unremarkable `v₂(p−1) ∈ {4,…,9}`, no GF
   structure, mixed cofactor smoothness (`lpf(m) ∈ {2,…,43}`); mean x is flat in `v₂` (1.139–1.155
   across all levels); the 16 GF primes in the window sit INSIDE the bulk (x 1.12–1.20) — GF
   resonance, per prior rounds a *moment/upper-tail* phenomenon, does not produce small-M primes
   either.
4. **The upper tail is also thin** (max x = 1.218 ≪ any Weil-type scale), consistent with the
   dossier's `C ∈ [1.07, 1.49]` wall-constant record and `M/√(n log m)` decreasing in n.

## 4. The decision and its consequence

**CONCENTRATION.** Both tails are thin; the variance is tiny and (per the cross-n comparison in
the probe output) consistent with the Gumbel `1/√(log m · log(p/n))` shrink — no heavy-tail
component at either n. Therefore:

- **The ∃-form gains nothing over the ∀-form.** Any "choose a rare good prize prime" strategy can
  improve the constant `C` in `M ≤ C√(n log(p/n))` by at most the measured band ratio
  (`< 1.11` at n = 16) — never by an order, never below the floor `x ≈ 1.10`. Formalized as the
  consumer chain in `Frontier/_D2LowerTailConcentrationGate.lean`:
  `LowerTailConcentrationFloor` (the NAMED EMPIRICAL Prop) ⟹ `no_anomalous_prime_of_floor` +
  `exists_form_within_band_of_forall`; `not_floor_iff_anomalous_witness` records that the ∃-lever
  is *exactly* the negation of the floor — measured false.
- **The D2 sliver is closed as a no-go** (empirical tier, honest label): with the coupling gate
  (`_D2RogersSiegelVarianceGate.lean`) blocking the theoretical transfer and this probe deciding
  the empirical distribution against heaviness, neither direction of the Rogers–Siegel avenue has
  a live opening. Remove D2 from the Tier-2 "decisive probes not yet run" list; record verdict.
- **What this does NOT say:** nothing here touches the ∀-form core (the wall is untouched); the
  scanned windows are n ∈ {16, 32}, β = 4 — the concentration at n = 2³⁰ is an extrapolation,
  and (dossier §10) numerics provably cannot decide the core itself. The no-go is about the
  *shape of the ensemble*, i.e. about the ∃-vs-∀ REDUCTION, which is exactly what the sliver
  proposed to exploit.

## 5. Files

- probe: `scripts/probes/probe_466_rogers_siegel_tail.py`
- output: `scripts/probes/_out_466_rogers_siegel_tail.txt`
- gate brick (axiom-clean, compiled via `pg-iterate`): 
  `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_D2LowerTailConcentrationGate.lean`
- prior gates it composes with: `_D2RogersSiegelVarianceGate.lean` (coupling),
  `_D2LargeDeviationRateFunction.lean` (rate function / floor identity).


**n=32 completion addendum (2026-07-02).** The full n=32 scan (2103 sampled + 123 structured of 13319 window primes, protected-image rerun after two taskkill collisions) confirms concentration: median x = 1.2402, std 0.0449 vs Gumbel-predicted 0.0784; P(x<1.1) = 0 exactly; zero primes below 0.85*median (1.054); mean x flat in v2(p-1) = 5..17 (1.224-1.256); the cross-n variance SHRINKS faster than the iid benchmark. The DISPROOF entry [466-r4-d2-lowertail-concentration]'s n=32 claim is now fully artifact-backed.
