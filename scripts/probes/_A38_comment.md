### [sweep][A38] Window-interior q-dependence of true δ* — PARTIAL (de-confounded: q-INDEPENDENT interior)

**Goal (A38, merged 389-T02/389-T18).** The #389 hill-climb found adversarial words beating power-words ~2.3× above Johnson, but the *q-dependence of the true δ\** was left **confounded by time-boxed search**: the per-prime crossovers `{97:0.43, 113:0.28, 193:0.21, 257:0.31}` mixed (1) the genuine `eps_mca = (badGamma integer)/q` **const/q ledge** (a finite-q ARTIFACT, recedes uniformly, NOT δ\*-dependence) with (2) any genuine q-drift of the bad-γ **incidence integers** in the interior (which WOULD make δ\* q-dependent). 389-T18: `N_a = (#cosets)·n` is claimed q-independent in the interior, but the leading `O(1)` constant *could* shift the crossing a full grid step. A converged measurement was never run.

**What I ran.** `RS[F_q, μ_8, k=2]`, ρ=1/4 — fully EXACT (q² codewords) at every prime on a clean ladder `q ∈ {41,73,89,97,113,137,193,233}` (q≡1 mod 8). Per-(pair,γ) bad-γ count is exact (full codeword list; S recomputed per list member; NOT-joint checked exactly). I split the two confounded effects:
- **PART 1 — structural FLOOR (deterministic, no RNG):** max badGamma over a **q-INDEPENDENT** construction (all monomial pairs + codeword+monomial deviations) → fair cross-prime comparison = char-0 coset spectrum.
- **PART 2 — mod-q DEFECT hunt (randomized hill-climb, 400×14):** extra badGamma found only by a non-structured word = a search-found spurious mod-q coincidence; run on the 2 smallest primes.

**Result (decisive).** The deterministic floor is **exactly q-invariant** across all 8 primes. Full spectrum per agreement level m (δ=1−m/8):

```
m:      8     7     6     5     4     3      (m=4: δ=J=.5 ; m=3,4 in [J,cap))
δ:    .000  .125  .250  .375  .500  .625
all q: 1     1     1     8     9    40     <- identical at q=41,73,89,97,113,137,193,233
```

Every row CONSTANT — interior (m=4→9, m=3→40), the Johnson boundary, AND the sub-Johnson onset. So `eps_mca = (q-invariant int)/q` falls like const/q at every row, and the measured crossover δ_x(q) at fixed eps RISES with q (eps=.05: .25→.50 as q:41→233) **purely via the const/q ledge** — the integers never move. That is exactly the #389 confounded drift, now explained. PART 2: the randomized hill-climb couldn't even MATCH the floor (best 6–7 vs floor 8–9) on q=41,73 — the **monomial pair is the converged worst-word**; no systematic boundary mod-q defect found.

**Verdict — PARTIAL.** The true δ\* is **q-INDEPENDENT in the window interior to leading order**: the interior incidence integers are the char-0 coset spectrum and do not move with q; the #389 per-prime crossover variation was the finite-q const/q ledge ARTIFACT, NOT δ\*-dependence. 389-T18's worry that the `O(1)` constant shifts the crossing is NOT realized at the worst (monomial) direction for n=8 — the constant is exactly fixed across the ladder. Residual q-dependence is confined to a small, positive, non-growing `O(1)/q` mod-q defect (at most one `1/n` grid step at isolated primes, does not scale with q). **δ\* admits a clean q-independent closed form in the interior up to an `O(1)/q` correction** — consistent with the closed-form candidate `δ*=1−ρ−2/s*` being q-independent by construction.

**Artifacts.** `scripts/probes/sweep_A38_qdep.py` (+ saved run `scripts/probes/_A38_out.txt`), kb note `docs/kb/deltastar-sweep-A38-qdep-2026-06-14.md`.

**Honest gaps.** Toy primes only (41..233); does NOT reach prize q~2^128 — validates the SHAPE/q-invariance on real codes, not the prize-regime constant. n=8's interior is thin (2 rows); n=16's ρ=1/4 interior is entirely all-bad (=q) and q⁴ is feasible only at p=17, so the q-ladder test is genuinely run only at n=8 (n=16 = shape confirmation, as labeled). A richer multi-prime interior test at larger n needs a list-decoding-style exact counter (reuses the A17 enumerator) — a clean follow-up. The worst-over-pairs is a converged LOWER bound; a constant row is strong evidence of q-independence, not a proof. This does NOT touch the prize wall (B-form / Gauss-period house at growing n, prize q); it removes a confound.
