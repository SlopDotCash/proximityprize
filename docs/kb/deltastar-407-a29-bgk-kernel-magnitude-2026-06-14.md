# A29 — BGK kernel M = |μ_n ∩ −(1+μ_n)| magnitude probe + Mersenne–Fermat structure

2026-06-14. Actionable A29 (merged 232-T03). Status: **PARTIAL** (structure re-confirmed +
one assumed correlation corrected; the smallest BGK cell is shown CLEAN at prize scale, so it
does NOT carry the open wall). Honesty contract: no closure claimed.

## Object

The first genuinely-open *interior* BGK cell of the proximity-gap wall is the zero-sum
3-subset count of the dyadic subgroup μ_n = order-n=2^k multiplicative subgroup of F_p:

    M(p,n) = #{ u ∈ μ_n : −(1+u) ∈ μ_n } = #{ u ∈ μ_n : ∃ w ∈ μ_n, 1+u+w = 0 }.

By dilation u → g·u (g ∈ μ_n), the number of *ordered* zero-sum triples (x,y,z) ∈ μ_n³ with
x+y+z=0 equals |μ_n|·M = n·M. BGK predicts M ≪ n^{1/2+o(1)}.

Probes (all under `scripts/probes/`, pure arithmetic + sympy for big-int):
- `sweep_A29_bgk_kernel.py`       — prize-shaped large primes + parity/Fermat/6| laws + homogeneity.
- `sweep_A29_bgk_kernel_anomaly.py` — dense small-p scan: WHERE is M>0; u=1 reachability table.
- `sweep_A29_bgk_kernel_spike.py`  — pin the generic spike (p=97,n=32) + magnitude-vs-Fermat census.

## Re-confirmed proven structure (232-T03 / Rosetta C013)

1. **M = 0 in char 0.** Complex μ_{2^k} (k=2..7) has no zero-sum 3-subset. Confirmed (part 1 [0]).
2. **Parity law M odd ⟺ p | 2^n−1.** HOLDS on every sampled prime, large and small (parts 1,2).
   (The u=1 fixed point of the conjugation involution on the solution set is present iff p|2^n−1.)
3. **6 | M generically** via S₃ on the unordered triple {x,y,z}. HOLDS for all M>0 *except* the
   small-p saturation cases where 1 itself sits in a triple (n=4 p=5 M=3; n=8 p=17 M=3;
   n=16 p=257 M=3; n=32 p=65537 M=3 — the residual-3 = the u=1 orbit, not S₃-free).
4. **Homogeneity n·M = #ordered zero-sum triples.** Verified EXACTLY incl. on an M>0 witness
   (p=97,n=32: n·M=384, #ordered=384, all 64 unordered triples genuine, 6·64=384, 0 degenerate).
5. **u=1 obstruction ⟺ p | F_0···F_{k−1}** (Fermat numbers, 2^n−1 = ∏_{j<k} F_j). Reachability
   table computed: at n=2^k the active (j,q) pairs (prime factors q of F_j with 2^k | q−1) are
   non-empty for k≤7 (e.g. n=32: {(3,257),(4,65537)}), so the obstruction is reachable at small n.

## NEW result 1 — the smallest BGK cell is CLEAN at prize scale (the wall is NOT here)

Across **all** prize-SHAPED thin primes (n ≪ p^{1/4}, a = log_n p ≥ 6..12, p up to ~7·10¹⁰),
**M(p,n) = 0** for n=8,16,32,64 — every single prime. Dense small-p scans locate M>0 ONLY in the
THICK tail:

| n  | #primes scanned | #(M>0) | max M | largest p with M>0 | p^{1/4}/n at onset |
|----|-----------------|--------|-------|--------------------|--------------------|
| 4  | 141 502         | 1      | 3     | 5                  | 0.37               |
| 8  | 70 695          | 1      | 3     | 17                 | 0.25               |
| 16 | 35 343          | 2      | 15    | 257                | 0.25               |
| 32 | 17 662          | 6      | 12    | 65 537             | 0.50               |

Every M>0 witness has **p^{1/4}/n ≤ 0.5**, i.e. n ≳ p^{1/4} — the THICK regime. The prize regime
is the opposite (a ∈ [25,40] ⟹ p^{1/4}/n = n^{a/4−1} ≫ 1). **The t=1,a=3 cell carries no wall at
prize scale.** This localizes the open BGK core *away* from the smallest cell: the genuinely open
quantity is the period sum B(μ_n) = max_b|η_b| (the B-form) / the deep moments E_r (energy-form),
NOT the 3-subset count. (Consistent with M = (1/p)·[lowest piece] of the moment hierarchy being
governed by the same η-flatness but trivially clean when there is no char-p anomaly.)

## NEW result 2 — Fermat structure governs PARITY, not MAGNITUDE (corrects the A29 hypothesis)

A29 asked to "correlate M-spikes with Fermat factorizations." The data **refutes** a magnitude
correlation while confirming the parity one. Max-M-by-class census (over all M>0 primes ≤ cap):

| n  | max M (all) | max M (p\|2^n−1, "Fermat") | max M (generic) | who wins |
|----|-------------|----------------------------|-----------------|----------|
| 4  | 3           | 3                          | 0               | Fermat   |
| 8  | 3           | 3                          | 0               | Fermat   |
| 16 | 15          | 15                         | 0               | Fermat   |
| 32 | 12          | 9                          | **12**          | generic  |
| 64 | 18          | 15                         | **18**          | generic  |

For n ≤ 16 the only M>0 primes happen to BE the Fermat primes (tiny p), so "Fermat wins" is an
artifact of there being nothing else. From n=32 up, the **largest M sits at a GENERIC prime**:
n=32 worst is M=12 at **p=97** (which does NOT divide 2^n−1), beating the Fermat primes 257 (M=9)
and 65537 (M=3); n=64 worst is M=18 at a generic prime vs 15 at the Fermat side. At p=97,n=32 the
element 1 is NOT in any zero-sum triple (−2 ∉ μ_n), so the spike is entirely the generic
(non-u=1) zero-sum-triple count. **Verdict: the Mersenne–Fermat divisibility fixes only the
parity of M and the existence of the single u=1 triple; it does not control the size of M.** The
n=16,p=17,M=15 "spike" is a *saturation* (M ≈ n, the whole subgroup) of a degenerate tiny field,
not a structured BGK spike.

## Honest remaining gap

- M>0 still **unbounded above by √n in the thick regime** (M/√n up to 3.75 at n=16,p=17), but that
  regime is outside the prize and is the saturation/anomaly tail, not the prize wall.
- The probe does NOT prove M=0 at prize scale for ALL primes — it is exhaustive over the sampled
  primes only. Proving "M(p,n)=0 whenever n ≪ p^{1/4}" rigorously would be a clean Lean target
  (it is essentially: a thin dyadic subgroup has no zero-sum 3-subset; the char-0 vanishing
  transfers as long as no Hasse–Weil anomaly fires, i.e. p > some poly(n) threshold). That would
  formally retire the t=1,a=3 cell. NOT attempted here — flagged as the natural follow-up.
- The open wall is unchanged and lives at the higher BGK cells / the period sum B(μ_n), consistent
  with the rest of the campaign. A29 contributes a *localization*: the smallest interior cell is
  not where the difficulty is.

## Cross-refs
- Mersenne–Fermat Rosetta: `AdditiveEnergyFermat.one_mem_bgk_iff_exists_fermat_dvd`,
  `fermat_dvd_unique` (in-tree); memory `arklib-407-analogies-energy-curve-gaussian` (C013).
- Energy/period transport: `EnergyCharacterTransport`, `EnergyDilationReduction.addEnergy_eq_card_mul_incidence`.
- Prior BGK probes: `probe_bgk_M.py`, `probe_bgk_tower.py`, `probe_prize_bgk_trend.py` (this A29
  work supersedes them with the prize-scale magnitude + Fermat-vs-magnitude separation).
