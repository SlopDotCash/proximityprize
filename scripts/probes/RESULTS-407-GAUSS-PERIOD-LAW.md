# #407 — The Gauss-period law for the prize floor (independent re-derivation + the sharp residual)

Decisive session findings (probe `probe_moment_growth_law_407.py` + `/tmp/probe_coset.py`,
independent from-scratch code). These **re-confirm** the campaign's open-core characterization and
**sharpen** it to an essentially exact law, with a quantitative no-go for the only elementary method.

## 1. The structural reduction (now a proven Lean theorem)

`S(b) = Σ_{x∈μ_n} e_p(bx)` is **constant on multiplicative cosets** `b·μ_n` (reindex `x ↦ ux`,
`u∈μ_n`). Hence it takes at most `m = (p−1)/n` distinct nonzero-frequency values — the **Gauss
periods** of the order-`n` subgroup (= eigenvalues of the generalized Paley graph `Cay(F_p, μ_n)`).
- **Verified** (`probe_coset.py`): every value of `S` occurs with multiplicity an exact multiple of
  `n` (8; 16/32; 32/64; 64/128 — the coset size, doubled on the rare period collisions).
- **Formalized, axiom-clean**: `ArkLib/.../ProximityGap/GaussPeriodCosetReduction.lean`
  (`eta_mul_invariant`: `x∈G ⟹ η_{b·x}=η_b`). This is *why* the law's log is `log((p−1)/n)`, not
  `log p`: the worst case is a max over `m=(p−1)/n` periods, not `p` frequencies.

## 2. The sharp law (constant ≈ 1)

`B(μ_n) := max_{b≠0}|S(b)| = (1+o(1))·√(n·log₂((p−1)/n))`. Measured `B/√(n·log₂(p/n))`:

| n | 8 | 16 | 32 | 64 | 128 |
|---|---|---|---|---|---|
| ratio | 0.973 | 1.065 | 1.025 | 1.006 | 1.036 |

Mechanism: `m` near-Gaussian (variance-`n`, Parseval `avg|S|²=n`) periods ⟹ extreme value
`√(n·log m)`. This sharpens `ShawGapLaw`/`WorstCaseIncompleteSumBound` to **constant 1** and pins the
correct argument of the log to `m=(p−1)/n`.

## 3. The deep-moment threshold law, re-confirmed from scratch

`E_r(μ_n) = #{Σx=Σy} = (1/p)Σ_b|S(b)|^{2r}`. Normalized `E_r/(r!·n^r)` matches the char-0 Gaussian
value `(2r−1)‼/r!` **exactly for `r ≤ r_max = 2·log_n p − 3`** and inflates beyond. At `p~n^3`
(`r_max=3`): `E_2,E_3` clean, `E_{≥4}` inflate — precisely the predicted cutoff. So the char-0 energy
bound `E_r ≤ (2r−1)‼·n^r` (Lam–Leung) transfers to `F_p` only up to `r_max ≈ 2 log_n p`, far below the
moment-optimal depth `r ≈ ln q`. (Matches `CharSumMomentDeepWall.lean` §; independent confirmation.)

## 4. The moment-arrow NO-GO (quantitative)

The only elementary handle is the arrow `B ≤ min_r (p·E_r)^{1/2r}` (`max_le_moment`, proven). With the
**true F_p moments** it is provably lossy: its best bound is stuck at the **trivial value ≈ n**, and the
overshoot **diverges** with n:

| n | 8 | 16 | 32 | 64 | 128 |
|---|---|---|---|---|---|
| `arrow_min / trueB` | 1.20 | 1.33 | 1.75 | 2.30 | 2.92 |

So no fixed-depth (or optimized-depth) moment computation reaches `√(n·log(p/n))`. The deep moments
inflate (heavy tail; MGF diverges) faster than the max grows — the max is governed by the bulk
hypocycloid, the moments by the rare tail. The methods diverge exactly here.

## 5. The residual, named precisely (NOT closed; honesty contract)

The prize floor ⟺ **growing-n sup-norm of the Gauss periods of μ_{2^a}** = the generalized
Paley-graph eigenvalue. `B ≤ 2√n ⟺ Ramanujan` (Paley Graph Conjecture, open). Fixed-n is solved
(Kowalski–Untrau hypocycloid, P1/P4); the growing-n quantitative tail (P2, Wasserstein) and the
norm/transfer (P3, Myerson/Habegger) are the open frontier. No method in the literature closes it at
`n=2^32 < p^{1/4}`; this session's no-go shows the elementary route cannot. **Nothing fabricated.**

References P1–P5: `PAPERS_NEEDED.md` §2026-06-14 (#407).

## 6. The house constant is q-INDEPENDENT deep-sparse (v2-dependence refuted)

`probe_house_constant_uniformity_407.py` + `probe_house_2adic_dependence_407.py`:
- A bold conjecture "C=B/√(n·ln m) is uniform ≤ √2" is **refuted** by the Fermat prime `p=65537`
  (`C=2.07` at n=64) — but that is the **near-threshold #400 trap** (`p/n^2.5=2.0`, `m` a pure power
  of 2). At n=16 the same prime is deep (`p/n^2.5=64`) and gives only `C=1.199`.
- Binning `C` by `v2(m)=v2(p−1)−a` within deep-sparse bands shows **no v2-law**: worst-case `C` lands
  at `v2(m)=0` (odd `m`) as often as at high `v2(m)`; median flat in `v2(m)`. The driver of large `C`
  is **shallowness `p/n^2.5`** (HBK density), not 2-adic structure.
- **Conclusion:** for prize-valid (non-Fermat) primes deep in the sparse regime, the house constant
  is **uniform / q-independent** (~1.16–1.33), matching the prize-diagonal plateau `C²≈1.75`
  (`DISPROOF_LOG` entry (1)). This *supports* a universal-constant closed-form `δ*` (no arithmetic
  correction), but the universal constant is the wall-gated value — unprovable here.

## 7. CORRECTIONS + new results from the 9-agent feasible-grind workflow (2026-06-14)

A multi-agent sweep (2 independent replicates per question, cross-validated to machine precision)
**revises §6** and adds decisive findings. All numbers are from real probe runs (scripts/probes/_wf_*.py).

- **§6 "flat q-independent plateau 1.16–1.33" is REVISED.** The house constant `C=B/√(n·ln m)` is NOT
  flat: it climbs with n (β=4: 1.058→1.171→1.240→1.332 for n=8..64) and is **β-dependent**
  (decreases with β under the `ln(q/n)` normalization; flattens under `ln(q)`). One exact point
  C=1.487 > √2 (n=64,β=4). The data cannot separate "finite β-dependent limit ~1.4–1.65" from "slow
  unbounded log-growth" — that gap IS the open growing-n Paley-eigenvalue wall. **Sharp form:
  `B ≲ C·√(n·ln q)`, C≈1.0–1.1 typical, log-argument `ln q` (not `ln(q/n)`).**
- **E_r random-likeness SETTLED YES** (do not re-litigate): off-mean excess `E_r − n^{2r}/p ≤ C^r r! n^r`,
  C≈1–1.6 bounded in both n and r, c_r *decreasing* in r (no deep-moment fat tail). The swarm
  E_3-spike debate = structured-prime resonance, not growing C. BUT the moment arrow saturates at the
  trivial value n at constant index (arrow/trueB diverges 2.1→11.4) — random-likeness is necessary,
  not sufficient; the route still needs max|S(b)| directly (the wall).
- **FLOOR BROKEN (Q3, confidence 8): the monomial ladder is NOT list-maximal.** Nodal Laurent words
  `x^{-1}+x^b` beat `N_fib` ABOVE Johnson — 7>3 (n8,t3), 35>7 (n16,t3), 115>28 (n16 k3 t4) — verified
  across ≥3 sparse primes and by independent brute-force line enumeration; the beaters are genuine
  combinatorial designs (8 distinct pairwise intersections, not a pencil). **A δ* closed form keyed to
  `N_fib` (ladder) alone is REFUTED; the floor is `max(N_fib, L_nodal(x^{-1}+x^b))`,** nodal winning at
  the deep end (near capacity), ladder winning near Johnson. Methodology lesson: random hill-climb /
  base+corruption search systematically UNDER-find the beaters (false negatives) — only
  ladder-neighborhood perturbation search found them; trust prior "ladder holds" reads only if they
  used neighborhood search. Open residual = whether the beat ratio (5/3, 9/7, 115/28) is O(1) or grows
  with n (→ the asymptotic equidistribution/deep-moment wall).
- **δ* ansatz validated up-to-Johnson (Q4):** the bad-γ incidence integers are q-invariant up to
  Johnson (count=9 at δ=0.5 across q=41..233 ⟹ eps_mca=const/q→0), the measured crossover rises toward
  the closed-form δ* as q grows, 0 of 25/19 cases refute it. Validated as the right ANSATZ + curve
  shape + window placement; the deep band (count 40→55 above Johnson) is the open core.

## 8. ADDITIVE-COMBINATORICS attack on the p-defect count (2026-06-13) — descent BROKEN, quantified

Technique = additive combinatorics specific to `2^μ`-th roots (Hanson–Petridis, Lam–Leung,
antipodal/tower structure). Probes: `probe_tower_descent_pdefect_407.py`,
`probe_char0_energy_check_407.py`, `probe_true_defect_onset_407.py`,
`probe_defect_onset_threshold_407.py`, `probe_descent_mechanism_407.py`,
`probe_face3_worstcase_407.py`, `probe_resonant_spike_vs_B_407.py`. All exact (brute / FFT over `Z_q`).

**(a) Baseline CORRECTED.** The char-0 energy is `E_r^C(μ_n) < (2r-1)!!·n^r` for finite n; the
Lam–Leung formula is the **asymptotic leading term** (an upper bound), exact only as n→∞:
measured `E_2^C/n²` rises 1.5→2.25→2.625→2.81→2.91 → `(2·2−1)!!=3`; `E_3^C/n³→15`, `E_4→105`.
The true defect is `D_r := E_r^{F_q}(μ_n) − E_r^C(μ_n) ≥ 0` (every C-solution is a mod-q solution;
sign confirmed). Using `(2r-1)!!n^r` as baseline gives spuriously NEGATIVE "defects" — a real bug
in any probe that does (the in-tree `GaussianEnergyBound`/`GaussPeriodMomentBound` use the asymptotic
form as an UPPER bound, which is correct for that direction; only as a baseline-for-subtraction is it wrong).

**(b) Defects are ARITHMETIC/RESONANT, not generic.** With (n,r) fixed and q varied, `D_r=0` for the
MAJORITY of primes and nonzero only at sporadic resonant q (a defect needs `q | N(α)` for a specific
small `α` in the relation lattice). E.g. n=16,r=3: D_3>0 at p∈{257,7457,…}, =0 at all other scanned
primes. Confirms the "p-defect onset" picture; the count is a divisibility (lattice) statistic.

**(c) THE DESCENT IS BROKEN — decisive, machine-verified (`probe_descent_mechanism_407.py`).**
Split a defect `α = Σ±g^{x_i}` by exponent parity: even block `A∈μ_{n/2}`, odd block `g·B`, `B∈μ_{n/2}`,
so `A + g·B ≡ 0 (mod q)`. In char 0 (deg-2 tower ext, basis {1,g}) this forces `A=0 ∧ B=0` separately
⟹ clean descent to two `μ_{n/2}` relations (the Lam–Leung mechanism). Classifying EVERY actual defect:
the fraction that are **cross-parity "leaks"** (both A and B nonzero in C, joined only by `A≡−gB mod q`)
is **96–100%**:

| (n,r) | char0 | defects | LEAK% (undescendable) | DESC% |
|---|---|---|---|---|
| (8,4) | 190120 | 22400 | 100.0 | 0.0 |
| (16,3) | 50560 | 59280 | 100.0 | 0.0 |
| (16,4) | 4649680 | 15.5M | 100.0 | 0.0 |
| (32,3) | 446720 | 852480 | 99.3 | 0.7 |
| (64,3) | 3750400 | 58.1M | 95.8 | 4.2 |

Mechanism, exactly: the char-0 vanishing (Lam–Leung antipodal pairing) is **block-diagonal** in the
parity split; the char-p defects are **off-diagonal** (created precisely by the parity-mixing the
descent discards). A descent / self-improvement argument can only see the block-diagonal part, which
carries 0–4% of the mass. Directly confirmed: at fixed q, `D_r(μ_n)>0` while `D_r(μ_{n/2})=0`
(ratios 2880/0, 57600/0, 1128960/0) — the top-level defects have NO shadow in the subtower. **This is
a sharper no-go than DISPROOF_LOG O14′ (descent "exact hence circular"): it gives the mechanism and a
quantitative 96–100% leak rate.** Slice-rank/Croot–Lev–Pach already a machine-checked dead end
(DISPROOF_LOG O22: needs additive tensor structure a multiplicative subgroup lacks).

**(d) The per-r face-3 floor `D_r ≤ n^{2r}/q` is FALSE worst-case at small r** (honest, important).
Scanning all primes in a band, `max_p D_r/(n^{2r}/q)` = 1.19 (n16r3), 1.61 (n16r4), **34.5** (n32r3,
p=194977). So no single small-r defect bound is the prize floor — resonant primes violate it by ≫1×.
BUT the spike does NOT lift to the house: at the same resonant p=194977, `C=B/√(n ln m)=1.505`, only
~1.2× the generic 1.23 (the r=3 spike washes out in `B=max_b|S(b)|`). Confirms the moment-arrow no-go
from a new angle: the prize floor is governed by the OPTIMIZED `r≈ln q` / the max, NOT any fixed small
r, and the deep-moment optimization is exactly the wall. **No additive-combinatorics tool here gives a
worst-case poly bound on the leak count; the leak (cross-parity, off-diagonal, resonant) IS the wall.**
