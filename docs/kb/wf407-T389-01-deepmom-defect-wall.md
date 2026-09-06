# wf407 / T389-01-deepmom — deep-moment validity wall: it is the char-`p` ENERGY DEFECT (verdict: WALLED)

**Thread:** 389-T01 (master open input). **Date:** 2026-06-14. **Verdict: WALLED** onto the
char-`p` transfer of deep additive energy = the BGK / generalized-Paley-graph √-cancellation wall
(W4). Sharpened localization + one axiom-clean Lean brick. **No closure fabricated.**

## The question

The prize reduces (machine-checked, in-tree) to `B = max_{b≠0}‖η_b‖ ≤ C√(n·log(q/n))`,
`η_b = Σ_{x∈μ_n} e_p(bx)`. The moment method gives `B ≤ (q·E_r)^{1/2r}` for every `r` (the only
rigorous arrow, `CharSumMomentDeepWall.charSum_le_root_moment`), and `√(n·log q)` is its value at the
saddle `r ≍ log q`. The anchor is proven only at `r = 2` (additive energy). The thread asks: (1)
re-confirm the depth gap `r_opt/r_max ≈ a/2`; (2) characterize PRECISELY what fails at the crossover —
the char-`0` energy bound, or the char-`p` transfer of it; (3) can any non-moment technique supply
depth `r ≍ log q`, or is this irreducibly the Paley/BGK wall.

## What the exact numerics settled

Probes (all EXACT enumeration, no sampling):
`scripts/probes/wf407_T389-01-deepmom_{crossover,threshold,saddle,nonmoment}.py`.

### Q2 (the sharp finding) — the failure is ENTIRELY the char-`p` transfer, never the char-`0` bound

- **The char-`0` bound `E_r^{(0)}(μ_n) ≤ (2r−1)!!·n^r` is a THEOREM, never fails.** Measured
  `E_r^{(0)}/((2r−1)!!·n^r)` is `< 1` and DECREASING in `r` (n=16: 1.00, 0.94, 0.82 at r=1,2,3;
  n=8: 1.00, 0.875, 0.667, 0.442 at r=1..4). This is exactly the Bessel coefficient inequality
  `RungBesselEnergy.bessel_energy_le_gaussian` (`[x^{2r}]I₀(2x)^d ≤ [x^{2r}]e^{dx²}`). **If the
  moment method had access to the char-`0` energy at every depth, it would close the prize.**
- **The char-`p` energy `E_r^{(p)} ≥ E_r^{(0)}` is one-sided, with equality iff `p > τ_r ≍
  n^{(r+3)/2}`** i.e. iff `r ≤ r_max = 2·log_n p − 3` (threshold law, confirmed: at order `r` the
  largest defect prime `p_def` has `log_n(p_def) ≈ (r+3)/2`; n=16,r=3 → p_def=5281, log₁₆=3.09 vs
  (r+3)/2=3.0; n=8,r=4 → p_def=1201, log₈=3.41 vs 3.5). The defect `Δ_r := E_r^{(p)} − E_r^{(0)} ≥ 0`
  COUNTS the spurious `r`-subset sums of `μ_n` that vanish mod `p` but not in `ℤ[ζ_n]`.
- **Saddle behaviour** (`saddle.py`, n=16 p=16369 β=3.5 r_max=4): `Δ_r` turns on exactly at r=r_max=4
  (defect 1.2% at r=4, 0% below). The bound `(q·E_r^{(p)})^{1/2r}` tracks the clean
  `(q·E_r^{(0)})^{1/2r}` until r_max, then degrades. At r_max the value is `≍ n^{3/4}√(log_n p)`
  (n=16: 22.95 ≫ true B=12.76 ≈ √(n ln p)=12.46) — **the moment optimum is PINNED at r_max by the
  defect, not by the char-`0` bound. The best the moment method can PROVE is `B ≲ n^{3/4+o(1)}`.**

### Q1 — the depth gap is HALF THE TOWER DEPTH (confirmed)

`r_max = 2 log_n p` (reliable), `r_opt = ln q` (saddle). Ratio `= (log₂ n)/2 = a/2` in
log₂-per-tower-level units (EXACT). At prize β=5 with the `−3` correction: r_max=7 pinned, r_opt=55
at a=32, absolute ratio ≈7.9. The `a/2` claim in `CharSumMomentDeepWall` is correct.

### Q3 — irreducibly the Paley/BGK wall; the height obstruction blocks ALL algebraic routes

- **The conjecture is empirically RIGHT** (`nonmoment.py` (A)): `B/√(n ln(p/n))` is STABLE ≈1.14–1.20
  across n=16,32 and β=3,4, while `B/√n` GROWS (2.79→3.46). Only the proof is missing.
- **`B` IS the generalized-Paley eigenvalue** (Parseval verified exactly: `Σ_{b≠0}|η_b|² = pn−n²`,
  n=16 p=16369 → 261648 exact). `B ≤ 2√n ⟺ Cay(F_q,μ_n)` Ramanujan = **Paley Graph Conjecture**
  (open; best PROVEN is BGK `n^{1−o(1)}`, vacuous below `q^{1/3}`).
- **HEIGHT OBSTRUCTION (the irreducibility, exact):** a char-`0` certificate that `Δ_r = 0` is the
  claim that a sparse `±1` root-sum `α ∈ ℤ[ζ_n]` is `≠ 0 mod p`. It is FORCED only if
  `|N(α)| ≤ house(α)^{φ(n)} < p`, i.e. `φ(n)·log₂ house(α) < 256`. Per-conjugate budget `256/φ(n)`:
  a=8 → 2.0, a=16 → 2^{−7}, **a=32 → 2^{−23}**. At prize a=32 the certificate would need
  house < 1+2^{−23} ≈ 1, but any nonzero ≥2-term root-sum has house > 1. **So no char-`0` algebraic
  certificate (energy, BGM/higher-order-MDS det, esymm vanishing) can force the transfer at prize
  scale; only an ANALYTIC (character-sum / equidistribution) input can bound the defect.** This is
  the unifying no-go (extends `EffectiveTransfer.esymm_eq_zero_iff` to every algebraic certificate;
  consistent with DISPROOF_LOG 2026-06-14 "height obstruction").

## The Lean brick (axiom-clean: exactly `[propext, Classical.choice, Quot.sound]`)

`Research/ProximityPrize/Frontier/WF407_DeepMomentDefectWall.lean` — the wall is
**monotone and one-sided**, `momentBound q E r := (q·E)^{1/(2r)}`:
- `momentBound_mono_in_energy` — bigger energy ⟹ worse bound.
- `defect_only_worsens` — `E_p = E_0 + Δ`, `Δ ≥ 0` ⟹ `momentBound q E_0 r ≤ momentBound q (E_0+Δ) r`.
  **A spurious mod-`p` collision can only WORSEN the bound; never helps.** This is the wall.
- `defect_strictly_worsens` — strict when `Δ > 0` (the transfer `Δ=0`, i.e. `p > τ_r`, is the ONLY
  way to attain the clean Gaussian bound at depth `r`).
- `momentBound_beats_iff` — `momentBound q E r ≤ T ↔ q·E ≤ T^{2r}` (self-contained criterion).
- `charp_beats_imp_char0_beats` — char-`p` beats `T` ⟹ char-`0` beats `T`, not conversely unless
  `Δ=0`. Prize ⟺ `Δ_r = 0` at the saddle = the open BGK/Paley wall.

Validated `bash scripts/pg-iterate.sh …` → ✅ OK (435s), audit exactly `[propext, Classical.choice,
Quot.sound]`.

## Verdict

**WALLED.** The deep-moment validity question is NOT a deficiency of the char-`0` energy bound (a
theorem) nor a re-optimization choice. It is, exactly and monotonically, the nonnegative char-`p`
energy defect `Δ_r = E_r^{(p)} − E_r^{(0)}` at the saddle depth `r ≍ log q ≫ r_max = 2 log_n p`. Any
proof that `Δ_r = 0` (or `Δ_r` small) at the saddle is, by the height obstruction, NECESSARILY
analytic (character-sum / equidistribution), hence is the BGK / generalized-Paley √-cancellation wall
(`B ≤ 2√n ⟺` Ramanujan, Paley Graph Conjecture). No algebraic/moment/tower route can supply it.

## What remains (for the next wave)

- The **single open inequality** is now crisply: `Δ_r = 0` (equivalently `E_r^{(p)} = (2r−1)!!n^r`)
  for `r` up to the saddle `≍ log q` at `p ~ n^5`, `n = 2^32`. This is faces 3↔4 and the analytic
  heart, NOT improvable by char-0 algebra (height obstruction).
- The **cross-parity leak `A ≡ −g·B mod q`** (407-T09, 96–100% of defects) is the structured form of
  `Δ_r`; turning the leak into a bound on `Δ_r` is the unexploited lever, = Pan–Xu ideal-SVP for the
  fully-split case.
- The defect `Δ_r` should be measured directly as a function of `r` at fixed prize-diagonal primes to
  test whether it is `O(small)` just past r_max (a soft landing would reopen a quantitative route) or
  jumps to `Θ(n^{2r})` (hard wall). Saddle data (n=16: 1.2% at r=r_max) suggests soft onset — worth
  a dedicated `Δ_r`-growth probe.
