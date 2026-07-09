# [#407 route effkatz] Effective-Katz / Wasserstein CONDUCTOR verdict (gitignored scratch)

## Object
`p-1 = m*n`, `mu_n` = order-n subgroup (index m), `eta_b = sum_{x in mu_n} e_p(b x)`,
`B = max_{b!=0}|eta_b|`. Prize floor conjecture: `B <= C*sqrt(n log m)`.

## CONDUCTOR computed independently (probe-exact)
The family `b -> eta_b` is the trace function of the additive Fourier transform `FT_psi(delta_{mu_n})`
of the n-point punctual sheaf on `mu_n`. Its ell-adic invariants on `A^1_b`:
- **generic rank = n EXACTLY** (n distinct geometric frequencies `zeta_p^x`, x in mu_n);
  measured by exact distinct-ratio count + Hankel rank: rank == n in **100% of swept cases**
  (`_wf407_effkatz_rank_exact.py`: "rank != n cases: 0").
- Swan_infinity <= n, tame at 0 => `c(F) = Theta(n)`. So conductor is **O(n)**, NOT O(1), NOT O(m).

## The 2^-48 obstruction is REAL (confirmed + sharpened)
Deligne single-point bound (KU eq.(17)): discrepancy `<= cond * p^{-1/2} = n/sqrt(p)`.
To beat the per-frequency non-conspiracy threshold `1/m`:
  `n/sqrt(p) < 1/m  <=>  n*m < sqrt(p)  <=>  (p-1) < sqrt(p)`  -- FALSE for every p >= 3.
Equivalently (comment's framing): need `conductor < sqrt(n/m) = 2^-48 < 1` -- impossible (cond=n>=1).
- Prize n=2^32, m=2^128, p~2^160: `n/sqrt(p) = 2^-48`, target `1/m = 2^-128`. **SHORT by 2^80.**
- The bound is in fact pointwise VACUOUS at every p: `n/sqrt(p) = (p-1)/(m sqrt(p)) ~ sqrt(p) >> 1`.

## Escape routes all CLOSED (no slack)
- **E1 (averaging / L^{2r}):** `<|eta_b|^2> = n-1` EXACTLY (Parseval) -> average conductor still Theta(n).
  `B/RMS` grows 1.97 -> 2.38 tracking `sqrt(log m)`. The route gives the sqrt(n) RMS for free; the
  remaining `sqrt(log m) * C` is the **OPEN prize constant** (R = B/sqrt(n ln m) flat at 1.0-1.4),
  NOT a conductor win.
- **E2 (Mellin / coset block-diagonalization):** along a mu_n-coset eta_b is constant (trivial
  invariance, rank 1); the MAX reduces to the m distinct coset-values = the m Gauss periods (Paley
  eigenvalues), each an independent |tau|=sqrt(p) phase. No effective rank drop -- recovers the same
  rank-n m-fold DFT object.
- **E3 (Mellin framework, KU Thm 4.11):** STRICTLY WORSE -- KU's own sec 4.4 remark: complexity enters
  EXPONENTIALLY in that setting (`c = 2^{Theta(n)}`); the W_1 <= 1/log p there is MEAN equidistribution,
  giving no pointwise sup-norm.

## Cross-checks
- Same wall as `KowalskiUntrauBarrier.lean` (KU sec 3, Lemma 3.9): there n=|H| is in the *denominator
  of the decay exponent* `q^{-1/(n-1)}` (short by ~2^30 in log); here n is the *conductor* feeding
  `n/sqrt(p)` (short by 2^80). Two incarnations (Sec 3 vs Sec 4) of n-in-the-wrong-place.
- Burgess in-regime? At the prize instance n=2^32, p~2^160: n = p^0.200 < p^0.25 => Burgess OUT.
  (Asymptotically at fixed index m, n=Theta(p) > p^{1/4}, but the single prize instance is sub-1/4.)

## Lean deliverable (axiom-clean, verified [propext, Classical.choice, Quot.sound])
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/EffKatzConductorBarrier.lean`
- `conductor_eq`: c(F) = n (the additive-FT generic rank).
- `deligne_never_beats_threshold` (p>=3) / `_real` (n,m>=2): `(n*m)^2 < p` is FALSE -> route vacuous.
- `prize_gap_squared`: the squared target is violated by ~2^160 (= 2^80 in the bound).
- `conductor_requirement_impossible`: `conductor < sqrt(n/m)` is impossible for n,m>=1.

## Verdict: WALL. The 2^-48 obstruction is REAL; conductor = n exactly; no averaging/Mellin slack.
The effective-Katz/Wasserstein route bottoms out at the sqrt(n) RMS (Parseval) and is structurally
blind to the open prize content (the sqrt(log m) factor + the ~1.3 constant = sqrt-cancellation among
m Gauss-sum phases). Same open core as the rest of the campaign, reached from the geometric/conductor side.
